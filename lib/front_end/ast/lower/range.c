/* range.c - Range to regular for statement conversion.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "util/alloc.h"
#include "util/hashmap.h"
#include "util/crc32.h"
#include "util/unreachable.h"
#include <assert.h>
#include <string.h>


#define DECL_NAME_MAX_LEN 256

/* \note: Functions cannot return array.
          Function takes array as parameter via pointer.
          Array can be declared as variable. */
struct array_decl_info {
    struct ast_node     *ast;
    char                 name[DECL_NAME_MAX_LEN];
    enum data_type       dt;
    /* If the array is
      
           int mem[1][2][3],
       `3` is stored. Used as is because
       we can iterate only by last
       level of array. To iterate over
       next ones, we should push new record
       to the storage with lower enclosure. */
    int32_t              top_enclosure_size;
    uint64_t             depth;
};

static uint64_t  scope_depth;
static hashmap_t storage;

static void storage_init()
{
    scope_depth = 0;
    hashmap_init(&storage, 100);
}

static void storage_reset()
{
    scope_depth = 0;
    hashmap_foreach(&storage, key, val) {
        (void) key;
        struct array_decl_info *decl = (struct array_decl_info *) val;
        weak_free(decl);
    }
    hashmap_destroy(&storage);
}

static void storage_start_scope()
{
    ++scope_depth;
}

static void storage_end_scope()
{
    hashmap_foreach(&storage, key, val) {
        struct array_decl_info *decl = (struct array_decl_info *) val;
        if (decl->depth == scope_depth)
            hashmap_remove(&storage, key);
    }
    --scope_depth;
}

static void storage_put(
    struct ast_node *ast,
    const char      *name,
    enum data_type   dt,
    int32_t          top_enclosure_size
) {
    struct array_decl_info *decl = weak_calloc(1, sizeof (struct array_decl_info));

    strncpy(decl->name, name, DECL_NAME_MAX_LEN - 1);
    decl->ast = ast;
    decl->dt = dt;
    decl->top_enclosure_size = top_enclosure_size;
    hashmap_put(&storage, crc32_string(name), (uint64_t) decl);
}

static struct array_decl_info *storage_lookup(const char *name)
{
    uint64_t hash = crc32_string(name);
    bool     ok   = 0;
    int64_t  addr = hashmap_get(&storage, hash, &ok);

    if (!ok || addr == 0)
        weak_unreachable("Could not find variable `%s`.", name);

    struct array_decl_info *decl = (struct array_decl_info *) addr;

    if (decl->depth > scope_depth)
        weak_unreachable("Impossible case: variable depth > current depth");

    return decl;
}

static void storage_put_array_decl(struct ast_node *ast)
{
    struct ast_array_decl *decl = ast->ast;
    struct ast_compound   *list = decl->enclosure_list->ast;

    storage_put(
        ast,
        decl->name,
        decl->dt,
        ((struct ast_num *) list->stmts[list->size - 1]->ast)
            ->value
    );
}

static void visit_node(struct ast_node **ast);

static void visit_ast_array_decl(struct ast_node *ast)
{
    storage_put_array_decl(ast);
}

static void visit_ast_compound(struct ast_node *ast)
{
    struct ast_compound *compound = ast->ast;

    for (uint64_t i = 0; i < compound->size; ++i)
        visit_node(&compound->stmts[i]);
}

static void visit_ast_function_decl(struct ast_node *ast)
{
    struct ast_function_decl *decl = ast->ast;

    storage_start_scope();

    struct ast_compound *args = decl->args->ast;
    if (args && args->size > 0)
        visit_node(&decl->args);

    storage_end_scope();

    visit_node(&decl->body);
}



/* Check if iterated array declaration "drops"
   last enclosure level. For example:
  
      int array[1][2][3];
  
      for (int it[1][2] : array) {} // Correct.
      for (int it[1] : array) {}    // Incorrect.
      for (int it[2][2] : array) {} // Incorrect. */
static bool verify_iterated_array(
    struct ast_array_decl *iterated,
    struct ast_array_decl *target
) {
    struct ast_compound *iterated_list = iterated->enclosure_list->ast;
    struct ast_compound   *target_list =   target->enclosure_list->ast;

    if (iterated_list->size != target_list->size - 1)
        return 0;

    for (uint64_t i = 0; i < iterated_list->size; ++i) {
        assert(iterated_list->stmts[i]->type == AST_INTEGER_LITERAL);
        assert(  target_list->stmts[i]->type == AST_INTEGER_LITERAL);

        struct ast_num *iterated_idx = iterated_list->stmts[i]->ast;
        struct ast_num   *target_idx =   target_list->stmts[i]->ast;

        int32_t it_v = iterated_idx->value;
        int32_t ta_v =   target_idx->value;

        if (it_v != ta_v)
            return 0;
    }

    return 1;
}

/* 1. Determine size of array
   2. Make usual for header
   3. Make iterator being pointer
   4. Copy `for` body after iterator declaration
  
       int main() {
         int array[5];
         int num = 0;
         for (int *i : array) {
           *i = ++num;
         }
         // ... //
         for (int __i = 0; __i < / * size of * / array; ++__i) {
           int *i = &array[__i];
           *i = ++num;
         }
       }
   ...
   Or
   ...
       int main() {
         for (int *i : f()) {
           *i = 0;
         }
         // ... //
         / * ??? * / *__range_target_1 = f();
         for (int __i = 0; __i < / * size of * / __range_target_1; ++__i) {
           int *i = &__range_target_1[__i];
         }
       }
   ...
   Or
   ...
       int main() {
         int arr[1][2][3] = { ... };
         for (int *ptr[1][2] : arr) {
           for (int *i[1] : *ptr) {
             for (int *j : *i) {
               ++(*j);
             }
           }
         }
         // ... //
         for (int __i1 = 0; __i1 < / * size of * / arr; ++__i1) {
           int *ptr[1][2] = &arr[__i1];
           for (int __i2 = 0; __i2 < / * size of * / *ptr; ++__i2) {
             int *i[1] = &ptr[__i2];
             for (int __i3 = 0; __i3 < / * size of * / *i; ++__i3) {
               int *j = &i[__i3];
               ++(*j); / * Action on j. * /
             }
           }
         }
       } */

__weak_really_inline static void assertion(
    struct ast_for_range *range,
    struct array_decl_info *decl
) {
    struct ast_node *iter   = range->iter;
    struct ast_node *target = range->range_target;

    (void) iter;
    (void) target;

    assert((
         iter->type == AST_ARRAY_DECL
      || iter->type == AST_VAR_DECL
    ) && (
        "Expected variable or array declaration."
    ));
    assert((
        target->type == AST_SYMBOL
    ) && (
        "Expected symbol as array."
    ));

    if (iter->type == AST_ARRAY_DECL)
        if (!verify_iterated_array(iter->ast, decl->ast->ast))
            weak_unreachable(
                "Iterated array declaration does not "
                "match the target declaration."
            );
}

__weak_really_inline static struct ast_node **make_index(const char *name)
{
    struct ast_node *idx = ast_symbol_init(strdup(name), 0, 0);
    struct ast_node **idxs = weak_calloc(1, sizeof (struct ast_node *));
    idxs[0] = idx;

    return idxs;
}

__weak_really_inline static struct ast_node *make_iter_index(
    const char *__i,
    uint16_t    line_no,
    uint16_t    col_no
) {
    return ast_var_decl_init(
        D_T_INT,
        strdup(__i),
        /*type_name*/NULL,
        /*indirection_lvl*/0,
        ast_num_init(0, line_no, col_no),
        line_no, col_no
    );
}

__weak_really_inline static void make_iter_ptr_body(
    struct array_decl_info *decl,
    struct ast_node        *iter_ptr,
    const char             *__i
) {
    bool array = iter_ptr->type == AST_ARRAY_DECL;

    struct ast_node *iter_body = ast_unary_init(
        AST_PREFIX_UNARY,
        TOK_BIT_AND,
        ast_array_access_init(
            strdup(decl->name),
            ast_compound_init(
                1,
                make_index(__i),
                0, 0
            ),
            0, 0
        ),
        0, 0
    );

    /* TODO: Compiler can derive all type information manually.
             Then verify_iterated_array() can be thrown out.
             Will `auto` keyword as in C++ make sence? */
    if (array) {
        struct ast_array_decl *arr = iter_ptr->ast;
        arr->body = iter_body;
    } else {
        struct ast_var_decl *var = iter_ptr->ast;
        var->body = iter_body;
    }
}

__weak_really_inline static struct ast_node *enlarge_body(struct ast_compound *body)
{
    struct ast_node **new_stmts = weak_calloc(body->size + 1, sizeof (struct ast_node *));

    /* Copy all statements from old body to the new
       and left space for first assignment. */
    for (uint64_t i = 1; i < body->size + 1; ++i)
        new_stmts[i] = body->stmts[i - 1];

    return ast_compound_init(
        body->size + 1,
        new_stmts,
        0, 0
    );
}

static void visit_ast_for_range(struct ast_node **ast)
{
    struct ast_for_range   *range      = (*ast)->ast;
    struct ast_node        *iter       = range->iter;
    struct ast_node        *target     = range->range_target;
    struct ast_compound    *body       = range->body->ast;
    struct ast_symbol      *target_sym = target->ast;
    struct array_decl_info *decl       = storage_lookup(target_sym->value);
    bool                    is_array   = iter->type == AST_ARRAY_DECL;

    assertion(range, decl);

    static int32_t i = 0;
    char __i[256] = {0};
    snprintf(__i, sizeof (__i), "__i%d", ++i);

    struct ast_node *iterator = make_iter_index(__i, iter->line_no, iter->col_no);

    if (is_array)
        storage_put_array_decl(iter);

    visit_node(&range->body);

    struct ast_node     *enlarged_body     = enlarge_body(body);
    struct ast_compound *enlarged_compound = enlarged_body->ast;

    enlarged_compound->stmts[0] = iter;

    make_iter_ptr_body(decl, iter, __i);

    weak_free(body->stmts);
    ast_node_cleanup(target);
    weak_free((*ast)->ast);
    weak_free((*ast));

    *ast = ast_for_init(
        iterator,
        ast_binary_init(
            TOK_LT,
            ast_symbol_init(strdup(__i), 0, 0),
            ast_num_init(decl->top_enclosure_size, 0, 0),
            0, 0
        ),
        ast_unary_init(
            AST_PREFIX_UNARY,
            TOK_INC,
            ast_symbol_init(strdup(__i), 0, 0),
            0, 0
        ),
        enlarged_body,
        0, 0
    );
}

static void visit_node(struct ast_node **ast)
{
    assert(ast);

    switch ((*ast)->type) {
    /* Only for full tree traversal. */
    case AST_COMPOUND_STMT:
        visit_ast_compound(*ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(*ast);
        break;
    /* Stuff. */
    case AST_ARRAY_DECL:
        visit_ast_array_decl(*ast);
        break;
    case AST_FOR_RANGE_STMT:
        visit_ast_for_range(ast);
        break;
    /* Ignore. */
    default:
        break;
    }
}

void ast_lower(struct ast_node **ast)
{
    storage_init();
    visit_node(ast);
    storage_reset();
}