/* variable_use_analysis.h - Variable issues detector.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast.h"
#include "util/diagnostic.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include "builtins.h"
#include <assert.h>
#include <string.h>

typedef vector_t         (struct ast_node *)  ast_array_t;
typedef vector_t(vector_t(struct ast_node *)) ast_usage_stack_t;

static struct ast_storage storage;

static ast_usage_stack_t usages = {0};

static void use_start_scope()
{
    vector_emplace_back(usages);
}

static void use_end_scope()
{
    vector_erase(usages, usages.count - 1);
}

static void init()
{
    /* Initialize first stack entry for the first
       scope depth. */
    use_start_scope();
    ast_storage_init(&storage);
}

static void reset()
{
    vector_foreach(usages, i) {
        vector_free(usages.data[i]);
    }
    vector_free(usages);
    ast_storage_free(&storage);
}

static void collect_ast(struct ast_node *ast)
{
    vector_push_back(vector_back(usages), ast);
}

static bool is_assignment_op(enum token_type e)
{
    switch (e) {
    case TOK_ASSIGN:
    case TOK_MUL_ASSIGN:
    case TOK_DIV_ASSIGN:
    case TOK_MOD_ASSIGN:
    case TOK_PLUS_ASSIGN:
    case TOK_MINUS_ASSIGN:
    case TOK_SHL_ASSIGN:
    case TOK_SHR_ASSIGN:
    case TOK_BIT_AND_ASSIGN:
    case TOK_BIT_OR_ASSIGN:
    case TOK_XOR_ASSIGN:
        return true;
    default:
        return false;
    }
}

/* This used in functions
   ast_assert_declared() for symbols, function calls and array access statements,
   ast_assert_not_declared() for all declarations. */
static const char *ast_decl_or_expr_to_string(struct ast_node *ast)
{
    switch (ast->type) {
    case AST_FUNCTION_CALL:
    case AST_FUNCTION_DECL:
        return "Function";
    case AST_ARRAY_DECL:
    case AST_ARRAY_ACCESS:
        return "Array";
    case AST_VAR_DECL:
    case AST_SYMBOL:
        return "Variable";
    default:
        weak_unreachable(
            "Expected variable or function AST, got `%s`.",
            ast_type_to_string(ast->type)
        );
    }
}

static void add_use(struct ast_node *ast, bool is_write)
{
    void (*usage_add_fun)(struct ast_storage *, const char *) = is_write
        ? ast_storage_add_write_use
        : ast_storage_add_read_use;

    if (ast->type == AST_FUNCTION_CALL) {
        struct ast_function_call *stmt = ast->ast;
        usage_add_fun(&storage, stmt->name);
    }
    if (ast->type == AST_SYMBOL) {
        struct ast_symbol *sym = ast->ast;
        usage_add_fun(&storage, sym->value);
    }
    if (ast->type == AST_ARRAY_ACCESS) {
        struct ast_array_access *access = ast->ast;
        usage_add_fun(&storage, access->name);
    }
    if (ast->type == AST_MEMBER) {
        struct ast_member *member = ast->ast;
        if (member->structure->type == AST_SYMBOL) {
            struct ast_symbol *sym = member->structure->ast;
            usage_add_fun(&storage, sym->value);
        }
        /* Otherwise it can be unary statement like
           *(var).member. */
    }
}

static void use_add_read(struct ast_node *ast)
{
    add_use(ast, /*is_write=*/false);
}

static void use_add_write(struct ast_node *ast)
{
    add_use(ast, /*is_write=*/true);
}

static void uses_mark_top_scope_as_read()
{
    for (uint64_t i = 0; i < vector_back(usages).count; ++i)
        use_add_read(vector_back(usages).data[i]);
}

static bool is_builtin(const char *name)
{
    for (uint64_t i = 0; i < __weak_array_size(builtin_fns); ++i)
         if (strcmp(builtin_fns[i].name, name) == 0)
            return 1;

    return 0;
}

static void assert_is_declared(const char *name, struct ast_node *loc)
{
    if (is_builtin(name)) return;
    if (ast_storage_lookup(&storage, name)) return;
    weak_compile_error(
        loc->line_no,
        loc->col_no,
        "%s `%s` not found",
        ast_decl_or_expr_to_string(loc), name
    );
}

static void assert_is_not_declared(const char *name, struct ast_node *loc)
{
    struct ast_storage_decl *decl = ast_storage_lookup(&storage, name);

    if (!decl) return;
    weak_compile_error(
        loc->line_no,
        loc->col_no,
        "%s `%s` already declared at line %u, column %u",
        ast_decl_or_expr_to_string(loc), name,
        decl->ast->line_no,
        decl->ast->col_no
    );
}

void make_unused_var_analysis()
{
    ast_storage_decl_array_t set = {0};
    ast_storage_current_scope_uses(&storage, &set);

    for (uint64_t i = 0; i < set.count; ++i) {
        struct ast_storage_decl *use = set.data[i];
        bool is_func = use->ast->type == AST_FUNCTION_DECL;
        if (!is_func && use->read_uses == 0) {
            weak_compile_warn(
                use->ast->line_no,
                use->ast->col_no,
                "Variable `%s` %s",
                use->name,
                use->write_uses ? "written, but never read" : "is never used"
            );
        }
    }

    vector_free(set);
}

void make_unused_var_and_func_analysis()
{
    ast_storage_decl_array_t set = {0};
    ast_storage_current_scope_uses(&storage, &set);

    for (uint64_t i = 0; i < set.count; ++i) {
        struct ast_storage_decl *use = set.data[i];
        bool is_func = use->ast->type == AST_FUNCTION_DECL;
        bool is_main_func = false;
        if (is_func) {
            struct ast_function_decl *decl = use->ast->ast;
            is_main_func = !strcmp(decl->name, "main");
        }
        if (!is_main_func && use->read_uses == 0)
            weak_compile_warn(
                use->ast->line_no,
                use->ast->col_no,
                "%s `%s` %s",
                is_func ? "Function" : "Variable",
                use->name,
                use->write_uses ? "written, but never read" : "is never used"
            );
    }

    vector_free(set);
}

static void visit_node(struct ast_node *ast);

static void visit_symbol(struct ast_node *ast)
{
    struct ast_symbol *sym = ast->ast;
    assert_is_declared(sym->value, ast);

    collect_ast(ast);
    /* We will decide if there is write use of this statement
       inside binary/unary operator logic.  */
}

static void visit_var_decl(struct ast_node *ast)
{
    struct ast_var_decl *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);
    ast_storage_push(&storage, decl->name, ast);
    if (decl->body)
        visit_node(decl->body);
}

static void visit_array_decl(struct ast_node *ast)
{
    struct ast_var_decl *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);
    ast_storage_push(&storage, decl->name, ast);
}

static void visit_binary(struct ast_node *ast)
{
    struct ast_binary *stmt = ast->ast;
    visit_node(stmt->lhs);
    visit_node(stmt->rhs);

    /* Only left hand side can be writeable. */
    if (is_assignment_op(stmt->operation))
        use_add_write(stmt->lhs);
    else
        use_add_read(stmt->lhs);
    use_add_read(stmt->rhs);
}

static void visit_unary(struct ast_node *ast)
{
    struct ast_unary *stmt = ast->ast;
    struct ast_node *op = stmt->operand;
    bool is_var = false;
    is_var |= op->type == AST_SYMBOL; /* *var */
    is_var |= op->type == AST_ARRAY_ACCESS; /* *var[0] */
    is_var |= op->type == AST_MEMBER; /* *var.field */
    is_var |= op->type == AST_PREFIX_UNARY; /* *(*var) */
    if (!is_var)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Variable as argument of unary operator expected"
        );

    switch (stmt->operation) {
    case TOK_INC: /* ++var */
    case TOK_DEC: /* --var */
        use_add_write(op);
        break;
    case TOK_STAR: /* *var */
    case TOK_BIT_AND: /* &var */
        use_add_read(op);
        break;
    default:
        weak_unreachable("Unknown unary operator `%s`.", tok_to_string(stmt->operation));
    }
    visit_node(op);
}

/* \todo: What if (*mem_ptr)[0][1][2]? */
static void visit_array_access(struct ast_node *ast)
{
    struct ast_array_access *stmt = ast->ast;
    collect_ast(ast);
    assert(stmt->indices->type == AST_COMPOUND_STMT);
    visit_node(stmt->indices->ast);
}

static void visit_member(struct ast_node *ast)
{
    collect_ast(ast);
}

static void visit_if(struct ast_node *ast)
{
    struct ast_if *stmt = ast->ast;
    visit_node(stmt->condition);
    visit_node(stmt->body);
    if (stmt->else_body)
        visit_node(stmt->else_body);
}

static void visit_for(struct ast_node *ast)
{
    struct ast_for *stmt = ast->ast;
    ast_storage_start_scope(&storage);
    if (stmt->init)
        visit_node(stmt->init);
    if (stmt->condition) {
        use_start_scope();
        visit_node(stmt->condition);
        uses_mark_top_scope_as_read();
        use_end_scope();
    }
    if (stmt->increment)
        visit_node(stmt->increment);
    visit_node(stmt->body);
    ast_storage_end_scope(&storage);
}

static void visit_while(struct ast_node *ast)
{
    struct ast_while *stmt = ast->ast;
    use_start_scope();
    visit_node(stmt->condition);
    uses_mark_top_scope_as_read();
    use_end_scope();
    visit_node(stmt->body);
}

static void visit_do_while(struct ast_node *ast)
{
    struct ast_do_while *stmt = ast->ast;
    use_start_scope();
    visit_node(stmt->condition);
    uses_mark_top_scope_as_read();
    use_end_scope();
    visit_node(stmt->body);
}

static void visit_return(struct ast_node *ast)
{
    struct ast_return *stmt = ast->ast;
    if (stmt->operand) {
        visit_node(stmt->operand);
        use_add_read(stmt->operand);
    }
}

static void visit_compound(struct ast_node *ast)
{
    struct ast_compound *stmt = ast->ast;
    ast_storage_start_scope(&storage);
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_node(stmt->stmts[i]);
    make_unused_var_and_func_analysis();
    ast_storage_end_scope(&storage);
}

static void visit_function_decl(struct ast_node *ast)
{
    struct ast_function_decl *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);

    ast_storage_start_scope(&storage);
    /* This is to have function in recursive calls. */
    ast_storage_push(&storage, decl->name, ast);
    /* Don't just visit compound AST, which creates and terminates scope. */
    struct ast_compound *args = decl->args->ast;
    for (uint64_t i = 0; i < args->size; ++i)
        visit_node(args->stmts[i]);
    visit_node(decl->body);
    make_unused_var_analysis();
    ast_storage_end_scope(&storage);
    /* This is to have function outside. */
    ast_storage_push(&storage, decl->name, ast);
}

static void visit_function_call(struct ast_node *ast)
{
    struct ast_function_call *stmt = ast->ast;

    if (is_builtin(stmt->name)) return;

    assert_is_declared(stmt->name, ast);
    use_add_read(ast);

    assert(stmt->args->type == AST_COMPOUND_STMT);
    struct ast_compound *args = stmt->args->ast;
    for (uint64_t i = 0; i < args->size; ++i) {
        visit_node(args->stmts[i]);
        use_add_read(args->stmts[i]);
    }
}

void visit_node(struct ast_node *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL: /* Unused. */
    case AST_INTEGER_LITERAL: /* Unused. */
    case AST_FLOATING_POINT_LITERAL: /* Unused. */
    case AST_STRING_LITERAL: /* Unused. */
    case AST_BOOLEAN_LITERAL: /* Unused. */
    case AST_STRUCT_DECL: /* Unused. */
    case AST_BREAK_STMT: /* Unused. */
    case AST_CONTINUE_STMT: /* Unused. */
        break;
    case AST_SYMBOL:
        visit_symbol(ast);
        break;
    case AST_VAR_DECL:
        visit_var_decl(ast);
        break;
    case AST_ARRAY_DECL:
        visit_array_decl(ast);
        break;
    case AST_BINARY:
        visit_binary(ast);
        break;
    case AST_PREFIX_UNARY:
        visit_unary(ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_unary(ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_array_access(ast);
        break;
    case AST_MEMBER:
        visit_member(ast);
        break;
    case AST_IF_STMT:
        visit_if(ast);
        break;
    case AST_FOR_STMT:
        visit_for(ast);
        break;
    case AST_WHILE_STMT:
        visit_while(ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_do_while(ast);
        break;
    case AST_RETURN_STMT:
        visit_return(ast);
        break;
    case AST_COMPOUND_STMT:
        visit_compound(ast);
        break;
    case AST_FUNCTION_DECL:
        visit_function_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_function_call(ast);
        break;
    default:
        weak_unreachable("Unknown AST type (numeric: %d).", ast->type);
    }
}

void analysis_variable_use_analysis(struct ast_node *root)
{
    init();
    visit_node(root);
    reset();
}
