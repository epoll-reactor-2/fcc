/* gen.c - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/gen.h"
#include "front_end/ast/ast.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/storage.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include <assert.h>
#include <string.h>

/* Total list of functions. */
static ir_vector_t        ir_fn_decls;
static struct ir_node    *ir_first;
static struct ir_node    *ir_last;
static struct ir_node    *ir_prev;
/* Our IR is designed to store a lot of implicit information
   and our language is not simply stack-based, when we can
   pop last two generated instructions and always know their
   type.
   So there is a type of last created instruction (if any),
   and mapping between symbol index and type. */
static enum data_type     ir_last_type;
static struct type        ir_type_map[65536];
/* Used to count alloca instructions.
   Conditions:
   - reset_state at the start of each function declaration,
   - increments with every created alloca instruction. */
static uint64_t           ir_var_idx;
static bool               ir_save_first;
static bool               ir_meta_is_loop;
/* Depth of source-level blocks ({ ... }). */
static uint64_t           ir_block_depth;
/* Loop index in function boundaries. If loop is nested,
   index is incremented sequentially. */
static uint64_t           ir_loop_idx;
static uint64_t           ir_meta_loop_idx;
/* This used to judge if we should put function call to IR list
   or use it as instruction operand. */
static bool               ir_is_global_scope;
static hashmap_t          ir_fn_return_types;
/* This is stacks for `break` and `continue` instructions.
   On the top of stack sits most recent loop (loop with maximum
   current depth). This complication used to store correct states
   for all nested loops where we are located now.
  
   When
     - break   , jumps to the first statement after current loop.
     - continue, jumps to the loop header (for, while, do-while conditions).
  
   Note, that there is no stack for continue statements. Indices for them
   computed immediately from `ir_loop_header_stack`. */
static ir_vector_t        ir_break_stack;
static vector_t(uint64_t) ir_loop_header_stack;

static void ir_fn_add_return_type(const char *name, enum data_type dt)
{
    hashmap_put(&ir_fn_return_types, crc32_string(name), (uint64_t) dt);
}

static enum data_type ir_fn_return_type(const char *name)
{
    bool ok = 0;
    uint64_t name_hash = crc32_string(name);
    uint64_t got = hashmap_get(&ir_fn_return_types, name_hash, &ok);
    if (!ok)
        weak_unreachable("Cannot get return type for function `%s`", name);

    return (enum data_type) got;
}

static void ir_try_add_meta(struct ir_node *ir)
{
    ir->meta.kind = IR_META_SYM;
    ir->meta.block_depth = ir_block_depth;
    ir->meta.global_loop_idx = ir_loop_idx;

    if (ir_meta_is_loop) {
        ir->meta.sym.loop = 1;
        ir->meta.sym.loop_idx = ir_meta_loop_idx++;
    }
}

/* Note: This function does not set previous pointers
         in IR list. Back edges always represents control flow
         and set up in `ir_link()`. */
static void ir_insert(struct ir_node *new_node)
{
    __weak_debug({
        __weak_debug_msg("Insert IR (instr_idx: %lu) :", new_node->instr_idx);
        ir_dump_node(stdout, new_node);
        puts("");
    });

    ir_try_add_meta(new_node);

    if (ir_save_first) {
        ir_first = new_node;
        ir_save_first = 0;
    }
    ir_last = new_node;

    if (ir_prev == NULL) {
        ir_prev = new_node;
        return;
    }

    ir_prev->next = new_node;
    new_node->prev = ir_prev;
    ir_prev = new_node;
}

really_inline static void ir_insert_last()
{
    ir_insert(ir_last);
}

static void reset_fn_state()
{
    ir_storage_init();

    memset(ir_type_map, 0, sizeof (ir_type_map));
    ir_last_type = D_T_UNKNOWN;
    ir_var_idx = 0;
    ir_loop_idx = 0;
    ir_block_depth = 0;
    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;
    ir_save_first = 1;
    vector_free(ir_break_stack);
    vector_free(ir_loop_header_stack);
}

static void reset_state()
{
    reset_fn_state();

    vector_free(ir_fn_decls);
    if (ir_fn_return_types.buckets)
        hashmap_destroy(&ir_fn_return_types);

    hashmap_init(&ir_fn_return_types, 32);
}

static void visit(struct ast_node *ast);

/* Primitives. They are not pushed to ir_stmts, because
   they are immediate values. */
static void visit_bool(struct ast_bool *ast)
{
    ir_last = ir_imm_bool_init(ast->value);
    ir_last_type = D_T_BOOL;
}

static void visit_char(struct ast_char *ast)
{
    ir_last = ir_imm_char_init(ast->value);
    ir_last_type = D_T_CHAR;
}

static void visit_float(struct ast_float *ast)
{
    ir_last = ir_imm_float_init(ast->value);
    ir_last_type = D_T_FLOAT;
}

static void visit_num(struct ast_num *ast)
{
    ir_last = ir_imm_int_init(ast->value);
    ir_last_type = D_T_INT;
}

static void visit_string(struct ast_string *ast)
{
    /* ast->value is allocated in AST also. We duplicate to do not
       be dependent on AST cleanup. */
    ir_last = ir_string_init(ast->len, strdup(ast->value));
    ir_last_type = D_T_STRING;
}

static void emit_assign(struct ast_binary *ast)
{
    visit(ast->lhs);
    struct ir_node *lhs = ir_last;
    visit(ast->rhs);
    struct ir_node *rhs = ir_last;

    ir_last = ir_store_init(lhs, rhs);
    ir_insert_last();
}

static bool logical(enum token_type t)
{
    switch (t) {
    case TOK_EQ:
    case TOK_NEQ:
    case TOK_LE:
    case TOK_GE:
    case TOK_LT:
    case TOK_GT:
        return 1;
    default:
        return 0;
    }
}

static void emit_bin(struct ast_binary *ast)
{
    ir_last = ir_alloca_init(D_T_UNKNOWN, /*ptr_depth=*/0, ir_var_idx++);
    struct ir_alloca *alloca = ir_last->ir;
    uint64_t alloca_idx = alloca->idx;

    ir_insert_last();

    visit(ast->lhs);
    struct ir_node *lhs = ir_last;
    visit(ast->rhs);
    struct ir_node *rhs = ir_last;

    if (logical(ast->op)) {
        alloca->dt = D_T_INT; /* Or bool. */
        ir_last_type = D_T_INT;
    } else
        alloca->dt = ir_last_type;

    ir_last = ir_store_sym_init(
        alloca_idx,
        ir_bin_init(ast->op, lhs, rhs)
    );
    ir_insert_last();
    ir_last = ir_sym_init(alloca_idx);
}

static void visit_binary(struct ast_binary *ast)
{
    /* Symbol. */
    if (ast->op == TOK_ASSIGN)
        emit_assign(ast);
    else
        emit_bin(ast);
}

static void visit_break(struct ast_break *ast)
{
    (void) ast;
    struct ir_node *ir = ir_jump_init(0);
    vector_push_back(ir_break_stack, ir);
    ir_insert(ir);
}

static void visit_continue(struct ast_continue *ast)
{
    (void) ast;
    struct ir_node *ir = ir_jump_init(vector_back(ir_loop_header_stack));
    ir_insert(ir);
}

/* To emit correct `break`, we just attach it to the next
   statement after the loop.
  
   To emit correct `continue` we taking last (deepest right now)
   loop header index from stack and then remove it from stack.
  
   while () {
     continue;         | Level 0
     while () {
       continue;       | Level 1
     }
   } */
static void emit_loop_flow_instrs()
{
    if (ir_break_stack.count > 0) {
        struct ir_node *back = vector_back(ir_break_stack);
        struct ir_jump *jmp = back->ir;
        jmp->idx = ir_last->instr_idx + 1;
        /* Target will be added during linkage based on index. */
        jmp->target = NULL;

        vector_pop_back(ir_break_stack);
    }

    vector_pop_back(ir_loop_header_stack);
}

static struct ir_node *zero_cond_immediate()
{
    switch (ir_last_type) {
    case D_T_INT:   return ir_imm_int_init(0);
    case D_T_FLOAT: return ir_imm_float_init(0.0);
    case D_T_CHAR:  return ir_imm_char_init(0);
    case D_T_BOOL:  return ir_imm_bool_init(0);
    default:
        weak_unreachable("Unknown data type (numeric: %d)", ir_last_type);
    }
}

static void visit_for(struct ast_for *ast)
{
    /* Schema:
      
       L0:  init variable
       L1:  if condition is true jump to L3
       L2:  jump to L7 (exit label)
       L3:  body instr 1
       L4:  body instr 2
       L5:  increment
       L6:  jump to L1 (condition)
       L7:  after for instr
       
       Initial part is optional. */

    ir_meta_is_loop = 1;
    if (ast->init) visit(ast->init);
    ir_meta_is_loop = 0;

    /* Body starts with condition that is checked on each
      iteration. */
    uint64_t         next_iter_jump_idx = 0;
    uint64_t         header_idx         = ir_last->instr_idx + 1;
    struct ir_node *cond                = NULL;
    struct ir_node *exit_jmp            = NULL;
    struct ir_jump *exit_jmp_ptr        = NULL;
    struct ir_node *body_start          = NULL;

    vector_push_back(ir_loop_header_stack, header_idx);

    if (ir_block_depth == 0)
        ++ir_loop_idx;

    ++ir_block_depth;
    /* Condition is optional. */
    if (ast->condition) {
        next_iter_jump_idx       = ir_last->instr_idx + 1;
        visit(ast->condition);
        struct ir_node *cond_bin = ir_bin_init(TOK_NEQ, ir_last, zero_cond_immediate());
        cond                     = ir_cond_init(cond_bin, /* Not used for now. */-1);
        exit_jmp                 = ir_jump_init(/* Not used for now. */-1);
        exit_jmp_ptr             = exit_jmp->ir;
        struct ir_cond *cond_ptr = cond->ir;

        ir_insert(cond);
        ir_insert(exit_jmp);

        cond_ptr->goto_label = ir_last->instr_idx + 1;
    } else {
        next_iter_jump_idx = ir_last->instr_idx + 1;
    }

    body_start = ir_last;
    visit(ast->body);
    if (body_start != ir_last)
        body_start = body_start->next;
    else
        body_start = NULL;

    /* Increment is optional. */
    ir_meta_is_loop = 1;
    if (ast->increment) visit(ast->increment);
    ir_meta_is_loop = 0;

    ir_last = ir_jump_init(next_iter_jump_idx);

    if (ast->condition)
        exit_jmp_ptr->idx = ir_last->instr_idx + 1;

    ir_insert_last();
    --ir_block_depth;

    emit_loop_flow_instrs();
}

static void visit_while(struct ast_while *ast)
{
    /* Schema:
      
       L0: if condition is true jump to L2
       L1: jump to L5 (exit label)
       L2: body instr 1
       L3: body instr 2
       L4: jump to L0 (condition)
       L5: after while instr */

    uint64_t next_iter_idx = ir_last ? ir_last->instr_idx + 1 : 0;
    uint64_t header_idx    = ir_last ? ir_last->instr_idx + 1 : 0;

    vector_push_back(ir_loop_header_stack, header_idx);

    if (ir_block_depth == 0)
        ++ir_loop_idx;

    ++ir_block_depth;
    ir_meta_is_loop = 1;
    visit(ast->cond);
    ir_meta_is_loop = 0;

    struct ir_node *cond_bin      = ir_bin_init(TOK_NEQ, ir_last, zero_cond_immediate());
    struct ir_node *cond          = ir_cond_init(cond_bin, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr      = cond->ir;
    struct ir_node *exit_jmp      = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *exit_jmp_ptr  = exit_jmp->ir;

    ir_insert(cond);
    ir_insert(exit_jmp);

    cond_ptr->goto_label = exit_jmp->instr_idx + 1;

    visit(ast->body);

    struct ir_node *next_iter_jmp = ir_jump_init(next_iter_idx);
    ir_insert(next_iter_jmp);
    --ir_block_depth;

    exit_jmp_ptr->idx = next_iter_jmp->instr_idx + 1;

    emit_loop_flow_instrs();
}

static void visit_do_while(struct ast_do_while *ast)
{
    /* Schema:
      
       L0: body instr 1
       L1: body instr 2
       L2: allocate temporary for condition
       L3: store condition in temporary
       L4: if condition is true jump to L0 */

    uint64_t stmt_begin;
    uint64_t header_idx
        = ir_last
        ? ir_last->instr_idx + 1
        : 0;

    vector_push_back(ir_loop_header_stack, header_idx);

    if (ir_last == NULL)
        stmt_begin = 0;
    else
        stmt_begin = ir_last->instr_idx + 1;

    if (ir_block_depth == 0)
        ++ir_loop_idx;

    ++ir_block_depth;
    visit(ast->body);

    ir_meta_is_loop = 1;
    visit(ast->condition);
    ir_meta_is_loop = 0;

    struct ir_node *cond = ir_cond_init(
        ir_bin_init(
            TOK_NEQ,
            ir_last,
            zero_cond_immediate()
        ),
        stmt_begin
    );

    ir_insert(cond);
    --ir_block_depth;

    emit_loop_flow_instrs();
}

static void visit_if(struct ast_if *ast)
{
    /* Schema:
      
            if condition is true jump to L1
       L0:  jump to L3 (exit label)
       L1:  body instr 1 (first if stmt)
       L2:  body instr 2
       L3:  after if
      
       or
            if condition is true jump to L1
       L0:  jump to L4 (else label)
       L1:  body instr 1 (first if stmt)
       L2:  body instr 2
       L3:  jump to L6
       L4:  else body instr 1
       L5:  else body instr 2
       L6:  after if */

    ++ir_block_depth;
    visit(ast->condition);
    assert((
        ir_last->type == IR_IMM ||
        ir_last->type == IR_SYM
    ) && ("Immediate value or symbol required."));

    /* Condition always looks like comparison with 0.
      
       Possible cases:
                          v Binary operation result.
       - if (1 + 1) -> if sym neq $0 goto ...
       - if (1    ) -> if imm neq $0 goto ...
       - if (var  ) -> if sym neq $0 goto ... */

    ir_last = ir_bin_init(TOK_NEQ, ir_last, zero_cond_immediate());

    struct ir_node *cond         = ir_cond_init(ir_last, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr     = cond->ir;
    struct ir_node *exit_jmp     = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *exit_jmp_ptr = exit_jmp->ir;

    /* Body starts after exit jump. */
    cond_ptr->goto_label = exit_jmp->instr_idx + 1;
    ir_insert(cond);
    ir_insert(exit_jmp);

    struct ir_node *initial_stmt = ir_last;

    visit(ast->body);
    --ir_block_depth;

    initial_stmt = initial_stmt->next;

    /* Even with code like
       void f() { if (x) { f(); } }
       this will make us to jump to the `ret`
       instruction, which terminates each (regardless
       on the return type) function. */
    exit_jmp_ptr->idx = ir_last->instr_idx + 1;

    if (!ast->else_body) return;
    ++ir_block_depth;
    struct ir_node *else_jmp = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *else_jmp_ptr = else_jmp->ir;
    /* Index of this jump will be changed through pointer. */
    ir_insert(else_jmp);

    initial_stmt = ir_last;

    /* Jump over the `then` statement to `else`. */
    exit_jmp_ptr->idx = ir_last->instr_idx + 1; /* +1 jump statement. */
    visit(ast->else_body);
    /* `then` part ends with jump over `else` part. */
    else_jmp_ptr->idx = ir_last->instr_idx + 1;

    initial_stmt = initial_stmt->next;

    --ir_block_depth;
}

static void visit_ret(struct ast_ret *ast)
{
    memset(&ir_last, 0, sizeof (ir_last));
    if (ast->op) {
        visit(ast->op);
    }
    ir_last = ir_ret_init(ir_last);
    ir_insert_last();
}

static void visit_sym(struct ast_sym *ast)
{
    uint64_t idx = ir_storage_get(ast->value)->sym_idx;
    ir_last = ir_sym_init(idx);
    ir_last_type = ir_type_map[idx].dt;
}

really_inline static void visit_unary_arith(enum token_type op)
{
    struct ir_sym *sym = ir_last->ir;

    ir_last = ir_bin_init(
        op == TOK_INC
            ? TOK_PLUS
            : TOK_MINUS, ir_last, ir_imm_int_init(1)
    );
    ir_last = ir_store_sym_init(sym->idx, ir_last);
    ir_insert_last();
}

really_inline static void visit_unary_pointer(enum token_type op, bool immediate)
{
    assert(
        ir_last->type == IR_SYM &&
        "Address can be taken only of variable."
    );
    struct ir_node *sym_node = ir_last;
    struct ir_sym  *sym      = ir_last->ir;

    /* If we reached "leaf" of unary statement, we are not
       forced to allocate new variable. */
    if (immediate) {
        ir_last = ir_sym_init(sym->idx);
    } else {
        uint64_t next_idx = ir_var_idx++;
        ir_last = ir_alloca_init(
            ir_type_map[sym->idx].dt,
            ir_type_map[sym->idx].ptr_depth > 0,
            next_idx
        );
        ir_insert_last();
        ir_last = ir_store_sym_init(next_idx, sym_node);
        ir_insert_last();
        ir_last = ir_sym_init(next_idx);
    }

    struct ir_sym *new_s = ir_last->ir;

    ir_type_map[new_s->idx] = ir_type_map[sym->idx];

    new_s->deref   = op == TOK_STAR;
    new_s->addr_of = op == TOK_BIT_AND;
}

static void visit_unary(struct ast_unary *ast)
{
    visit(ast->operand);
    assert((
        ir_last->type == IR_SYM
    ) && (
        "Unary operator expects variable argument."
    ));

    enum token_type op = ast->op;

    switch (op) {
    /* Arithmetic operations. */
    case TOK_INC:
    case TOK_DEC:
        visit_unary_arith(op);
        break;
    /* Pointer operations. */
    case TOK_STAR:    /* * */
    case TOK_BIT_AND: /* & */
        visit_unary_pointer(op, ast->operand->type == AST_SYMBOL);
        break;
    default:
        weak_unreachable("Unknown operator `%s`", tok_to_string(op));
    }
}

static void visit_struct_decl(struct ast_struct_decl *ast) { (void) ast; }

static void emit_var(struct ast_var_decl *ast)
{
    uint64_t next_idx = ir_var_idx++;
    ir_last = ir_alloca_init(ast->dt, ast->ptr_depth, next_idx);
    ir_type_map[next_idx].dt = ast->dt;
    ir_type_map[next_idx].ptr_depth = ast->ptr_depth;

    /* Used as function argument or as function body statement. */
    ir_insert_last();
    ir_storage_push(ast->name, next_idx, ast->dt, ast->ptr_depth, ir_last);

    if (ast->body) {
        visit(ast->body);
        ir_last = ir_store_sym_init(next_idx, ir_last);
        ir_insert_last();
    }
}

static void emit_var_string(struct ast_var_decl *ast)
{
    struct ast_string *string   = ast->body->ast;
    uint64_t           next_idx = ir_var_idx++;
    uint64_t           mem_siz  = string->len + 1; /* We add '\0'. */

    ir_last = ir_alloca_array_init(D_T_CHAR, &mem_siz, 1, next_idx);
    ir_insert_last();
    ir_storage_push(ast->name, next_idx, ast->dt, ast->ptr_depth, ir_last);

    visit(ast->body);
    ir_last = ir_store_init(ir_sym_init(next_idx), ir_last);
    ir_insert_last();
}

static void visit_var_decl(struct ast_var_decl *ast)
{
    bool string = 1;
    string &= ast->ptr_depth == 1;
    string &= ast->dt == D_T_CHAR;
    string &= ast->body && ast->body->type == AST_STRING_LITERAL;

    if (string)
        emit_var_string(ast);
    else
        emit_var(ast);
}

/* Example. Decide, how to store indices list.

   int mem[1][2][3];
   mem[0][0][1] = 6;
   mem[0][1][2] = 9;

   alloca [1 * 2 * 3] %0
   %1 = load %0 [0 * 1 + 0 * 2 + 1]
       /// Stride = 1
       ///
       /// [ ][ ][ ][ ][ ][ ]
       ///     ^
       ///     Store there
   store %1 6
   %2 = load %0 [0 * 1 + 1 * 2 + 2]
       /// Stride = 4
       ///
       /// [ ][ ][ ][ ][ ][ ]
       ///              ^
       ///              Store there
   store %2 9
*/
static void visit_array_decl(struct ast_array_decl *ast)
{
    assert(ast->arity->type == AST_COMPOUND_STMT && "Array declarator expects compound ast enclosure list.");

    uint64_t             next_idx  = ir_var_idx++;
    struct ast_compound *enclosure = ast->arity->ast;

    assert(enclosure->size <= 16 && "Maximum array depth limited to 16.");

    uint64_t *lvls = alloca(enclosure->size * sizeof (uint64_t));
    if (!lvls)
        weak_unreachable("Something funny happened.");

    for (uint64_t i = 0; i < enclosure->size; ++i) {
        struct ast_num *num = enclosure->stmts[i]->ast;
        lvls[i] = num->value;
    }

    ir_last = ir_alloca_array_init(ast->dt, lvls, enclosure->size, next_idx);
    ir_insert_last();

    ir_storage_push(ast->name, next_idx, ast->dt, ast->ptr_depth, ir_last);
}

static void visit_array_access(struct ast_array_access *ast)
{
    /* First just assume one-dimensional array.
       Next extend to multi-dimensional. */

    struct ir_storage_record *record  = ir_storage_get(ast->name);
    struct ast_compound      *indices = ast->indices->ast;

    if (indices->size == 1) {
        visit(indices->stmts[0]);
        struct ir_node *idx = ir_last;

        uint64_t next_idx = ir_var_idx++;

        ir_last = ir_alloca_init(record->dt, /*ptr=*/1, next_idx);
        ir_type_map[next_idx].dt = record->dt;
        ir_type_map[next_idx].ptr_depth = record->ptr_depth;
        ir_insert_last();
        ir_last = ir_store_init(
            ir_sym_init(next_idx),
            ir_bin_init(
                TOK_PLUS,
                ir_sym_init(record->sym_idx),
                idx
            )
        );
        ir_insert_last();
        ir_last = ir_sym_ptr_init(next_idx);
    }
}

static void visit_member(struct ast_member *ast) { (void) ast; }

static void visit_compound(struct ast_compound *ast)
{
    for (uint64_t i = 0; i < ast->size; ++i) {
        struct ast_node *s = ast->stmts[i];
        if (s->type == AST_FUNCTION_CALL) {
            ir_is_global_scope = 1;
            visit(s);
            ir_is_global_scope = 0;
        } else {
            visit(s);
        }
    }
}

static void visit_fn_decl(struct ast_fn_decl *decl)
{
    reset_fn_state();

    visit(decl->args);
    struct ir_node *args = ir_first;

    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;
    ir_save_first = 1;

    ir_reset_state();

    ir_fn_add_return_type(decl->name, decl->data_type);

    visit(decl->body);
    if (decl->data_type == D_T_VOID)
        ir_insert(ir_ret_init(NULL));

    struct ir_node *body = ir_first;

    vector_push_back(
        ir_fn_decls,
        ir_fn_decl_init(
        decl->data_type,
        decl->ptr_depth,
        /* Duplicate to not be depended on AST string values (after free). */
        strdup(decl->name),
        args,
        body
    )
    );

    ir_storage_reset();
}

static void visit_fn_call(struct ast_fn_call *ast)
{
    struct ast_compound *args_ast   = ast->args->ast;
    struct ir_node      *args       = NULL;
    struct ir_node      *args_start = NULL;

    for (uint64_t i = 0; i < args_ast->size; ++i) {
        visit(args_ast->stmts[i]);

        if (args == NULL) {
            args = ir_last;
            args_start = args;
        } else {
            args->next = ir_last;
            args = args->next;
        }
    }

    enum data_type ret_dt = ir_fn_return_type(ast->name);
    /* Duplicate to not be depended on AST string values (after free). */
    char *fcall_name = strdup(ast->name);

    if (ir_is_global_scope) {
        ir_last = ir_fn_call_init(fcall_name, args_start);
        ir_insert(ir_last);
    } else {
        uint64_t next_idx = ir_var_idx++;
        ir_last = ir_alloca_init(ret_dt, /*ptr=*/0, next_idx);
        ir_type_map[next_idx].dt = ret_dt;
        ir_insert_last();

        ir_last = ir_fn_call_init(fcall_name, args_start);
        ir_last = ir_store_sym_init(next_idx, ir_last);
        ir_insert_last();
        ir_last = ir_sym_init(next_idx);
    }

    ir_last_type = ret_dt;
}

static void visit(struct ast_node *ast)
{
    assert(ast);

    void *ptr = ast->ast;
    switch (ast->type) {
    case AST_CHAR_LITERAL:    visit_char(ptr); break;
    case AST_INTEGER_LITERAL: visit_num(ptr); break;
    case AST_FLOATING_POINT_LITERAL: visit_float(ptr); break;
    case AST_STRING_LITERAL:  visit_string(ptr); break;
    case AST_BOOLEAN_LITERAL: visit_bool(ptr); break;
    case AST_SYMBOL:          visit_sym(ptr); break;
    case AST_VAR_DECL:        visit_var_decl(ptr); break;
    case AST_ARRAY_DECL:      visit_array_decl(ptr); break;
    case AST_STRUCT_DECL:     visit_struct_decl(ptr); break;
    case AST_BREAK_STMT:      visit_break(ptr); break;
    case AST_CONTINUE_STMT:   visit_continue(ptr); break;
    case AST_BINARY:          visit_binary(ptr); break;
    case AST_PREFIX_UNARY:    visit_unary(ptr); break;
    case AST_POSTFIX_UNARY:   visit_unary(ptr); break;
    case AST_ARRAY_ACCESS:    visit_array_access(ptr); break;
    case AST_MEMBER:          visit_member(ptr); break;
    case AST_IF_STMT:         visit_if(ptr); break;
    case AST_FOR_STMT:        visit_for(ptr); break;
    case AST_WHILE_STMT:      visit_while(ptr); break;
    case AST_DO_WHILE_STMT:   visit_do_while(ptr); break;
    case AST_RETURN_STMT:     visit_ret(ptr); break;
    case AST_COMPOUND_STMT:   visit_compound(ptr); break;
    case AST_FUNCTION_DECL:   visit_fn_decl(ptr); break;
    case AST_FUNCTION_CALL:   visit_fn_call(ptr); break;
    default:
        weak_unreachable("Wrong AST type (numeric: %d).", ast->type);
    }
}



/* To ease IR access by instruction index, we maintain hashmap. */
really_inline static void link_stmt_map(hashmap_t *stmt_map, struct ir_node *ir)
{
    hashmap_init(stmt_map, 128);

    while (ir) {
        hashmap_put(stmt_map, ir->instr_idx, (uint64_t) ir);
        /* Clear all CFG information. */
        vector_free(ir->cfg.preds);
        vector_free(ir->cfg.succs);
        ir = ir->next;
    }
}

really_inline static struct ir_node *link_target(hashmap_t *stmt_map, uint64_t jmp)
{
    bool     ok   = 0;
    uint64_t addr = hashmap_get(stmt_map, jmp, &ok);

    assert(ok);

    return (struct ir_node *) addr;
}

really_inline static void link_jmp(hashmap_t *stmt_map, struct ir_node *stmt)
{
    struct ir_jump *jump = stmt->ir;
    jump->target = link_target(stmt_map, jump->idx);

    ir_vector_t *prevs = &jump->target->cfg.preds;
    vector_push_back(stmt->cfg.succs, jump->target);
    vector_push_back(*prevs, stmt);
}

/* Return statement cannot have control flow successors.
   Also we cannot reach one return from another. */
really_inline static void link_ret(struct ir_node *stmt)
{
    ir_vector_t *succs = &stmt->cfg.succs;
    ir_vector_t *preds = &stmt->cfg.preds;

    vector_free(*succs);
    vector_foreach_back(*preds, i) {
        struct ir_node *pred = vector_at(*preds, i);
        switch (pred->type) {
        case IR_RET:
            vector_erase(*preds, i);
            break;
        default:
            break;
        }
    }
}

really_inline static void link_cond(hashmap_t *stmt_map, struct ir_node *stmt)
{
    struct ir_cond *cond = stmt->ir;

    uint64_t to = cond->goto_label;
    cond->target = link_target(stmt_map, to);

    vector_push_back(stmt->cfg.succs, cond->target);
    vector_push_back(stmt->cfg.succs, stmt->next);

    ir_vector_t *prevs = &cond->target->cfg.preds;
    vector_push_back(*prevs, stmt);
}

really_inline static void link_stmt(struct ir_node *stmt)
{
    if (stmt->next)
        vector_push_back(stmt->cfg.succs, stmt->next);
}

static void link(struct ir_fn_decl *decl)
{
    struct ir_node *it       = decl->body;
    hashmap_t       stmt_map = {0};

    link_stmt_map(&stmt_map, it);

    hashmap_foreach(&stmt_map, k, v) {
        (void) k;
        struct ir_node *stmt = (struct ir_node *) v;

        /* Link previous. If we have return statement,
           some predecessors will be dropped. */
        if (stmt->instr_idx > 0) {
            struct ir_node *prev = link_target(&stmt_map, stmt->instr_idx - 1);

            if (prev->type != IR_JUMP)
                vector_push_back(stmt->cfg.preds, prev);
        }

        switch (stmt->type) {
        case IR_JUMP:
            link_jmp(&stmt_map, stmt);
            break;

        case IR_COND:
            link_cond(&stmt_map, stmt);
            break;

        case IR_RET:
            link_ret(stmt);
            break;

        default:
            link_stmt(stmt);
            break;
        }
    }

    hashmap_destroy(&stmt_map);
}

void ir_cfg_build(struct ir_fn_decl *decl)
{
    struct ir_node *it     = decl->body;
    uint64_t        cfg_no = 0;

    link(decl);

    while (it) {
        bool new = 0;
        new |= it->cfg.preds.count == 0; /* Very beginning. */
        new |= it->cfg.preds.count >= 2; /* Branch. */
        new |= it->type == IR_JUMP;
        new |= it->type == IR_COND;

        it->cfg_block_no = cfg_no;

        if (new)
            ++cfg_no;

        it = it->next;
    }
}

struct ir_unit ir_gen(struct ast_node *ast)
{
    reset_state();

    visit(ast);

    vector_foreach(ir_fn_decls, i) {
        if (i >= ir_fn_decls.count - 1)
            break;

        struct ir_node *decl      = vector_at(ir_fn_decls, i);
        struct ir_node *decl_next = vector_at(ir_fn_decls, i + 1);

        decl->next = decl_next;
        vector_push_back(decl_next->cfg.preds, decl);
    }

    /* NOTE: Linking and CFG construction is done
             by driver code. */

    struct ir_node *decls = vector_at(ir_fn_decls, 0);

    return (struct ir_unit) { .fn_decls = decls };
}
