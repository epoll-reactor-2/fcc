/* type_ana.c - Type checker.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/ana.h"
#include "front_end/ana/ast_storage.h"
#include "front_end/ast/ast.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include "util/unreachable.h"
#include <assert.h>

static enum data_type     last_dt = D_T_UNKNOWN;
static uint16_t           last_indir_lvl = 0;
static enum data_type     last_return_dt = D_T_UNKNOWN;
static struct ast_storage storage;

static void init()
{
    ast_storage_init(&storage);
}

static void reset()
{
    last_dt = D_T_UNKNOWN;
    last_return_dt = D_T_UNKNOWN;
    ast_storage_free(&storage);
}

static void visit(struct ast_node *ast);

static void visit_char  () { last_indir_lvl = 0; last_dt = D_T_CHAR; }
static void visit_num   () { last_indir_lvl = 0; last_dt = D_T_INT; }
static void visit_float () { last_indir_lvl = 0; last_dt = D_T_FLOAT; }
static void visit_bool  () { last_indir_lvl = 0; last_dt = D_T_BOOL; }

static void visit_implicit_cast(struct ast_node *ast)
{
    struct ast_implicit_cast *cast = ast->ast;

    last_dt = cast->to;
    visit(cast->body);
}

static bool correct_bin_ops(enum token_type op, enum data_type t)
{
    bool are_correct = false;

    switch (op) {
    case TOK_ASSIGN: /* Fall through. */
        /* We need only check if there are same types on assignment. */
        are_correct = true;
        break;
    /* Integer and floats. */
    case TOK_LE:
    case TOK_LT:
    case TOK_GE:
    case TOK_GT:
    case TOK_EQ:
    case TOK_NEQ:
    case TOK_OR:
    case TOK_AND: /* Fall through. */
        switch (t) {
        case D_T_CHAR:
        case D_T_FLOAT: /* Fall through. */
            last_dt = D_T_INT;
        default: break;
        }
        /* Fall through. */
    case TOK_PLUS:
    case TOK_MINUS:
    case TOK_STAR:
    case TOK_SLASH:
    case TOK_MUL_ASSIGN:
    case TOK_DIV_ASSIGN:
    case TOK_PLUS_ASSIGN:
    case TOK_MINUS_ASSIGN: /* Fall through. */
        are_correct |= t == D_T_INT;
        are_correct |= t == D_T_CHAR;
        are_correct |= t == D_T_BOOL;
        are_correct |= t == D_T_FLOAT;
        break;
    /* Only integers. */
    case TOK_BIT_OR:
    case TOK_BIT_AND:
    case TOK_BIT_XOR:
    case TOK_SHL:
    case TOK_SHR:
    case TOK_MOD:
    case TOK_MOD_ASSIGN:
    case TOK_BIT_OR_ASSIGN:
    case TOK_BIT_AND_ASSIGN:
    case TOK_BIT_XOR_ASSIGN:
    case TOK_SHL_ASSIGN:
    case TOK_SHR_ASSIGN: /* Fall through. */
        are_correct |= t == D_T_INT;
        are_correct |= t == D_T_CHAR;
        are_correct |= t == D_T_BOOL;
        break;
    default:
        break;
    }

    return are_correct;
}

static void visit_binary(struct ast_node *ast)
{
    struct ast_binary *stmt = ast->ast;

    visit(stmt->lhs);
    enum data_type l_dt = last_dt;
    uint16_t l_indir_lvl = last_indir_lvl;

    visit(stmt->rhs);
    enum data_type r_dt = last_dt;
    uint16_t r_indir_lvl = last_indir_lvl;

    bool are_same = false;
    are_same |= l_dt == D_T_BOOL  && r_dt == D_T_BOOL;
    are_same |= l_dt == D_T_CHAR  && r_dt == D_T_CHAR;
    are_same |= l_dt == D_T_FLOAT && r_dt == D_T_FLOAT;
    are_same |= l_dt == D_T_INT   && r_dt == D_T_INT;

    if (l_indir_lvl == 0 && r_indir_lvl == 0) {
        bool correct_ops = correct_bin_ops(stmt->op, l_dt);
        if (!are_same || !correct_ops)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot apply `%s` to %s and %s",
                tok_to_string(stmt->op),
                data_type_to_string(l_dt),
                data_type_to_string(r_dt)
            );
    } else {
        bool correct_ops = l_indir_lvl == r_indir_lvl;
        if (!are_same || !correct_ops)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Indirection level mismatch (%d vs %d)",
                l_indir_lvl,
                r_indir_lvl
            );
    }
}

static void visit_unary(struct ast_node *ast)
{
    struct ast_unary *stmt = ast->ast;
    visit(stmt->operand);
    enum data_type dt = last_dt;

    switch (stmt->op) {
    case TOK_INC:
    case TOK_DEC: /* Fall through. */
        if (dt != D_T_CHAR && dt != D_T_INT)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot apply `%s` to %s",
                tok_to_string(stmt->op),
                data_type_to_string(dt)
            );
        break;
    case TOK_BIT_AND: /* Address operator `&`. */
        ++last_indir_lvl;
        break;
    case TOK_STAR: /* Dereference operator `*`. */
        if (last_indir_lvl == 0)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Attempt to dereference integral type"
            );
        --last_indir_lvl;
        break;
    default:
        fcc_unreachable("Invalid unary operand.");
    }
}

static void visit_symbol(struct ast_node *ast)
{
    struct ast_sym *stmt = ast->ast;
    struct ast_storage_decl *record = ast_storage_lookup(&storage, stmt->value);

    last_dt = record->data_type;
    last_indir_lvl = record->ptr_depth;
}

static void visit_var_decl(struct ast_node *ast)
{
    struct ast_var_decl *decl = ast->ast;
    if (decl->body) {
        visit(decl->body);
        bool are_correct = 0;
        are_correct |= decl->dt == last_dt;
        are_correct |= decl->ptr_depth == 1;
        if (!are_correct)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot assign %s to variable of type %s",
                data_type_to_string(last_dt),
                data_type_to_string(decl->dt)
            );
    }
    ast_storage_push_typed(&storage, decl->name, decl->dt, decl->ptr_depth, ast);
    last_dt = decl->dt;
    last_indir_lvl = decl->ptr_depth;
}

static void visit_array_decl(struct ast_node *ast)
{
    struct ast_array_decl *decl = ast->ast;
    /* Required to be compound. */
    struct ast_compound *dimensions = decl->arity->ast;
    for (uint64_t i = 0; i < dimensions->size; ++i) {
        int32_t num = ( (struct ast_int *) (dimensions->stmts[i]->ast) )->value;
        if (num == 0)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Array size cannot be equal '0'"
            );
    }

    ast_storage_push_typed(&storage, decl->name, decl->dt, decl->ptr_depth, ast);
    last_dt = decl->dt;
    last_indir_lvl = decl->ptr_depth;
}

#define MIN(a, b) ((a) < (b) ? (a) : (b))
static void out_of_range_analysis(struct ast_node *decl_indices_ast, struct ast_node *indices_ast)
{
    struct ast_compound *call_indices = indices_ast->ast;
    struct ast_compound *decl_indices = decl_indices_ast->ast;
    assert(call_indices->size);
    assert(decl_indices->size);
    if (decl_indices->size < call_indices->size) {
        char index[16];
        ordinal_numeral(call_indices->size, index);
        fcc_compile_error(
            call_indices->stmts[0]->line_no,
            call_indices->stmts[0]->col_no,
            "Cannot get %s index of %d dimensional array",
            index, decl_indices->size
        );
    }

    for (uint64_t i = 0; i < MIN(call_indices->size, decl_indices->size); ++i) {
        if (call_indices->stmts[i]->type != AST_INT)
            continue;
        struct ast_node *index_ast = call_indices->stmts[i];
        struct ast_int *num = index_ast->ast;
        struct ast_int *decl_index_ast = decl_indices->stmts[i]->ast;
        int32_t index = num->value;
        int32_t decl_index = decl_index_ast->value;

        if (index < 0)
            fcc_compile_error(
                index_ast->line_no,
                index_ast->col_no,
                "Array index less than zero"
            );

        if (index >= decl_index)
            fcc_compile_error(
                index_ast->line_no,
                index_ast->col_no,
                "Out of range! Index (which is %d) >= array size (which is %d)",
                index, decl_index
            );
    }
}
#undef MIN

static void visit_array_access(struct ast_node *ast)
{
    struct ast_array_access *stmt = ast->ast;
    struct ast_node *record = ast_storage_lookup(&storage, stmt->name)->ast;
    enum data_type decl_dt = D_T_UNKNOWN;

    if (record->type == AST_ARRAY_DECL) {
        struct ast_array_decl *decl = record->ast;
        out_of_range_analysis(decl->arity, stmt->indices);
        decl_dt = decl->dt;
    } else {
        /* If it is not an array, then obviously variable
           declaration. */
        struct ast_var_decl *decl = record->ast;
        if (decl->ptr_depth == 0)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot get index of non-array type"
            );
        decl_dt = decl->dt;
    }
    struct ast_compound *enclosure = stmt->indices->ast;
    for (uint64_t i = 0; i < enclosure->size; ++i) {
        visit(enclosure->stmts[i]);
        if (last_dt != D_T_INT)
            fcc_compile_error(
                enclosure->stmts[i]->line_no,
                enclosure->stmts[i]->col_no,
                "Expected integer as array index, got %s",
                data_type_to_string(last_dt)
            );
    }

    last_dt = decl_dt;
}

static void require_last_dt_convertible_to_bool(struct ast_node *location)
{
    enum data_type dt = last_dt;
    if (dt != D_T_INT && dt != D_T_BOOL)
        fcc_compile_error(
            location->line_no,
            location->col_no,
            "Cannot convert %s to boolean",
            data_type_to_string(dt)
        );
}

static void visit_if(struct ast_node *ast)
{
    struct ast_if *stmt = ast->ast;
    visit(stmt->condition);
    require_last_dt_convertible_to_bool(ast);

    visit(stmt->body);
    if (stmt->else_body)
        visit(stmt->else_body);
}

static void visit_for(struct ast_node *ast)
{
    struct ast_for *stmt = ast->ast;
    if (stmt->init)
        visit(stmt->init);
    if (stmt->condition) {
        visit(stmt->condition);
        require_last_dt_convertible_to_bool(ast);
    }
    if (stmt->increment)
        visit(stmt->increment);
    visit(stmt->body);
}

static void visit_while(struct ast_node *ast)
{
    struct ast_while *stmt = ast->ast;
    visit(stmt->cond);
    require_last_dt_convertible_to_bool(ast);
    visit(stmt->body);
}

static void visit_do_while(struct ast_node *ast)
{
    struct ast_do_while *stmt = ast->ast;
    visit(stmt->body);
    visit(stmt->condition);
    require_last_dt_convertible_to_bool(ast);
}

static void visit_return(struct ast_node *ast)
{
    struct ast_ret *stmt = ast->ast;
    if (stmt->op)
        visit(stmt->op);
    last_return_dt = last_dt;
}

static void visit_compound(struct ast_node *ast)
{
    struct ast_compound *stmt = ast->ast;
    ast_storage_start_scope(&storage);
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit(stmt->stmts[i]);
    ast_storage_end_scope(&storage);
}

static char *decl_name(struct ast_node *decl)
{
    if (decl->type == AST_VAR_DECL)
        return ( (struct ast_var_decl *) decl->ast )->name;

    if (decl->type == AST_ARRAY_DECL)
        return ( (struct ast_array_decl *) decl->ast )->name;

    fcc_unreachable("Declaration expected.");
}

static void visit_fn_call(struct ast_node *ast)
{
    struct ast_fn_call *call = ast->ast;
    struct ast_node *decl = ast_storage_lookup(&storage, call->name)->ast;
    if (decl->type != AST_FUNCTION_DECL)
        fcc_compile_error(
            ast->line_no,
            ast->col_no,
            "`%s` is not a function",
            call->name
        );

    struct ast_fn_decl *fun = decl->ast;
    struct ast_compound *fun_args = fun->args->ast;
    struct ast_compound *call_args = call->args->ast;
    assert(
        fun_args->size == call_args->size &&
        "Call arguments size checked in function analyzer."
    );

    for (uint64_t i = 0; i < call_args->size; ++i) {
        visit(fun_args->stmts[i]);
        enum data_type l_dt = last_dt;
        uint64_t l_indir_lvl = last_indir_lvl;

        visit(call_args->stmts[i]);
        enum data_type r_dt = last_dt;
        uint64_t r_indir_lvl = last_indir_lvl;

        if (l_dt != r_dt)
            fcc_compile_error(
                call_args->stmts[i]->line_no,
                call_args->stmts[i]->col_no,
                "For argument `%s` got %s, but %s expected",
                decl_name(fun_args->stmts[i]),
                data_type_to_string(r_dt),
                data_type_to_string(l_dt)
            );

        if (l_indir_lvl != r_indir_lvl)
            fcc_compile_error(
                ast->line_no,
                ast->col_no,
                "Indirection level mismatch (%d vs %d)",
                l_indir_lvl,
                r_indir_lvl
            );
    }
    last_dt = fun->data_type;
    last_indir_lvl = fun->ptr_depth;
}

static void visit_fn_decl(struct ast_node *ast)
{
    struct ast_fn_decl *decl = ast->ast;
    enum data_type dt = decl->data_type;
    if (decl->body == NULL) { /* Function prototype. */
        ast_storage_push_typed(&storage, decl->name, D_T_FUNC, decl->ptr_depth, ast);
        return;
    }
    ast_storage_start_scope(&storage);
    /* This is to have function in recursive calls. */
    ast_storage_push_typed(&storage, decl->name, D_T_FUNC, decl->ptr_depth, ast);
    /* Don't just visit compound AST, which creates and terminates scope. */
    struct ast_compound *args = decl->args->ast;
    for (uint64_t i = 0; i < args->size; ++i)
        visit(args->stmts[i]);

    visit(decl->body);
    if (dt != D_T_VOID && dt != last_return_dt)
        fcc_compile_error(
            ast->line_no,
            ast->col_no,
            "Cannot return %s instead of %s",
            data_type_to_string(last_return_dt),
            data_type_to_string(dt)
        );
    ast_storage_end_scope(&storage);
    /* This is to have function outside. */
    ast_storage_push_typed(&storage, decl->name, D_T_FUNC, decl->ptr_depth, ast);
}

void visit(struct ast_node *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_MEMBER: /* Unused... Or should be used? */
    case AST_STRUCT_DECL: /* Unused... Or should be used? */
    case AST_BREAK_STMT: /* Unused. */
    case AST_CONTINUE_STMT: /* Unused. */
        break;
    case AST_CHAR:
        visit_char();
        break;
    case AST_INT:
        visit_num();
        break;
    case AST_FLOAT:
        visit_float();
        break;
    case AST_BOOL:
        visit_bool();
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
    case AST_POSTFIX_UNARY: /* Fall through. */
        visit_unary(ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_array_access(ast);
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
        visit_fn_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_fn_call(ast);
        break;
    case AST_IMPLICIT_CAST:
        visit_implicit_cast(ast);
        break;
    default: {
        enum ast_type t = ast->type;
        fcc_unreachable("Unknown AST type (%d, %s).", t, ast_type_to_string(t));
    }
    }
}

void ana_type(struct ast_node *root)
{
    init();
    visit(root);
    reset();
}
