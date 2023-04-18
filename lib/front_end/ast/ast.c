/* ast.c - All AST statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "utility/alloc.h"
#include "utility/unreachable.h"


///////////////////////////////////////////////
///              Array access               ///
///////////////////////////////////////////////
ast_node_t *ast_array_access_init(char *name, ast_node_t *indices, uint16_t line_no, uint16_t col_no)
{
    ast_array_access_t *ast = weak_calloc(1, sizeof(ast_array_access_t));
    ast->name = name;
    ast->indices = indices;
    return ast_node_init(AST_ARRAY_ACCESS, ast, line_no, col_no);
}

void ast_array_access_cleanup(ast_array_access_t *ast)
{
    ast_node_cleanup(ast->indices);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Array declaration          ///
///////////////////////////////////////////////
ast_node_t *ast_array_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    ast_node_t  *arity_list,
    uint16_t     indirection_lvl,
    uint16_t     line_no,
    uint16_t     col_no
) {
    ast_array_decl_t *ast = weak_calloc(1, sizeof(ast_array_decl_t));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->arity_list = arity_list;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_ARRAY_DECL, ast, line_no, col_no);
}

void ast_array_decl_cleanup(ast_array_decl_t *ast)
{
    ast_node_cleanup(ast->arity_list);
    if (ast->type_name)
        weak_free(ast->type_name);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Binary expression          ///
///////////////////////////////////////////////
ast_node_t *ast_binary_init(
    tok_type_e  operation,
    ast_node_t *lhs,
    ast_node_t *rhs,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_binary_t *ast = weak_calloc(1, sizeof(ast_binary_t));
    ast->operation = operation;
    ast->lhs = lhs;
    ast->rhs = rhs;
    return ast_node_init(AST_BINARY, ast, line_no, col_no);
}

void ast_binary_cleanup(ast_binary_t *ast)
{
    ast_node_cleanup(ast->lhs);
    ast_node_cleanup(ast->rhs);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Boolean                    ///
///////////////////////////////////////////////
ast_node_t *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no)
{
    ast_bool_t *ast = weak_calloc(1, sizeof(ast_bool_t));
    ast->value = value;
    return ast_node_init(AST_BOOLEAN_LITERAL, ast, line_no, col_no);
}

void ast_bool_cleanup(ast_bool_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Break statemen             ///
///////////////////////////////////////////////
ast_node_t *ast_break_init(uint16_t line_no, uint16_t col_no)
{
    ast_break_t *ast = weak_calloc(1, sizeof(ast_break_t));
    return ast_node_init(AST_BREAK_STMT, ast, line_no, col_no);
}

void ast_break_cleanup(ast_break_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Character                  ///
///////////////////////////////////////////////
ast_node_t *ast_char_init(char value, uint16_t line_no, uint16_t col_no)
{
    ast_char_t *ast = weak_calloc(1, sizeof(ast_char_t));
    ast->value = value;
    return ast_node_init(AST_CHAR_LITERAL, ast, line_no, col_no);
}

void ast_char_cleanup(ast_char_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Compound statement         ///
///////////////////////////////////////////////
ast_node_t *ast_compound_init(uint64_t size, ast_node_t **stmts, uint16_t line_no, uint16_t col_no)
{
    ast_compound_t *ast = weak_calloc(1, sizeof(ast_compound_t));
    ast->size = size;
    ast->stmts = stmts;
    return ast_node_init(AST_COMPOUND_STMT, ast, line_no, col_no);
}

void ast_compound_cleanup(ast_compound_t *ast)
{
    for (uint64_t i = 0; i < ast->size; ++i) {
        ast_node_cleanup(ast->stmts[i]);
    }

    weak_free(ast->stmts);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Continue statement         ///
///////////////////////////////////////////////
ast_node_t *ast_continue_init(uint16_t line_no, uint16_t col_no)
{
    ast_continue_t *ast = weak_calloc(1, sizeof(ast_continue_t));
    return ast_node_init(AST_CONTINUE_STMT, ast, line_no, col_no);
}

void ast_continue_cleanup(ast_continue_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Do while                   ///
///////////////////////////////////////////////
ast_node_t *ast_do_while_init(ast_node_t *body, ast_node_t *condition, uint16_t line_no, uint16_t col_no)
{
    ast_do_while_t *ast = weak_calloc(1, sizeof(ast_do_while_t));
    ast->body = body;
    ast->condition = condition;
    return ast_node_init(AST_DO_WHILE_STMT, ast, line_no, col_no);
}

void ast_do_while_cleanup(ast_do_while_t *ast)
{
    ast_node_cleanup(ast->body);
    ast_node_cleanup(ast->condition);
    weak_free(ast);
}


///////////////////////////////////////////////
///         Floating point literal          ///
///////////////////////////////////////////////
ast_node_t *ast_float_init(float value, uint16_t line_no, uint16_t col_no)
{
    ast_float_t *ast = weak_calloc(1, sizeof(ast_float_t));
    ast->value = value;
    return ast_node_init(AST_FLOATING_POINT_LITERAL, ast, line_no, col_no);
}

void ast_float_cleanup(ast_float_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              For statement              ///
///////////////////////////////////////////////
ast_node_t *ast_for_init(
    ast_node_t *init,
    ast_node_t *condition,
    ast_node_t *increment,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_for_t *ast = weak_calloc(1, sizeof(ast_for_t));
    ast->init = init;
    ast->condition = condition;
    ast->increment = increment;
    ast->body = body;
    return ast_node_init(AST_FOR_STMT, ast, line_no, col_no);
}

void ast_for_cleanup(ast_for_t *ast)
{
    if (ast->init)
        ast_node_cleanup(ast->init);

    if (ast->condition)
        ast_node_cleanup(ast->condition);

    if (ast->increment)
        ast_node_cleanup(ast->increment);

    ast_node_cleanup(ast->body);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Function call              ///
///////////////////////////////////////////////
ast_node_t *ast_function_call_init(
    char       *name,
    ast_node_t *args,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_function_call_t *ast = weak_calloc(1, sizeof(ast_function_call_t));
    ast->name = name;
    ast->args = args;
    return ast_node_init(AST_FUNCTION_CALL, ast, line_no, col_no);
}

void ast_function_call_cleanup(ast_function_call_t *ast)
{
    ast_node_cleanup(ast->args);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Function declaration       ///
///////////////////////////////////////////////
ast_node_t *ast_function_decl_init(
    data_type_e data_type,
    char       *name,
    ast_node_t *args,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_function_decl_t *ast = weak_calloc(1, sizeof(ast_function_decl_t));
    ast->data_type = data_type;
    ast->name = name;
    ast->args = args;
    ast->body = body;
    return ast_node_init(AST_FUNCTION_DECL, ast, line_no, col_no);
}

void ast_function_decl_cleanup(ast_function_decl_t *ast)
{
    ast_node_cleanup(ast->args);
    if (ast->body)
        ast_node_cleanup(ast->body);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              If statement               ///
///////////////////////////////////////////////
ast_node_t *ast_if_init(
    ast_node_t *condition,
    ast_node_t *body,
    ast_node_t *else_body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_if_t *ast = weak_calloc(1, sizeof(ast_if_t));
    ast->condition = condition;
    ast->body = body;
    ast->else_body = else_body;
    return ast_node_init(AST_IF_STMT, ast, line_no, col_no);
}

void ast_if_cleanup(ast_if_t *ast)
{
    ast_node_cleanup(ast->condition);
    ast_node_cleanup(ast->body);

    if (ast->else_body)
        ast_node_cleanup(ast->else_body);

    weak_free(ast);
}


///////////////////////////////////////////////
///              Structure access           ///
///////////////////////////////////////////////
ast_node_t *ast_member_init(
    ast_node_t *structure,
    ast_node_t *member,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_member_t *ast = weak_calloc(1, sizeof(ast_member_t));
    ast->structure = structure;
    ast->member = member;
    return ast_node_init(AST_MEMBER, ast, line_no, col_no);
}

void ast_member_cleanup(ast_member_t *ast)
{
    ast_node_cleanup(ast->member);
    ast_node_cleanup(ast->structure);
    weak_free(ast);
}

///////////////////////////////////////////////
///              Integral literal           ///
///////////////////////////////////////////////
ast_node_t *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no)
{
    ast_num_t *ast = weak_calloc(1, sizeof(ast_num_t));
    ast->value = value;
    return ast_node_init(AST_INTEGER_LITERAL, ast, line_no, col_no);
}

void ast_num_cleanup(ast_num_t *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Return statement           ///
///////////////////////////////////////////////
ast_node_t *ast_return_init(ast_node_t *operand, uint16_t line_no, uint16_t col_no)
{
    ast_return_t *ast = weak_calloc(1, sizeof(ast_return_t));
    ast->operand = operand;
    return ast_node_init(AST_RETURN_STMT, ast, line_no, col_no);
}

void ast_return_cleanup(ast_return_t *ast)
{
    if (ast->operand)
        ast_node_cleanup(ast->operand);

    weak_free(ast);
}


///////////////////////////////////////////////
///              String literal             ///
///////////////////////////////////////////////
ast_node_t *ast_string_init(char *value, uint16_t line_no, uint16_t col_no)
{
    ast_string_t *ast = weak_calloc(1, sizeof(ast_string_t));
    ast->value = value;
    return ast_node_init(AST_STRING_LITERAL, ast, line_no, col_no);
}

void ast_string_cleanup(ast_string_t *ast)
{
    weak_free(ast->value);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Structure declaration      ///
///////////////////////////////////////////////
ast_node_t *ast_struct_decl_init(char *name, ast_node_t *decls, uint16_t line_no, uint16_t col_no)
{
    ast_struct_decl_t *ast = weak_calloc(1, sizeof(ast_struct_decl_t));
    ast->name = name;
    ast->decls = decls;
    return ast_node_init(AST_STRUCT_DECL, ast, line_no, col_no);
}

void ast_struct_decl_cleanup(ast_struct_decl_t *ast)
{
    ast_node_cleanup(ast->decls);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Symbol                     ///
///////////////////////////////////////////////
ast_node_t *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no)
{
    ast_symbol_t *ast = weak_calloc(1, sizeof(ast_symbol_t));
    ast->value = value;
    return ast_node_init(AST_SYMBOL, ast, line_no, col_no);
}

void ast_symbol_cleanup(ast_symbol_t *ast)
{
    weak_free(ast->value);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Unary statement            ///
///////////////////////////////////////////////
ast_node_t *ast_unary_init(ast_type_e type, tok_type_e operation, ast_node_t *operand, uint16_t line_no, uint16_t col_no)
{
    if (type != AST_PREFIX_UNARY && type != AST_POSTFIX_UNARY) {
        weak_fatal_error("Expected prefix or postfix unary type.");
    }

    ast_unary_t *ast = weak_calloc(1, sizeof(ast_unary_t));
    ast->operation = operation;
    ast->operand = operand;
    return ast_node_init(type, ast, line_no, col_no);
}

void ast_unary_cleanup(ast_unary_t *ast)
{
    ast_node_cleanup(ast->operand);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Variable declaration       ///
///////////////////////////////////////////////
ast_node_t *ast_var_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    uint16_t     indirection_lvl,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
) {
    ast_var_decl_t *ast = weak_calloc(1, sizeof(ast_var_decl_t));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->body = body;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_VAR_DECL, ast, line_no, col_no);
}

void ast_var_decl_cleanup(ast_var_decl_t *ast)
{
    weak_free(ast->name);

    if (ast->type_name)
        weak_free(ast->type_name);

    if (ast->body)
        ast_node_cleanup(ast->body);

    weak_free(ast);
}


///////////////////////////////////////////////
///              While statement            ///
///////////////////////////////////////////////
ast_node_t *ast_while_init(ast_node_t *condition, ast_node_t *body, uint16_t line_no, uint16_t col_no)
{
    ast_while_t *ast = weak_calloc(1, sizeof(ast_while_t));
    ast->condition = condition;
    ast->body = body;
    return ast_node_init(AST_WHILE_STMT, ast, line_no, col_no);
}

void ast_while_cleanup(ast_while_t *ast)
{
    ast_node_cleanup(ast->condition);
    ast_node_cleanup(ast->body);
    weak_free(ast);
}


///////////////////////////////////////////////
///              AST Node                   ///
///////////////////////////////////////////////
ast_node_t *ast_node_init(ast_type_e type, void *ast, uint16_t line_no, uint16_t col_no)
{
    ast_node_t *node = weak_calloc(1, sizeof(ast_node_t));
    node->type = type;
    node->ast = ast;
    node->line_no = line_no;
    node->col_no = col_no;
    return node;
}

void ast_node_cleanup(ast_node_t *ast)
{
    if (!ast) return;
    switch (ast->type) {
    case AST_CHAR_LITERAL:
        ast_char_cleanup(ast->ast);
        break;
    case AST_INTEGER_LITERAL:
        ast_num_cleanup(ast->ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        ast_float_cleanup(ast->ast);
        break;
    case AST_STRING_LITERAL:
        ast_string_cleanup(ast->ast);
        break;
    case AST_BOOLEAN_LITERAL:
        ast_bool_cleanup(ast->ast);
        break;
    case AST_SYMBOL:
        ast_symbol_cleanup(ast->ast);
        break;
    case AST_VAR_DECL:
        ast_var_decl_cleanup(ast->ast);
        break;
    case AST_ARRAY_DECL:
        ast_array_decl_cleanup(ast->ast);
        break;
    case AST_STRUCT_DECL:
        ast_struct_decl_cleanup(ast->ast);
        break;
    case AST_BREAK_STMT:
        ast_break_cleanup(ast->ast);
        break;
    case AST_CONTINUE_STMT:
        ast_continue_cleanup(ast->ast);
        break;
    case AST_BINARY:
        ast_binary_cleanup(ast->ast);
        break;
    case AST_PREFIX_UNARY:
        ast_unary_cleanup(ast->ast);
        break;
    case AST_POSTFIX_UNARY:
        ast_unary_cleanup(ast->ast);
        break;
    case AST_ARRAY_ACCESS:
        ast_array_access_cleanup(ast->ast);
        break;
    case AST_MEMBER:
        ast_member_cleanup(ast->ast);
        break;
    case AST_IF_STMT:
        ast_if_cleanup(ast->ast);
        break;
    case AST_FOR_STMT:
        ast_for_cleanup(ast->ast);
        break;
    case AST_WHILE_STMT:
        ast_while_cleanup(ast->ast);
        break;
    case AST_DO_WHILE_STMT:
        ast_do_while_cleanup(ast->ast);
        break;
    case AST_RETURN_STMT:
        ast_return_cleanup(ast->ast);
        break;
    case AST_COMPOUND_STMT:
        ast_compound_cleanup(ast->ast);
        break;
    case AST_FUNCTION_DECL:
        ast_function_decl_cleanup(ast->ast);
        break;
    case AST_FUNCTION_CALL:
        ast_function_call_cleanup(ast->ast);
        break;
    default:
        weak_unreachable("Should not reach here.");
    }
    weak_free(ast);
}