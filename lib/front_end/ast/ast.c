/* ast.c - All AST statements.
 * Copyright (C) 2022-2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "util/alloc.h"
#include "util/unreachable.h"


///////////////////////////////////////////////
///              Array access               ///
///////////////////////////////////////////////
struct ast_node *ast_array_access_init(char *name, struct ast_node *indices, uint16_t line_no, uint16_t col_no)
{
    struct ast_array_access *ast = weak_calloc(1, sizeof (struct ast_array_access));
    ast->name = name;
    ast->indices = indices;
    return ast_node_init(AST_ARRAY_ACCESS, ast, line_no, col_no);
}

void ast_array_access_cleanup(struct ast_array_access *ast)
{
    ast_node_cleanup(ast->indices);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Array declaration          ///
///////////////////////////////////////////////
struct ast_node *ast_array_decl_init(
    enum data_type   dt,
    char            *name,
    char            *type_name,
    struct ast_node *arity_list,
    uint16_t         indirection_lvl,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_array_decl *ast = weak_calloc(1, sizeof (struct ast_array_decl));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->arity_list = arity_list;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_ARRAY_DECL, ast, line_no, col_no);
}

void ast_array_decl_cleanup(struct ast_array_decl *ast)
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
struct ast_node *ast_binary_init(
    enum token_type  operation,
    struct ast_node *lhs,
    struct ast_node *rhs,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_binary *ast = weak_calloc(1, sizeof (struct ast_binary));
    ast->operation = operation;
    ast->lhs = lhs;
    ast->rhs = rhs;
    return ast_node_init(AST_BINARY, ast, line_no, col_no);
}

void ast_binary_cleanup(struct ast_binary *ast)
{
    ast_node_cleanup(ast->lhs);
    ast_node_cleanup(ast->rhs);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Boolean                    ///
///////////////////////////////////////////////
struct ast_node *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no)
{
    struct ast_bool *ast = weak_calloc(1, sizeof (struct ast_bool));
    ast->value = value;
    return ast_node_init(AST_BOOLEAN_LITERAL, ast, line_no, col_no);
}

void ast_bool_cleanup(struct ast_bool *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Break statemen             ///
///////////////////////////////////////////////
struct ast_node *ast_break_init(uint16_t line_no, uint16_t col_no)
{
    struct ast_break *ast = weak_calloc(1, sizeof (struct ast_break));
    return ast_node_init(AST_BREAK_STMT, ast, line_no, col_no);
}

void ast_break_cleanup(struct ast_break *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Character                  ///
///////////////////////////////////////////////
struct ast_node *ast_char_init(char value, uint16_t line_no, uint16_t col_no)
{
    struct ast_char *ast = weak_calloc(1, sizeof (struct ast_char));
    ast->value = value;
    return ast_node_init(AST_CHAR_LITERAL, ast, line_no, col_no);
}

void ast_char_cleanup(struct ast_char *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Compound statement         ///
///////////////////////////////////////////////
struct ast_node *ast_compound_init(
    uint64_t          size,
    struct ast_node **stmts,
    uint16_t          line_no,
    uint16_t          col_no
) {
    struct ast_compound *ast = weak_calloc(1, sizeof (struct ast_compound));
    ast->size = size;
    ast->stmts = stmts;
    return ast_node_init(AST_COMPOUND_STMT, ast, line_no, col_no);
}

void ast_compound_cleanup(struct ast_compound *ast)
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
struct ast_node *ast_continue_init(uint16_t line_no, uint16_t col_no)
{
    struct ast_continue *ast = weak_calloc(1, sizeof (struct ast_continue));
    return ast_node_init(AST_CONTINUE_STMT, ast, line_no, col_no);
}

void ast_continue_cleanup(struct ast_continue *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Do while                   ///
///////////////////////////////////////////////
struct ast_node *ast_do_while_init(
    struct ast_node *body,
    struct ast_node *condition,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_do_while *ast = weak_calloc(1, sizeof (struct ast_do_while));
    ast->body = body;
    ast->condition = condition;
    return ast_node_init(AST_DO_WHILE_STMT, ast, line_no, col_no);
}

void ast_do_while_cleanup(struct ast_do_while *ast)
{
    ast_node_cleanup(ast->body);
    ast_node_cleanup(ast->condition);
    weak_free(ast);
}


///////////////////////////////////////////////
///         Floating point literal          ///
///////////////////////////////////////////////
struct ast_node *ast_float_init(float value, uint16_t line_no, uint16_t col_no)
{
    struct ast_float *ast = weak_calloc(1, sizeof (struct ast_float));
    ast->value = value;
    return ast_node_init(AST_FLOATING_POINT_LITERAL, ast, line_no, col_no);
}

void ast_float_cleanup(struct ast_float *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              For statement              ///
///////////////////////////////////////////////
struct ast_node *ast_for_init(
    struct ast_node *init,
    struct ast_node *condition,
    struct ast_node *increment,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_for *ast = weak_calloc(1, sizeof (struct ast_for));
    ast->init = init;
    ast->condition = condition;
    ast->increment = increment;
    ast->body = body;
    return ast_node_init(AST_FOR_STMT, ast, line_no, col_no);
}

void ast_for_cleanup(struct ast_for *ast)
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
struct ast_node *ast_function_call_init(
    char            *name,
    struct ast_node *args,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_function_call *ast = weak_calloc(1, sizeof (struct ast_function_call));
    ast->name = name;
    ast->args = args;
    return ast_node_init(AST_FUNCTION_CALL, ast, line_no, col_no);
}

void ast_function_call_cleanup(struct ast_function_call *ast)
{
    ast_node_cleanup(ast->args);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Function declaration       ///
///////////////////////////////////////////////
struct ast_node *ast_function_decl_init(
    enum data_type   data_type,
    char            *name,
    struct ast_node *args,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_function_decl *ast = weak_calloc(1, sizeof (struct ast_function_decl));
    ast->data_type = data_type;
    ast->name = name;
    ast->args = args;
    ast->body = body;
    return ast_node_init(AST_FUNCTION_DECL, ast, line_no, col_no);
}

void ast_function_decl_cleanup(struct ast_function_decl *ast)
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
struct ast_node *ast_if_init(
    struct ast_node *condition,
    struct ast_node *body,
    struct ast_node *else_body,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_if *ast = weak_calloc(1, sizeof (struct ast_if));
    ast->condition = condition;
    ast->body = body;
    ast->else_body = else_body;
    return ast_node_init(AST_IF_STMT, ast, line_no, col_no);
}

void ast_if_cleanup(struct ast_if *ast)
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
struct ast_node *ast_member_init(
    struct ast_node *structure,
    struct ast_node *member,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_member *ast = weak_calloc(1, sizeof (struct ast_member));
    ast->structure = structure;
    ast->member = member;
    return ast_node_init(AST_MEMBER, ast, line_no, col_no);
}

void ast_member_cleanup(struct ast_member *ast)
{
    ast_node_cleanup(ast->member);
    ast_node_cleanup(ast->structure);
    weak_free(ast);
}

///////////////////////////////////////////////
///              Integral literal           ///
///////////////////////////////////////////////
struct ast_node *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no)
{
    struct ast_num *ast = weak_calloc(1, sizeof (struct ast_num));
    ast->value = value;
    return ast_node_init(AST_INTEGER_LITERAL, ast, line_no, col_no);
}

void ast_num_cleanup(struct ast_num *ast)
{
    weak_free(ast);
}


///////////////////////////////////////////////
///              Return statement           ///
///////////////////////////////////////////////
struct ast_node *ast_return_init(struct ast_node *operand, uint16_t line_no, uint16_t col_no)
{
    struct ast_return *ast = weak_calloc(1, sizeof (struct ast_return));
    ast->operand = operand;
    return ast_node_init(AST_RETURN_STMT, ast, line_no, col_no);
}

void ast_return_cleanup(struct ast_return *ast)
{
    if (ast->operand)
        ast_node_cleanup(ast->operand);

    weak_free(ast);
}


///////////////////////////////////////////////
///              String literal             ///
///////////////////////////////////////////////
struct ast_node *ast_string_init(char *value, uint16_t line_no, uint16_t col_no)
{
    struct ast_string *ast = weak_calloc(1, sizeof (struct ast_string));
    ast->value = value;
    return ast_node_init(AST_STRING_LITERAL, ast, line_no, col_no);
}

void ast_string_cleanup(struct ast_string *ast)
{
    weak_free(ast->value);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Structure declaration      ///
///////////////////////////////////////////////
struct ast_node *ast_struct_decl_init(char *name, struct ast_node *decls, uint16_t line_no, uint16_t col_no)
{
    struct ast_struct_decl *ast = weak_calloc(1, sizeof (struct ast_struct_decl));
    ast->name = name;
    ast->decls = decls;
    return ast_node_init(AST_STRUCT_DECL, ast, line_no, col_no);
}

void ast_struct_decl_cleanup(struct ast_struct_decl *ast)
{
    ast_node_cleanup(ast->decls);
    weak_free(ast->name);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Symbol                     ///
///////////////////////////////////////////////
struct ast_node *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no)
{
    struct ast_symbol *ast = weak_calloc(1, sizeof (struct ast_symbol));
    ast->value = value;
    return ast_node_init(AST_SYMBOL, ast, line_no, col_no);
}

void ast_symbol_cleanup(struct ast_symbol *ast)
{
    weak_free(ast->value);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Unary statement            ///
///////////////////////////////////////////////
struct ast_node *ast_unary_init(
    enum ast_type    type,
    enum token_type  operation,
    struct ast_node *operand,
    uint16_t         line_no,
    uint16_t         col_no
) {
    if (type != AST_PREFIX_UNARY && type != AST_POSTFIX_UNARY) {
        weak_fatal_error("Expected prefix or postfix unary type.");
    }

    struct ast_unary *ast = weak_calloc(1, sizeof (struct ast_unary));
    ast->operation = operation;
    ast->operand = operand;
    return ast_node_init(type, ast, line_no, col_no);
}

void ast_unary_cleanup(struct ast_unary *ast)
{
    ast_node_cleanup(ast->operand);
    weak_free(ast);
}


///////////////////////////////////////////////
///              Variable declaration       ///
///////////////////////////////////////////////
struct ast_node *ast_var_decl_init(
    enum data_type   dt,
    char            *name,
    char            *type_name,
    uint16_t         indirection_lvl,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
) {
    struct ast_var_decl *ast = weak_calloc(1, sizeof (struct ast_var_decl));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->body = body;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_VAR_DECL, ast, line_no, col_no);
}

void ast_var_decl_cleanup(struct ast_var_decl *ast)
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
struct ast_node *ast_while_init(
    struct ast_node *condition,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t col_no
) {
    struct ast_while *ast = weak_calloc(1, sizeof (struct ast_while));
    ast->condition = condition;
    ast->body = body;
    return ast_node_init(AST_WHILE_STMT, ast, line_no, col_no);
}

void ast_while_cleanup(struct ast_while *ast)
{
    ast_node_cleanup(ast->condition);
    ast_node_cleanup(ast->body);
    weak_free(ast);
}


///////////////////////////////////////////////
///              AST Node                   ///
///////////////////////////////////////////////
struct ast_node *ast_node_init(enum ast_type type, void *ast, uint16_t line_no, uint16_t col_no)
{
    struct ast_node *node = weak_calloc(1, sizeof (struct ast_node));
    node->type = type;
    node->ast = ast;
    node->line_no = line_no;
    node->col_no = col_no;
    return node;
}

void ast_node_cleanup(struct ast_node *ast)
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