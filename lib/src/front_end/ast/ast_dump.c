/* visit_node.c - AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_bool.h"
#include "front_end/ast/ast_char.h"
#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_float.h"
#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_node.h"
#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_string.h"
#include "front_end/ast/ast_struct_decl.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_while.h"
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>

static uint32_t ast_indent = 0;

static int32_t visit_node(FILE *memstream, ast_node_t *ast);

static void fprintf_n(FILE *stream, uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i)
        fputc(c, stream);

    fflush(stream);
}

static void ast_print_indent(FILE *stream)
{
    fprintf_n(stream, ast_indent, ' ');
}

static void ast_print_positioned(
    FILE       *memstream,
    ast_node_t *ast,
    bool        new_line_wanted,
    const char *fmt,
    va_list     list
) {
    ast_print_indent(memstream);

    vfprintf(memstream, fmt, list);

    fprintf(
        memstream, " <line:%u, col:%u>%c",
        ast->line_no,
        ast->col_no,
        new_line_wanted ? '\n' : ' '
    );
    fflush(memstream);
}

static void ast_print(FILE *memstream, ast_node_t *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(memstream, ast, /*new_line_wanted=*/false, fmt, args);

    va_end(args);
}

static void ast_print_line(FILE *memstream, ast_node_t *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(memstream, ast, /*new_line_wanted=*/true, fmt, args);

    va_end(args);
}

void visit_ast_binary(FILE *memstream, ast_node_t *ast)
{
    ast_binary_t *binary = ast->ast;

    ast_print(memstream, ast, "BinaryOperator");
    fprintf(memstream, "%s\n", tok_to_string(binary->operation));

    ast_indent += 2;
    visit_node(memstream, binary->lhs);
    visit_node(memstream, binary->rhs);
    ast_indent -= 2;
}

void visit_ast_bool(FILE *memstream, ast_node_t *ast)
{
    ast_bool_t *boolean = ast->ast;

    ast_print(memstream, ast, "BooleanLiteral");
    fprintf(memstream, "%s\n", boolean->value ? "true" : "false");
}

void visit_ast_break(FILE *memstream, ast_node_t *ast)
{
    ast_print_line(memstream, ast, "BreakStmt");
}

void visit_ast_char(FILE *memstream, ast_node_t *ast)
{
    ast_char_t *c = ast->ast;

    ast_print(memstream, ast, "CharLiteral");
    fprintf(memstream, "'%c'\n", c->value);
}

void visit_ast_compound(FILE *memstream, ast_node_t *ast)
{
    ast_compound_t *compound = ast->ast;

    if (!compound || !compound->stmts)
        return;

    ast_print_line(memstream, ast, "CompoundStmt");

    ast_indent += 2;
    for (uint64_t i = 0; i < compound->size; ++i) {
        visit_node(memstream, compound->stmts[i]);
    }
    ast_indent -= 2;
}

void visit_ast_continue(FILE *memstream, ast_node_t *ast)
{
    ast_print_line(memstream, ast, "ContinueStmt");
}

void visit_ast_float(FILE *memstream, ast_node_t *ast)
{
    ast_float_t *f = ast->ast;

    ast_print(memstream, ast, "FloatLiteral");
    fprintf(memstream, "%f\n", f->value);
}

void visit_ast_for(FILE *memstream, ast_node_t *ast)
{
    ast_for_t *for_stmt = ast->ast;

    ast_print_line(memstream, ast, "ForStmt");
    ast_indent += 2;

    if (for_stmt->init) {
        ast_print_line(memstream, for_stmt->init, "ForStmtInit");
        ast_indent += 2;
        visit_node(memstream, for_stmt->init);
        ast_indent -= 2;
    }

    if (for_stmt->condition) {
        ast_print_line(memstream, for_stmt->condition, "ForStmtCondition");
        ast_indent += 2;
        visit_node(memstream, for_stmt->condition);
        ast_indent -= 2;
    }

    if (for_stmt->increment) {
        ast_print_line(memstream, for_stmt->increment, "ForStmtIncrement");
        ast_indent += 2;
        visit_node(memstream, for_stmt->increment);
        ast_indent -= 2;
    }

    ast_print_line(memstream, for_stmt->body, "ForStmtBody");
    ast_indent += 2;
    visit_node(memstream, for_stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

void visit_ast_if(FILE *memstream, ast_node_t *ast)
{
    ast_if_t *if_stmt = ast->ast;

    ast_print_line(memstream, ast, "IfStmt");
    ast_indent += 2;

    ast_print_line(memstream, if_stmt->condition, "IfStmtCondition");
    ast_indent += 2;
    visit_node(memstream, if_stmt->condition);
    ast_indent -= 2;

    ast_print_line(memstream, if_stmt->body, "IfStmtThenBody");
    ast_indent += 2;
    visit_node(memstream, if_stmt->body);
    ast_indent -= 2;

    if (if_stmt->else_body) {
        ast_print_line(memstream, if_stmt->else_body, "IfStmtElseBody");
        ast_indent += 2;
        visit_node(memstream, if_stmt->else_body);
        ast_indent -= 2;
    }

    ast_indent -= 2;
}

void visit_ast_num(FILE *memstream, ast_node_t *ast)
{
    ast_num_t *number = ast->ast;

    ast_print(memstream, ast, "Number");
    fprintf(memstream, "%d\n", number->value);
}

void visit_ast_return(FILE *memstream, ast_node_t *ast)
{
    ast_return_t *ret = ast->ast;

    if (ret->operand) {
        ast_indent += 2;
        visit_node(memstream, ret->operand);
        ast_indent -= 2;
    }
}

void visit_ast_string(FILE *memstream, ast_node_t *ast)
{
    ast_string_t *string = ast->ast;

    ast_print(memstream, ast, "StringLiteral");
    fprintf(memstream, "%s\n", string->value);
}

void visit_ast_symbol(FILE *memstream, ast_node_t *ast)
{
    ast_symbol_t *sym = ast->ast;

    ast_print(memstream, ast, "Symbol");
    fprintf(memstream, "%s\n", sym->value);
}

void visit_ast_unary(FILE *memstream, ast_node_t *ast)
{
    ast_unary_t *unary = ast->ast;

    ast_print(memstream, ast, "%sfix UnaryOperator", unary->type == AST_POSTFIX_UNARY ? "Pre" : "Post");
    fprintf(memstream, "%s\n", tok_to_string(unary->operation));

    ast_indent += 2;
    visit_node(memstream, unary->operand);
    ast_indent -= 2;
}

void visit_ast_struct_decl(FILE *memstream, ast_node_t *ast)
{
    ast_struct_decl_t *decl = ast->ast;

    ast_print(memstream, ast, "StructDecl");
    fprintf(memstream, "`%s`\n", decl->name);

    ast_indent += 2;
    visit_node(memstream, decl->decls);
    ast_indent -= 2;
}

void visit_ast_var_decl(FILE *memstream, ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    data_type_e dt = decl->data_type;
    unsigned il = decl->indirection_lvl;

    ast_print(memstream, ast, "VarDecl");
    if (dt == D_T_STRUCT) {
        fprintf(memstream, "%s ", decl->type_name);
    } else {
        fprintf(memstream, "%s ", data_type_to_string(dt));
    }

    if (il > 0) {
        fprintf_n(memstream, il, '*');
        fprintf(memstream, " ");
    }

    fprintf(memstream, "`%s`\n", decl->name);

    if (decl->body) {
        ast_indent += 2;
        visit_node(memstream, decl->body);
        ast_indent -= 2;
    }
}

void visit_ast_array_decl(FILE *memstream, ast_node_t *ast)
{
    ast_array_decl_t *decl = ast->ast;
    data_type_e dt = decl->data_type;
    unsigned il = decl->indirection_lvl;

    ast_print(memstream, ast, "ArrayDecl");

    if (dt == D_T_STRUCT) {
        fprintf(memstream, "%s ", decl->type_name);
    }

    if (il > 0) {
        fprintf_n(memstream, il, '*');
        fprintf(memstream, " ");
    }

    ast_compound_t *dimensions = decl->arity_list;
    for (uint64_t i = 0; i < dimensions->size; ++i) {
        fprintf(memstream, "[%d]", ((ast_num_t *)dimensions->stmts[i])->value);
    }
    fprintf(memstream, " `%s`\n", decl->name);
}

void visit_ast_array_access(FILE *memstream, ast_node_t *ast)
{
    ast_array_access_t *stmt = ast->ast;

    ast_print(memstream, ast, "ArrayAccess");
    fprintf(memstream, "`%s`", stmt->name);

    ast_indent += 2;
    for (uint64_t i = 0; i < stmt->indices->size; ++i) {
        visit_node(memstream, stmt->indices->stmts[i]);
    }
    ast_indent -= 2;
}

void visit_ast_member(FILE *memstream, ast_node_t *ast)
{
    ast_member_t *stmt = ast->ast;

    ast_print_line(memstream, ast, "StructMember");

    ast_indent += 2;
    visit_node(memstream, stmt->structure);
    visit_node(memstream, stmt->member);
    ast_indent -= 2;
}

void visit_ast_function_decl(FILE *memstream, ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    bool is_proto = decl->body == NULL;

    ast_print_line(memstream, ast, is_proto ? "FunctionPrototype" : "FunctionDecl");

    ast_indent += 2;
    ast_print(memstream, ast, "FunctionDeclRetType");
    fprintf(memstream, "%s\n", data_type_to_string(decl->data_type));

    ast_print(memstream, ast, "FunctionDeclName");
    fprintf(memstream, "`%s`\n", decl->name);

    ast_print_line(memstream, ast, "FunctionDeclArgs");

    visit_node(memstream, decl->args);

    if (is_proto) {
        ast_indent -= 2;
        return;
    }

    ast_indent += 2;
    visit_node(memstream, decl->body);
    ast_indent -= 2;

    ast_print_line(memstream, ast, "FunctionDeclBody");

    ast_indent += 2;
    visit_node(memstream, decl->body);
    ast_indent -= 2;
}

void visit_ast_function_call(FILE *memstream, ast_node_t *ast)
{
    ast_function_call_t *stmt = ast->ast;

    ast_print(memstream, ast, "FunctionCall");
    fprintf(memstream, "`%s`\n", stmt->name);

    ast_indent += 2;
    ast_print_line(memstream, ast, "FunctionCallArgs");

    ast_indent += 2;
    for (uint64_t i = 0; i < stmt->args->size; ++i) {
        visit_node(memstream, stmt->args->stmts[i]);
    }
    ast_indent -= 2;
    ast_indent -= 2;
}

void visit_ast_while(FILE *memstream, ast_node_t *ast)
{
    ast_while_t *stmt = ast->ast;

    ast_print_line(memstream, ast, "WhileStmt");

    ast_indent += 2;
    ast_print_line(memstream, stmt->condition, "WhileStmtCond");
    ast_indent += 2;
    visit_node(memstream, stmt->condition);
    ast_indent -= 2;

    ast_print_line(memstream, stmt->condition, "WhileStmtBody");
    ast_indent += 2;
    visit_node(memstream, stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

void visit_ast_do_while(FILE *memstream, ast_node_t *ast)
{
    ast_do_while_t *stmt = ast->ast;

    ast_print_line(memstream, ast, "DoWhileStmt");

    ast_print_line(memstream, stmt->condition, "DoWhileStmtBody");
    ast_indent += 2;
    visit_node(memstream, stmt->body);
    ast_indent -= 2;

    ast_indent += 2;
    ast_print_line(memstream, stmt->condition, "DoWhileStmtCond");
    ast_indent += 2;
    visit_node(memstream, stmt->condition);
    ast_indent -= 2;
    ast_indent -= 2;
}

int32_t visit_node(FILE *memstream, ast_node_t *ast)
{
    if (memstream == NULL || ast == NULL) {
        return -1;
    }

    switch (ast->type) {
    case AST_CHAR_LITERAL:
        visit_ast_char(memstream, ast);
        break;
    case AST_INTEGER_LITERAL:
        visit_ast_num(memstream, ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_ast_float(memstream, ast);
        break;
    case AST_STRING_LITERAL:
        visit_ast_string(memstream, ast);
        break;
    case AST_BOOLEAN_LITERAL:
        visit_ast_bool(memstream, ast);
        break;
    case AST_SYMBOL:
        visit_ast_symbol(memstream, ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(memstream, ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(memstream, ast);
        break;
    case AST_STRUCT_DECL:
        visit_ast_struct_decl(memstream, ast);
        break;
    case AST_BREAK_STMT:
        visit_ast_break(memstream, ast);
        break;
    case AST_CONTINUE_STMT:
        visit_ast_continue(memstream, ast);
        break;
    case AST_BINARY:
        visit_ast_binary(memstream, ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(memstream, ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(memstream, ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(memstream, ast);
        break;
    case AST_MEMBER:
        visit_ast_member(memstream, ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(memstream, ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(memstream, ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(memstream, ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(memstream, ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(memstream, ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(memstream, ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(memstream, ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(memstream, ast);
        break;
    default:
        fprintf(stderr, "Wrong ast type: %d\n", (int)ast->type);
        return -1;
    }

    return 0;
}

int32_t ast_dump(FILE *memstream, ast_node_t *ast)
{
    ast_indent = 0;

    return visit_node(memstream, ast);
}