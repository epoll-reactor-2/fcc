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
#include "utility/unreachable.h"
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>

static uint32_t ast_indent = 0;

static int32_t visit_node(FILE *mem, ast_node_t *ast);

static void fprintf_n(FILE *stream, uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i)
        fputc_unlocked(c, stream);
}

static void ast_print_indent(FILE *stream)
{
    fprintf_n(stream, ast_indent, ' ');
}

static void ast_print_positioned(
    FILE       *mem,
    ast_node_t *ast,
    bool        new_line_wanted,
    const char *fmt,
    va_list     list
) {
    ast_print_indent(mem);

    vfprintf(mem, fmt, list);

    fprintf(
        mem, " <line:%u, col:%u>%c",
        ast->line_no,
        ast->col_no,
        new_line_wanted ? '\n' : ' '
    );
}

static void ast_print(FILE *mem, ast_node_t *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(mem, ast, /*new_line_wanted=*/false, fmt, args);

    va_end(args);
}

static void ast_print_line(FILE *mem, ast_node_t *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(mem, ast, /*new_line_wanted=*/true, fmt, args);

    va_end(args);
}

static void visit_ast_binary(FILE *mem, ast_node_t *ast)
{
    ast_binary_t *binary = ast->ast;

    ast_print(mem, ast, "BinaryOperator");
    fprintf(mem, "%s\n", tok_to_string(binary->operation));

    ast_indent += 2;
    visit_node(mem, binary->lhs);
    visit_node(mem, binary->rhs);
    ast_indent -= 2;
}

static void visit_ast_bool(FILE *mem, ast_node_t *ast)
{
    ast_bool_t *boolean = ast->ast;

    ast_print(mem, ast, "BooleanLiteral");
    fprintf(mem, "%s\n", boolean->value ? "true" : "false");
}

static void visit_ast_break(FILE *mem, ast_node_t *ast)
{
    ast_print_line(mem, ast, "BreakStmt");
}

static void visit_ast_char(FILE *mem, ast_node_t *ast)
{
    ast_char_t *c = ast->ast;

    ast_print(mem, ast, "CharLiteral");
    fprintf(mem, "'%c'\n", c->value);
}

static void visit_ast_compound(FILE *mem, ast_node_t *ast)
{
    ast_compound_t *compound = ast->ast;

    if (!compound)
        return;

    ast_print_line(mem, ast, "CompoundStmt");

    if (!compound->stmts)
        return;

    ast_indent += 2;
    for (uint64_t i = 0; i < compound->size; ++i) {
        visit_node(mem, compound->stmts[i]);
    }
    ast_indent -= 2;
}

static void visit_ast_continue(FILE *mem, ast_node_t *ast)
{
    ast_print_line(mem, ast, "ContinueStmt");
}

static void visit_ast_float(FILE *mem, ast_node_t *ast)
{
    ast_float_t *f = ast->ast;

    ast_print(mem, ast, "FloatLiteral");
    fprintf(mem, "%f\n", f->value);
}

static void visit_ast_for(FILE *mem, ast_node_t *ast)
{
    ast_for_t *for_stmt = ast->ast;

    ast_print_line(mem, ast, "ForStmt");
    ast_indent += 2;

    if (for_stmt->init) {
        ast_print_line(mem, for_stmt->init, "ForStmtInit");
        ast_indent += 2;
        visit_node(mem, for_stmt->init);
        ast_indent -= 2;
    }

    if (for_stmt->condition) {
        ast_print_line(mem, for_stmt->condition, "ForStmtCondition");
        ast_indent += 2;
        visit_node(mem, for_stmt->condition);
        ast_indent -= 2;
    }

    if (for_stmt->increment) {
        ast_print_line(mem, for_stmt->increment, "ForStmtIncrement");
        ast_indent += 2;
        visit_node(mem, for_stmt->increment);
        ast_indent -= 2;
    }

    ast_print_line(mem, for_stmt->body, "ForStmtBody");
    ast_indent += 2;
    visit_node(mem, for_stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_ast_if(FILE *mem, ast_node_t *ast)
{
    ast_if_t *if_stmt = ast->ast;

    ast_print_line(mem, ast, "IfStmt");
    ast_indent += 2;

    ast_print_line(mem, if_stmt->condition, "IfStmtCondition");
    ast_indent += 2;
    visit_node(mem, if_stmt->condition);
    ast_indent -= 2;

    ast_print_line(mem, if_stmt->body, "IfStmtThenBody");
    ast_indent += 2;
    visit_node(mem, if_stmt->body);
    ast_indent -= 2;

    if (if_stmt->else_body) {
        ast_print_line(mem, if_stmt->else_body, "IfStmtElseBody");
        ast_indent += 2;
        visit_node(mem, if_stmt->else_body);
        ast_indent -= 2;
    }

    ast_indent -= 2;
}

static void visit_ast_num(FILE *mem, ast_node_t *ast)
{
    ast_num_t *number = ast->ast;

    ast_print(mem, ast, "Number");
    fprintf(mem, "%d\n", number->value);
}

static void visit_ast_return(FILE *mem, ast_node_t *ast)
{
    ast_return_t *ret = ast->ast;

    ast_print_line(mem, ast, "ReturnStmt");
    if (ret->operand) {
        ast_indent += 2;
        visit_node(mem, ret->operand);
        ast_indent -= 2;
    }
}

static void visit_ast_string(FILE *mem, ast_node_t *ast)
{
    ast_string_t *string = ast->ast;

    ast_print(mem, ast, "StringLiteral");
    fprintf(mem, "%s\n", string->value);
}

static void visit_ast_symbol(FILE *mem, ast_node_t *ast)
{
    ast_symbol_t *sym = ast->ast;

    ast_print(mem, ast, "Symbol");
    fprintf(mem, "`%s`\n", sym->value);
}

static void visit_ast_unary(FILE *mem, ast_node_t *ast)
{
    ast_unary_t *unary = ast->ast;

    ast_print(mem, ast, "%sfix UnaryOperator", ast->type == AST_POSTFIX_UNARY ? "Post" : "Pre");
    fprintf(mem, "%s\n", tok_to_string(unary->operation));

    ast_indent += 2;
    visit_node(mem, unary->operand);
    ast_indent -= 2;
}

static void visit_ast_struct_decl(FILE *mem, ast_node_t *ast)
{
    ast_struct_decl_t *decl = ast->ast;

    ast_print(mem, ast, "StructDecl");
    fprintf(mem, "`%s`\n", decl->name);

    ast_indent += 2;
    visit_node(mem, decl->decls);
    ast_indent -= 2;
}

static void visit_ast_var_decl(FILE *mem, ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    data_type_e dt = decl->data_type;
    unsigned il = decl->indirection_lvl;

    ast_print(mem, ast, "VarDecl");
    if (dt == D_T_STRUCT) {
        fprintf(mem, "struct %s ", decl->type_name);
    } else {
        fprintf(mem, "%s ", data_type_to_string(dt));
    }

    if (il > 0) {
        fprintf_n(mem, il, '*');
        fprintf(mem, " ");
    }

    fprintf(mem, "`%s`\n", decl->name);

    if (decl->body) {
        ast_indent += 2;
        visit_node(mem, decl->body);
        ast_indent -= 2;
    }
}

static void visit_ast_array_decl(FILE *mem, ast_node_t *ast)
{
    ast_array_decl_t *decl = ast->ast;
    data_type_e dt = decl->data_type;
    unsigned il = decl->indirection_lvl;

    ast_print(mem, ast, "ArrayDecl");

    if (dt == D_T_STRUCT) {
        fprintf(mem, "struct %s ", decl->type_name);
    } else {
        fprintf(mem, "%s ", data_type_to_string(decl->data_type));
    }

    if (il > 0) {
        fprintf_n(mem, il, '*');
        fprintf(mem, " ");
    }

    ast_compound_t *dimensions = decl->arity_list->ast;

    for (uint64_t i = 0; i < dimensions->size; ++i)
        fprintf(mem, "[%d]", ( (ast_num_t *)(dimensions->stmts[i]->ast) )->value);

    fprintf(mem, " `%s`\n", decl->name);
}

static void visit_ast_array_access(FILE *mem, ast_node_t *ast)
{
    ast_array_access_t *stmt = ast->ast;

    ast_print(mem, ast, "ArrayAccess");
    fprintf(mem, "`%s`\n", stmt->name);

    ast_compound_t *indices = stmt->indices->ast;

    ast_indent += 2;
    for (uint64_t i = 0; i < indices->size; ++i) {
        visit_node(mem, indices->stmts[i]);
    }
    ast_indent -= 2;
}

static void visit_ast_member(FILE *mem, ast_node_t *ast)
{
    ast_member_t *stmt = ast->ast;

    ast_print_line(mem, ast, "StructMember");

    ast_indent += 2;
    visit_node(mem, stmt->structure);
    visit_node(mem, stmt->member);
    ast_indent -= 2;
}

static void visit_ast_function_decl(FILE *mem, ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    bool is_proto = decl->body == NULL;

    ast_print_line(mem, ast, is_proto ? "FunctionProtoDecl" : "FunctionDecl");

    ast_indent += 2;
    ast_print(mem, ast, is_proto ? "FunctionProtoRetType" : "FunctionDeclRetType");
    fprintf(mem, "%s\n", data_type_to_string(decl->data_type));

    ast_print(mem, ast, is_proto ? "FunctionProtoName" : "FunctionDeclName");
    fprintf(mem, "`%s`\n", decl->name);

    ast_print_line(mem, ast, is_proto ? "FunctionProtoArgs" : "FunctionDeclArgs");

    ast_indent += 2;
    ast_compound_t *args = decl->args->ast;
    if (args && args->size > 0)
        visit_node(mem, decl->args);
    ast_indent -= 2;

    if (is_proto) {
        ast_indent -= 2;
        return;
    }

    ast_print_line(mem, ast, is_proto ? "FunctionProtoBody" : "FunctionDeclBody");

    ast_indent += 2;
    visit_node(mem, decl->body);
    ast_indent -= 2;
}

static void visit_ast_function_call(FILE *mem, ast_node_t *ast)
{
    ast_function_call_t *stmt = ast->ast;

    ast_print(mem, ast, "FunctionCall");
    fprintf(mem, "`%s`\n", stmt->name);

    ast_indent += 2;
    ast_print_line(mem, ast, "FunctionCallArgs");

    ast_indent += 2;
    ast_compound_t *args = stmt->args->ast;
    if (args && args->size > 0)
        visit_node(mem, stmt->args);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_ast_while(FILE *mem, ast_node_t *ast)
{
    ast_while_t *stmt = ast->ast;

    ast_print_line(mem, ast, "WhileStmt");

    ast_indent += 2;
    ast_print_line(mem, stmt->condition, "WhileStmtCond");
    ast_indent += 2;
    visit_node(mem, stmt->condition);
    ast_indent -= 2;

    ast_print_line(mem, stmt->body, "WhileStmtBody");
    ast_indent += 2;
    visit_node(mem, stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_ast_do_while(FILE *mem, ast_node_t *ast)
{
    ast_do_while_t *stmt = ast->ast;

    ast_print_line(mem, ast, "DoWhileStmt");

    ast_indent += 2;
    ast_print_line(mem, stmt->body, "DoWhileStmtBody");
    ast_indent += 2;
    visit_node(mem, stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;

    ast_indent += 2;
    ast_print_line(mem, stmt->condition, "DoWhileStmtCond");
    ast_indent += 2;
    visit_node(mem, stmt->condition);
    ast_indent -= 2;
    ast_indent -= 2;
}

int32_t visit_node(FILE *mem, ast_node_t *ast)
{
    if (mem == NULL || ast == NULL) {
        return -1;
    }

    switch (ast->type) {
    case AST_CHAR_LITERAL:
        visit_ast_char(mem, ast);
        break;
    case AST_INTEGER_LITERAL:
        visit_ast_num(mem, ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_ast_float(mem, ast);
        break;
    case AST_STRING_LITERAL:
        visit_ast_string(mem, ast);
        break;
    case AST_BOOLEAN_LITERAL:
        visit_ast_bool(mem, ast);
        break;
    case AST_SYMBOL:
        visit_ast_symbol(mem, ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(mem, ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(mem, ast);
        break;
    case AST_STRUCT_DECL:
        visit_ast_struct_decl(mem, ast);
        break;
    case AST_BREAK_STMT:
        visit_ast_break(mem, ast);
        break;
    case AST_CONTINUE_STMT:
        visit_ast_continue(mem, ast);
        break;
    case AST_BINARY:
        visit_ast_binary(mem, ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(mem, ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(mem, ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(mem, ast);
        break;
    case AST_MEMBER:
        visit_ast_member(mem, ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(mem, ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(mem, ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(mem, ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(mem, ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(mem, ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(mem, ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(mem, ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(mem, ast);
        break;
    default:
        weak_unreachable("Wrong AST type");
    }

    return 0;
}

int32_t ast_dump(FILE *mem, ast_node_t *ast)
{
    ast_indent = 0;

    int32_t code = visit_node(mem, ast);
    fflush(mem);
    return code;
}