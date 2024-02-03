/* ast_dump.c - AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "util/unreachable.h"
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>

static uint32_t ast_indent = 0;

static int32_t visit(FILE *mem, struct ast_node *ast);

static void fprintf_n(FILE *stream, uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i)
        fputc(c, stream);
}

static void ast_print_indent(FILE *stream)
{
    fprintf_n(stream, ast_indent, ' ');
}

static void ast_print_positioned(
    FILE       *mem,
    struct ast_node *ast,
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

static void ast_print(FILE *mem, struct ast_node *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(mem, ast, /*new_line_wanted=*/false, fmt, args);

    va_end(args);
}

static void ast_print_line(FILE *mem, struct ast_node *ast, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    ast_print_positioned(mem, ast, /*new_line_wanted=*/true, fmt, args);

    va_end(args);
}

static void visit_binary(FILE *mem, struct ast_node *ast)
{
    struct ast_binary *binary = ast->ast;

    ast_print(mem, ast, "BinaryOperator");
    fprintf(mem, "%s\n", tok_to_string(binary->op));

    ast_indent += 2;
    visit(mem, binary->lhs);
    visit(mem, binary->rhs);
    ast_indent -= 2;
}

static void visit_bool(FILE *mem, struct ast_node *ast)
{
    struct ast_bool *boolean = ast->ast;

    ast_print(mem, ast, "BooleanLiteral");
    fprintf(mem, "%s\n", boolean->value ? "true" : "false");
}

static void visit_break(FILE *mem, struct ast_node *ast)
{
    ast_print_line(mem, ast, "BreakStmt");
}

static void visit_char(FILE *mem, struct ast_node *ast)
{
    struct ast_char *c = ast->ast;

    ast_print(mem, ast, "CharLiteral");
    fprintf(mem, "'%c'\n", c->value);
}

static void visit_compound(FILE *mem, struct ast_node *ast)
{
    struct ast_compound *compound = ast->ast;

    if (!compound)
        return;

    ast_print_line(mem, ast, "CompoundStmt");

    if (!compound->stmts)
        return;

    ast_indent += 2;
    for (uint64_t i = 0; i < compound->size; ++i) {
        visit(mem, compound->stmts[i]);
    }
    ast_indent -= 2;
}

static void visit_continue(FILE *mem, struct ast_node *ast)
{
    ast_print_line(mem, ast, "ContinueStmt");
}

static void visit_float(FILE *mem, struct ast_node *ast)
{
    struct ast_float *f = ast->ast;

    ast_print(mem, ast, "FloatLiteral");
    fprintf(mem, "%f\n", f->value);
}

static void visit_for(FILE *mem, struct ast_node *ast)
{
    struct ast_for *for_stmt = ast->ast;

    ast_print_line(mem, ast, "ForStmt");
    ast_indent += 2;

    if (for_stmt->init) {
        ast_print_line(mem, for_stmt->init, "ForStmtInit");
        ast_indent += 2;
        visit(mem, for_stmt->init);
        ast_indent -= 2;
    }

    if (for_stmt->condition) {
        ast_print_line(mem, for_stmt->condition, "ForStmtCondition");
        ast_indent += 2;
        visit(mem, for_stmt->condition);
        ast_indent -= 2;
    }

    if (for_stmt->increment) {
        ast_print_line(mem, for_stmt->increment, "ForStmtIncrement");
        ast_indent += 2;
        visit(mem, for_stmt->increment);
        ast_indent -= 2;
    }

    ast_print_line(mem, for_stmt->body, "ForStmtBody");
    ast_indent += 2;
    visit(mem, for_stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_for_range(FILE *mem, struct ast_node *ast)
{
    struct ast_for_range *for_stmt = ast->ast;

    ast_print_line(mem, ast, "ForRangeStmt");
    ast_indent += 2;

    ast_print_line(mem, for_stmt->iter, "ForRangeIterStmt");
    ast_indent += 2;
    visit(mem, for_stmt->iter);
    ast_indent -= 2;

    ast_print_line(mem, for_stmt->range_target, "ForRangeTargetStmt");
    ast_indent += 2;
    visit(mem, for_stmt->range_target);
    ast_indent -= 2;

    ast_print_line(mem, for_stmt->body, "ForRangeStmtBody");
    ast_indent += 2;
    visit(mem, for_stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_if(FILE *mem, struct ast_node *ast)
{
    struct ast_if *if_stmt = ast->ast;

    ast_print_line(mem, ast, "IfStmt");
    ast_indent += 2;

    ast_print_line(mem, if_stmt->condition, "IfStmtCondition");
    ast_indent += 2;
    visit(mem, if_stmt->condition);
    ast_indent -= 2;

    ast_print_line(mem, if_stmt->body, "IfStmtThenBody");
    ast_indent += 2;
    visit(mem, if_stmt->body);
    ast_indent -= 2;

    if (if_stmt->else_body) {
        ast_print_line(mem, if_stmt->else_body, "IfStmtElseBody");
        ast_indent += 2;
        visit(mem, if_stmt->else_body);
        ast_indent -= 2;
    }

    ast_indent -= 2;
}

static void visit_num(FILE *mem, struct ast_node *ast)
{
    struct ast_num *number = ast->ast;

    ast_print(mem, ast, "Number");
    fprintf(mem, "%d\n", number->value);
}

static void visit_ret(FILE *mem, struct ast_node *ast)
{
    struct ast_ret *ret = ast->ast;

    ast_print_line(mem, ast, "ReturnStmt");
    if (ret->op) {
        ast_indent += 2;
        visit(mem, ret->op);
        ast_indent -= 2;
    }
}

static void visit_string(FILE *mem, struct ast_node *ast)
{
    struct ast_string *string = ast->ast;

    ast_print(mem, ast, "StringLiteral");
    fprintf(mem, "%s\n", string->value);
}

static void visit_sym(FILE *mem, struct ast_node *ast)
{
    struct ast_sym *sym = ast->ast;

    ast_print(mem, ast, "Symbol");
    fprintf(mem, "`%s`\n", sym->value);
}

static void visit_unary(FILE *mem, struct ast_node *ast)
{
    struct ast_unary *unary = ast->ast;

    ast_print(mem, ast, "%sfix UnaryOperator", ast->type == AST_POSTFIX_UNARY ? "Post" : "Pre");
    fprintf(mem, "%s\n", tok_to_string(unary->op));

    ast_indent += 2;
    visit(mem, unary->operand);
    ast_indent -= 2;
}

static void visit_struct_decl(FILE *mem, struct ast_node *ast)
{
    struct ast_struct_decl *decl = ast->ast;

    ast_print(mem, ast, "StructDecl");
    fprintf(mem, "`%s`\n", decl->name);

    ast_indent += 2;
    visit(mem, decl->decls);
    ast_indent -= 2;
}

static void visit_var_decl(FILE *mem, struct ast_node *ast)
{
    struct ast_var_decl *decl = ast->ast;
    enum data_type dt = decl->dt;
    unsigned il = decl->ptr_depth;

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
        visit(mem, decl->body);
        ast_indent -= 2;
    }
}

static void visit_array_decl(FILE *mem, struct ast_node *ast)
{
    struct ast_array_decl *decl = ast->ast;
    enum data_type dt = decl->dt;
    unsigned il = decl->ptr_depth;

    ast_print(mem, ast, "ArrayDecl");

    if (dt == D_T_STRUCT) {
        fprintf(mem, "struct %s ", decl->type_name);
    } else {
        fprintf(mem, "%s ", data_type_to_string(dt));
    }

    if (il > 0) {
        fprintf_n(mem, il, '*');
        fprintf(mem, " ");
    }

    struct ast_compound *dimensions = decl->arity->ast;

    for (uint64_t i = 0; i < dimensions->size; ++i)
        fprintf(mem, "[%d]", ( (struct ast_num *)(dimensions->stmts[i]->ast) )->value);

    fprintf(mem, " `%s`\n", decl->name);

    if (decl->body) {
        ast_indent += 2;
        visit(mem, decl->body);
        ast_indent -= 2;
    }
}

static void visit_array_access(FILE *mem, struct ast_node *ast)
{
    struct ast_array_access *stmt = ast->ast;

    ast_print(mem, ast, "ArrayAccess");
    fprintf(mem, "`%s`\n", stmt->name);

    struct ast_compound *indices = stmt->indices->ast;

    ast_indent += 2;
    for (uint64_t i = 0; i < indices->size; ++i) {
        visit(mem, indices->stmts[i]);
    }
    ast_indent -= 2;
}

static void visit_member(FILE *mem, struct ast_node *ast)
{
    struct ast_member *stmt = ast->ast;

    ast_print_line(mem, ast, "StructMember");

    ast_indent += 2;
    visit(mem, stmt->structure);
    visit(mem, stmt->member);
    ast_indent -= 2;
}

static void visit_fn_decl(FILE *mem, struct ast_node *ast)
{
    struct ast_fn_decl *decl = ast->ast;
    bool is_proto = decl->body == NULL;

    ast_print_line(mem, ast, is_proto ? "FunctionProtoDecl" : "FunctionDecl");

    ast_indent += 2;
    ast_print(mem, ast, is_proto ? "FunctionProtoRetType" : "FunctionDeclRetType");
    fprintf(mem, "%s\n", data_type_to_string(decl->data_type));

    ast_print(mem, ast, is_proto ? "FunctionProtoName" : "FunctionDeclName");
    fprintf(mem, "`%s`\n", decl->name);

    ast_print_line(mem, ast, is_proto ? "FunctionProtoArgs" : "FunctionDeclArgs");

    ast_indent += 2;
    struct ast_compound *args = decl->args->ast;
    if (args && args->size > 0)
        visit(mem, decl->args);
    ast_indent -= 2;

    if (is_proto) {
        ast_indent -= 2;
        return;
    }

    ast_print_line(mem, ast, "FunctionDeclBody");

    ast_indent += 2;
    visit(mem, decl->body);
    ast_indent -= 2;
}

static void visit_fn_call(FILE *mem, struct ast_node *ast)
{
    struct ast_fn_call *stmt = ast->ast;

    ast_print(mem, ast, "FunctionCall");
    fprintf(mem, "`%s`\n", stmt->name);

    ast_indent += 2;
    ast_print_line(mem, ast, "FunctionCallArgs");

    ast_indent += 2;
    struct ast_compound *args = stmt->args->ast;
    if (args && args->size > 0)
        visit(mem, stmt->args);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_while(FILE *mem, struct ast_node *ast)
{
    struct ast_while *stmt = ast->ast;

    ast_print_line(mem, ast, "WhileStmt");

    ast_indent += 2;
    ast_print_line(mem, stmt->cond, "WhileStmtCond");
    ast_indent += 2;
    visit(mem, stmt->cond);
    ast_indent -= 2;

    ast_print_line(mem, stmt->body, "WhileStmtBody");
    ast_indent += 2;
    visit(mem, stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_do_while(FILE *mem, struct ast_node *ast)
{
    struct ast_do_while *stmt = ast->ast;

    ast_print_line(mem, ast, "DoWhileStmt");

    ast_indent += 2;
    ast_print_line(mem, stmt->body, "DoWhileStmtBody");
    ast_indent += 2;
    visit(mem, stmt->body);
    ast_indent -= 2;
    ast_indent -= 2;

    ast_indent += 2;
    ast_print_line(mem, stmt->condition, "DoWhileStmtCond");
    ast_indent += 2;
    visit(mem, stmt->condition);
    ast_indent -= 2;
    ast_indent -= 2;
}

static void visit_implicit_cast(FILE *mem, struct ast_node *ast)
{
    struct ast_implicit_cast *stmt = ast->ast;

    ast_print(mem, ast, "ImplicitCastExpr");
    fprintf(
        mem, "%s -> %s\n",
        data_type_to_string(stmt->from),
        data_type_to_string(stmt->to));

    ast_indent += 2;
    visit(mem, stmt->body);
    ast_indent -= 2;
}

int32_t visit(FILE *mem, struct ast_node *ast)
{
    if (mem == NULL || ast == NULL) {
        return -1;
    }

    switch (ast->type) {
    case AST_CHAR_LITERAL:
        visit_char(mem, ast);
        break;
    case AST_INTEGER_LITERAL:
        visit_num(mem, ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_float(mem, ast);
        break;
    case AST_STRING_LITERAL:
        visit_string(mem, ast);
        break;
    case AST_BOOLEAN_LITERAL:
        visit_bool(mem, ast);
        break;
    case AST_SYMBOL:
        visit_sym(mem, ast);
        break;
    case AST_VAR_DECL:
        visit_var_decl(mem, ast);
        break;
    case AST_ARRAY_DECL:
        visit_array_decl(mem, ast);
        break;
    case AST_STRUCT_DECL:
        visit_struct_decl(mem, ast);
        break;
    case AST_BREAK_STMT:
        visit_break(mem, ast);
        break;
    case AST_CONTINUE_STMT:
        visit_continue(mem, ast);
        break;
    case AST_BINARY:
        visit_binary(mem, ast);
        break;
    case AST_PREFIX_UNARY:
        visit_unary(mem, ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_unary(mem, ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_array_access(mem, ast);
        break;
    case AST_MEMBER:
        visit_member(mem, ast);
        break;
    case AST_IF_STMT:
        visit_if(mem, ast);
        break;
    case AST_FOR_STMT:
        visit_for(mem, ast);
        break;
    case AST_FOR_RANGE_STMT:
        visit_for_range(mem, ast);
        break;
    case AST_WHILE_STMT:
        visit_while(mem, ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_do_while(mem, ast);
        break;
    case AST_RETURN_STMT:
        visit_ret(mem, ast);
        break;
    case AST_COMPOUND_STMT:
        visit_compound(mem, ast);
        break;
    case AST_FUNCTION_DECL:
        visit_fn_decl(mem, ast);
        break;
    case AST_FUNCTION_CALL:
        visit_fn_call(mem, ast);
        break;
    case AST_IMPLICIT_CAST:
        visit_implicit_cast(mem, ast);
        break;
    default:
        weak_unreachable("Unknown AST type (numeric: %d).", ast->type);
    }

    return 0;
}

int32_t ast_dump(FILE *mem, struct ast_node *ast)
{
    ast_indent = 0;

    int32_t code = visit(mem, ast);
    fflush(mem);
    return code;
}