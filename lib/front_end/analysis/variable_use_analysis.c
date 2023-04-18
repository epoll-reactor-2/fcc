/* variable_use_analysis.h - Variable issues detector.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast.h"
#include "utility/diagnostic.h"
#include "utility/unreachable.h"
#include "utility/vector.h"
#include <assert.h>
#include <string.h>

typedef vector_t(ast_node_t *) ast_array_t;
typedef vector_t(vector_t(ast_node_t *)) ast_usage_stack_t;

static ast_usage_stack_t collected_uses = {0};

static void collected_uses_start_scope()
{
    vector_emplace_back(collected_uses);
}

static void collected_uses_end_scope()
{
    vector_erase(collected_uses, collected_uses.count - 1);
}

static void init_internal_state()
{
    /// Initialize first stack entry for the first
    /// scope depth.
    collected_uses_start_scope();
}

static void reset_internal_state()
{
    vector_foreach(collected_uses, i) {
        vector_clear(collected_uses.data[i]);
    }
    vector_clear(collected_uses);
    memset(&collected_uses, 0, sizeof(ast_usage_stack_t));
}

static void collect_ast(ast_node_t *ast)
{
    vector_push_back(vector_back(collected_uses), ast);
}

static bool is_assignment_op(tok_type_e e)
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

/// This used in functions
/// ast_assert_declared() for symbols, function calls and array access statements,
/// ast_asssert_not_declared() for all declarations.
static const char *ast_decl_or_expr_to_string(ast_node_t *ast)
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
        weak_unreachable("Expected variable or function AST");
    }
}

static void add_use(ast_node_t *ast, bool is_write)
{
    void (*usage_add_fun)(const char *) = is_write
        ? ast_storage_add_write_use
        : ast_storage_add_read_use;

    if (ast->type == AST_FUNCTION_CALL) {
        ast_function_call_t *stmt = ast->ast;
        usage_add_fun(stmt->name);
    }
    if (ast->type == AST_SYMBOL) {
        ast_symbol_t *sym = ast->ast;
        usage_add_fun(sym->value);
    }
    if (ast->type == AST_ARRAY_ACCESS) {
        ast_array_access_t *access = ast->ast;
        usage_add_fun(access->name);
    }
    if (ast->type == AST_MEMBER) {
        ast_member_t *member = ast->ast;
        if (member->structure->type == AST_SYMBOL) {
            ast_symbol_t *sym = member->structure->ast;
            usage_add_fun(sym->value);
        }
        /// Otherwise it can be unary statement like
        /// *(var).member.
    }
}

static void add_read_use(ast_node_t *ast)
{
    add_use(ast, /*is_write=*/false);
}

static void add_write_use(ast_node_t *ast)
{
    add_use(ast, /*is_write=*/true);
}

static void collected_uses_mark_top_scope_as_read()
{
    for (uint64_t i = 0; i < vector_back(collected_uses).count; ++i)
        add_read_use(vector_back(collected_uses).data[i]);
}

static void assert_is_declared(const char *name, ast_node_t *location)
{
    if (ast_storage_lookup(name)) return;
    weak_compile_error(
        location->line_no,
        location->col_no,
        "%s `%s` not found",
        ast_decl_or_expr_to_string(location), name
    );
}

static void assert_is_not_declared(const char *name, ast_node_t *location)
{
    ast_storage_decl_t *decl = ast_storage_lookup(name);

    if (!decl) return;
    weak_compile_error(
        location->line_no,
        location->col_no,
        "%s `%s` already declared at line %u, column %u",
        ast_decl_or_expr_to_string(location), name,
        decl->ast->line_no,
        decl->ast->col_no
    );
}

void make_unused_var_analysis()
{
    ast_storage_decl_array_t set = {0};
    ast_storage_current_scope_uses(&set);

    for (uint64_t i = 0; i < set.count; ++i) {
        ast_storage_decl_t *use = set.data[i];
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
}

void make_unused_var_and_func_analysis()
{
    ast_storage_decl_array_t set = {0};
    ast_storage_current_scope_uses(&set);

    for (uint64_t i = 0; i < set.count; ++i) {
        ast_storage_decl_t *use = set.data[i];
        bool is_func = use->ast->type == AST_FUNCTION_DECL;
        bool is_main_func = false;
        if (is_func) {
            ast_function_decl_t *decl = use->ast->ast;
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
}

static void visit_ast_node(ast_node_t *ast);

static void visit_ast_symbol(ast_node_t *ast)
{
    ast_symbol_t *sym = ast->ast;
    assert_is_declared(sym->value, ast);

    collect_ast(ast);
    /// We will decide if there is write use of this statement
    /// inside binary/unary operators logic.
}

static void visit_ast_var_decl(ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);
    ast_storage_push(decl->name, ast);
    if (decl->body)
        visit_ast_node(decl->body);
}

static void visit_ast_array_decl(ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);
    ast_storage_push(decl->name, ast);
}

static void visit_ast_binary(ast_node_t *ast)
{
    ast_binary_t *stmt = ast->ast;
    visit_ast_node(stmt->lhs);
    visit_ast_node(stmt->rhs);

    /// Only left hand side can be writable.
    if (is_assignment_op(stmt->operation))
        add_write_use(stmt->lhs);
    else
        add_read_use(stmt->lhs);
    add_read_use(stmt->rhs);
}

static void visit_ast_unary(ast_node_t *ast)
{
    ast_unary_t *stmt = ast->ast;
    ast_node_t *op = stmt->operand;
    bool is_var = false;
    is_var |= op->type == AST_SYMBOL; /// *var
    is_var |= op->type == AST_ARRAY_ACCESS; /// *var[0]
    is_var |= op->type == AST_MEMBER; /// *var.field
    is_var |= op->type == AST_PREFIX_UNARY; /// *(*var)
    if (!is_var)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Variable as argument of unary operator expected"
        );

    switch (stmt->operation) {
    case TOK_INC: /// ++var
    case TOK_DEC: /// --var
        add_write_use(op);
        break;
    case TOK_STAR: /// *var
    case TOK_BIT_AND: /// &var
        add_read_use(op);
        break;
    default:
        weak_unreachable("Wrong unary operator");
    }
    visit_ast_node(op);
}

/// \todo: What if (*mem_ptr)[0][1][2]?
static void visit_ast_array_access(ast_node_t *ast)
{
    ast_array_access_t *stmt = ast->ast;
    collect_ast(ast);
    assert(stmt->indices->type == AST_COMPOUND_STMT);
    visit_ast_node(stmt->indices->ast);
}

static void visit_ast_member(ast_node_t *ast)
{
    collect_ast(ast);
}

static void visit_ast_if(ast_node_t *ast)
{
    ast_if_t *stmt = ast->ast;
    visit_ast_node(stmt->condition);
    visit_ast_node(stmt->body);
    if (stmt->else_body)
        visit_ast_node(stmt->else_body);
}

static void visit_ast_for(ast_node_t *ast)
{
    ast_for_t *stmt = ast->ast;
    ast_storage_start_scope();
    if (stmt->init)
        visit_ast_node(stmt->init);
    if (stmt->condition) {
        collected_uses_start_scope();
        visit_ast_node(stmt->condition);
        collected_uses_mark_top_scope_as_read();
        collected_uses_end_scope();
    }
    if (stmt->increment)
        visit_ast_node(stmt->increment);
    visit_ast_node(stmt->body);
    ast_storage_end_scope();
}

static void visit_ast_while(ast_node_t *ast)
{
    ast_while_t *stmt = ast->ast;
    collected_uses_start_scope();
    visit_ast_node(stmt->condition);
    collected_uses_mark_top_scope_as_read();
    collected_uses_end_scope();
    visit_ast_node(stmt->body);
}

static void visit_ast_do_while(ast_node_t *ast)
{
    ast_do_while_t *stmt = ast->ast;
    collected_uses_start_scope();
    visit_ast_node(stmt->condition);
    collected_uses_mark_top_scope_as_read();
    collected_uses_end_scope();
    visit_ast_node(stmt->body);
}

static void visit_ast_return(ast_node_t *ast)
{
    ast_return_t *stmt = ast->ast;
    if (stmt->operand) {
        visit_ast_node(stmt->operand);
        add_read_use(stmt->operand);
    }
}

static void visit_ast_compound(ast_node_t *ast)
{
    ast_compound_t *stmt = ast->ast;
    ast_storage_start_scope();
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_ast_node(stmt->stmts[i]);
    make_unused_var_and_func_analysis();
    ast_storage_end_scope();
}

static void visit_ast_function_decl(ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    assert_is_not_declared(decl->name, ast);

    ast_storage_start_scope();
    /// This is to have function in recursive calls.
    ast_storage_push(decl->name, ast);
    /// Don't just visit compound AST, which creates and terminates scope.
    ast_compound_t *args = decl->args->ast;
    for (uint64_t i = 0; i < args->size; ++i)
        visit_ast_node(args->stmts[i]);
    visit_ast_node(decl->body);
    make_unused_var_analysis();
    ast_storage_end_scope();
    /// This is to have function outside.
    ast_storage_push(decl->name, ast);
}

static void visit_ast_function_call(ast_node_t *ast)
{
    ast_function_call_t *stmt = ast->ast;
    assert_is_declared(stmt->name, ast);
    add_read_use(ast);

    assert(stmt->args->type == AST_COMPOUND_STMT);
    ast_compound_t *args = stmt->args->ast;
    for (uint64_t i = 0; i < args->size; ++i) {
        visit_ast_node(args->stmts[i]);
        add_read_use(args->stmts[i]);
    }
}

void visit_ast_node(ast_node_t *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL: /// Unused.
    case AST_INTEGER_LITERAL: /// Unused.
    case AST_FLOATING_POINT_LITERAL: /// Unused.
    case AST_STRING_LITERAL: /// Unused.
    case AST_BOOLEAN_LITERAL: /// Unused.
    case AST_STRUCT_DECL: /// Unused.
    case AST_BREAK_STMT: /// Unused.
    case AST_CONTINUE_STMT: break; /// Unused.
    case AST_SYMBOL:
        visit_ast_symbol(ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(ast);
        break;
    case AST_BINARY:
        visit_ast_binary(ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(ast);
        break;
    case AST_MEMBER:
        visit_ast_member(ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(ast);
        break;
    default:
        weak_unreachable("Wrong AST type");
    }
}

void analysis_variable_use_analysis(ast_node_t *root)
{
    ast_storage_init_state();
    init_internal_state();
    visit_ast_node(root);
    reset_internal_state();
    ast_storage_reset_state();
}
