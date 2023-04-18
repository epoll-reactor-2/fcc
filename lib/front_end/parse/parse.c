/* parse.c - Syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/lex/data_type.h"
#include "front_end/parse/parse.h"
#include "utility/alloc.h"
#include "utility/diagnostic.h"
#include "utility/unreachable.h"
#include "utility/vector.h"
#include <assert.h>
#include <string.h>

typedef vector_t(ast_node_t *) ast_array_t;

static data_type_e tok_to_data_type(tok_type_e t)
{
    switch (t) {
    case TOK_VOID:   return D_T_VOID;
    case TOK_INT:    return D_T_INT;
    case TOK_FLOAT:  return D_T_FLOAT;
    case TOK_CHAR:   return D_T_CHAR;
    case TOK_BOOL:   return D_T_BOOL;
    case TOK_SYMBOL: return D_T_STRUCT;
    default:         weak_unreachable("Cannot convert token to data type");
    }
}

static const tok_t *tok_begin;
static const tok_t *tok_end;

static uint32_t loops_depth = 0;

static const tok_t *peek_current()
{
    return tok_begin;
}

static const tok_t *peek_next()
{
    return tok_begin++;
}

const tok_t *require_token(tok_type_e t)
{
    const tok_t *curr_tok = peek_current();

    if (curr_tok->type != t)
        weak_compile_error(
            curr_tok->line_no,
            curr_tok->col_no,
            "Expected `%s`, got `%s`",
            tok_to_string(t), tok_to_string(curr_tok->type)
        );

    ++tok_begin;
    return curr_tok;
}

const tok_t *require_char(char c)
{
    return require_token(tok_char_to_tok(c));
}

static ast_node_t *parse_decl();
static ast_node_t *parse_struct_decl();
static ast_node_t *parse_function_decl();
static ast_node_t *parse_stmt();
static ast_node_t *parse_selection_stmt();
static ast_node_t *parse_iteration_stmt();
static ast_node_t *parse_jump_stmt();
static ast_node_t *parse_for();
static ast_node_t *parse_do_while();
static ast_node_t *parse_while();
static ast_node_t *parse_block();
static ast_node_t *parse_iteration_block();
static ast_node_t *parse_constant();
static ast_node_t *parse_logical_or();
static ast_node_t *parse_logical_and();
static ast_node_t *parse_inclusive_or();
static ast_node_t *parse_exclusive_or();
static ast_node_t *parse_and();
static ast_node_t *parse_equality();
static ast_node_t *parse_relational();
static ast_node_t *parse_shift();
static ast_node_t *parse_additive();
static ast_node_t *parse_multiplicative();
static ast_node_t *parse_prefix_unary();
static ast_node_t *parse_postfix_unary();
static ast_node_t *parse_symbol();
static ast_node_t *parse_primary();
static ast_node_t *parse_decl_without_initializer();
static ast_node_t *parse_var_decl_without_initializer();
static ast_node_t *parse_struct_var_decl();
static ast_node_t *parse_struct_field_access();
static ast_node_t *parse_array_access();
static ast_node_t *parse_expr();
static ast_node_t *parse_assignment();
static ast_node_t *parse_function_call();

ast_node_t *parse(const tok_t *begin, const tok_t *end)
{
    tok_begin = (tok_t *)begin;
    tok_end = (tok_t *)end;

    typedef vector_t(ast_node_t *) stmts_t;

    stmts_t global_stmts = {0};
    const tok_t *curr_tok = NULL;

    while (tok_begin < tok_end) {
        curr_tok = peek_current();
        switch (curr_tok->type) {
        case TOK_STRUCT:
            vector_push_back(global_stmts, parse_struct_decl());
            break;
        case TOK_VOID:
        case TOK_INT:
        case TOK_CHAR:
        case TOK_FLOAT:
        case TOK_BOOL: /// Fall through.
            vector_push_back(global_stmts, parse_function_decl());
            break;
        default:
            weak_compile_error(
                curr_tok->line_no,
                curr_tok->col_no,
                "Unexpected token in global context: %s\n",
                tok_to_string(curr_tok->type)
            );
        }
    }

    return ast_compound_init(
        /*size=*/global_stmts.count,
        /*stmts=*/global_stmts.data,
        /*line_no=*/0,
        /*col_no=*/0
    );
}

typedef struct {
    data_type_e  data_type;
    char        *type_name;
    uint16_t     indirection_lvl;
    uint16_t     line_no;
    int16_t      col_no;
} localized_data_type_t;

static localized_data_type_t parse_type()
{
    const tok_t *curr_tok = peek_next();

    switch (curr_tok->type) {
    case TOK_INT:
    case TOK_FLOAT:
    case TOK_CHAR:
    case TOK_BOOL:
    case TOK_SYMBOL: { /// Fall through.
        unsigned indirection_lvl = 0;
        while (tok_is(peek_current(), '*')) {
            ++indirection_lvl;
            peek_next(); /// Don't needed to require '*'.
        }
        localized_data_type_t l = {
            .data_type = tok_to_data_type(curr_tok->type),
            .type_name = (curr_tok->type == TOK_SYMBOL) ? strdup(curr_tok->data) : NULL,
            .indirection_lvl = indirection_lvl,
            .line_no = curr_tok->line_no,
            .col_no = curr_tok->col_no
        };
        return l;
    }
    default:
        weak_compile_error(
            curr_tok->line_no,
            curr_tok->col_no,
            "Data type expected, got %s",
            tok_to_string(curr_tok->type)
        );
    }
}

static localized_data_type_t parse_return_type()
{
    const tok_t *curr_tok = peek_current();

    if (curr_tok->type != TOK_VOID)
        return parse_type();

    peek_next();

    localized_data_type_t l = {
        .data_type = tok_to_data_type(curr_tok->type),
        .indirection_lvl = 0,
        .line_no = curr_tok->line_no,
        .col_no = curr_tok->col_no
    };
    return l;
}

static ast_node_t *parse_array_decl()
{
    localized_data_type_t dt = parse_type();
    const tok_t *var_name = peek_next();

    if (var_name->type != TOK_SYMBOL)
        weak_compile_error(
            var_name->line_no,
            var_name->col_no,
            "Variable name expected"
        );

    ast_array_t arity_list = {0};

    if (!tok_is(peek_current(), '['))
        weak_compile_error(
            peek_current()->line_no,
            peek_current()->col_no,
            "`[` expected"
        );

    while (tok_is(peek_current(), '[')) {
        require_char('[');
        ast_node_t *constant = parse_constant();
        if (constant->type != AST_INTEGER_LITERAL)
            weak_compile_error(
                constant->line_no,
                constant->col_no,
                "Integer size declarator expected"
            );

        vector_push_back(arity_list, constant);
        require_char(']');
    }

    ast_node_t *arity_list_compound = ast_compound_init(
        arity_list.count,
        arity_list.data,
        dt.line_no,
        dt.col_no
    );

    return ast_array_decl_init(
        dt.data_type,
        strdup(var_name->data),
        dt.type_name,
        arity_list_compound,
        dt.indirection_lvl,
        dt.line_no,
        dt.col_no
    );
}

static ast_node_t *parse_decl_without_initializer()
{
    const tok_t *ptr = peek_current();
    localized_data_type_t dt = parse_type();
    bool is_array = tok_is((tok_begin + 1), '[');
    ptrdiff_t offset = tok_begin - ptr;
    tok_begin -= offset;

    /// We just compute the offset of whole type
    /// declaration, e.g for `char ********` to judge
    /// what type of declaration there is. All other
    /// allocated strings are not needed.
    if (dt.type_name)
        weak_free(dt.type_name);

    switch (ptr->type) {
    case TOK_SYMBOL:
    case TOK_VOID:
    case TOK_INT:
    case TOK_FLOAT:
    case TOK_CHAR:
    case TOK_BOOL: /// Fall through.
        if (is_array)
            return parse_array_decl();
        else
            return parse_var_decl_without_initializer();
    default:
      weak_unreachable("Data type expected");
    }
}

static ast_node_t *parse_var_decl_without_initializer()
{
    localized_data_type_t dt = parse_type();
    const tok_t *var_name = require_token(TOK_SYMBOL);

    return ast_var_decl_init(
        dt.data_type,
        strdup(var_name->data),
        dt.type_name, /// Already strdup()'ed.
        dt.indirection_lvl,
        /*body=*/NULL,
        dt.line_no,
        dt.col_no
    );
}

static ast_node_t *parse_var_decl()
{
    localized_data_type_t dt = parse_type();
    const tok_t *var_name = peek_next();

    if (var_name->type != TOK_SYMBOL)
        weak_compile_error(
            var_name->line_no,
            var_name->col_no,
            "Variable name expected"
        );

    const tok_t *operator = peek_next();

    if (tok_is(operator, '='))
        return ast_var_decl_init(
            dt.data_type,
            strdup(var_name->data),
            dt.type_name,
            dt.indirection_lvl,
            parse_logical_or(),
            dt.line_no,
            dt.col_no
        );

    /// This is placed here because language supports nested functions.
    if (tok_is(operator, '(')) {
        --tok_begin; /// Open paren.
        --tok_begin; /// Function name.
        --tok_begin; /// Data type.
        tok_begin -= dt.indirection_lvl;
        return parse_function_decl();
    }

    if (tok_is(operator, '[')) {
        --tok_begin; /// Open paren.
        --tok_begin; /// Function name.
        --tok_begin; /// Data type.
        tok_begin -= dt.indirection_lvl;
        return parse_array_decl();
    }

    weak_compile_error(
        var_name->line_no,
        var_name->col_no,
        "Function, variable or array declaration expected"
    );
}

static ast_node_t *parse_decl()
{
    const tok_t *t = peek_current();

    switch (t->type) {
    case TOK_STRUCT:
        return parse_struct_decl();
    case TOK_SYMBOL:
        return parse_struct_var_decl();
    case TOK_VOID:
    case TOK_INT:
    case TOK_CHAR:
    case TOK_FLOAT:
    case TOK_BOOL: /// Fall through.
        return parse_decl_without_initializer();
    default:
        weak_compile_error(
            t->line_no,
            t->col_no,
            "Declaration expected"
        );
    }
}

static ast_node_t *parse_struct_decl()
{
    ast_array_t decls = {0};

    const tok_t *start = require_token(TOK_STRUCT);
    const tok_t *name = require_token(TOK_SYMBOL);

    require_char('{');

    while (!tok_is(peek_current(), '}')) {
        vector_push_back(decls, parse_decl());
        require_char(';');
    }

    require_char('}');

    ast_node_t *decls_list = ast_compound_init(
        decls.count,
        decls.data,
        start->line_no,
        start->col_no
    );

    return ast_struct_decl_init(
        strdup(name->data),
        decls_list,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_function_param_list()
{
    ast_array_t list = {0};

    if (tok_is(peek_current(), ')'))
        return ast_compound_init(
            0,
            NULL,
            peek_current()->line_no,
            peek_current()->col_no
        );

    while (!tok_is(peek_current(), ')')) {
        vector_push_back(list, parse_decl_without_initializer());
        if (tok_is(peek_current(), ','))
            require_char(',');
    }

    return ast_compound_init(
        list.count,
        list.data,
        peek_current()->line_no,
        peek_current()->col_no
    );
}

static ast_node_t *parse_function_decl()
{
    localized_data_type_t dt = parse_return_type();
    const tok_t *name = require_token(TOK_SYMBOL);

    require_char('(');
    ast_node_t *param_list = parse_function_param_list();
    require_char(')');

    ast_node_t *block = NULL;

    if (tok_is(peek_current(), '{'))
        block = parse_block(); /// Function.
    else
        require_char(';'); /// Prototype.

    return ast_function_decl_init(
        dt.data_type,
        strdup(name->data),
        param_list,
        block ? block : NULL,
        dt.line_no,
        dt.col_no
    );
}

static ast_node_t *parse_stmt()
{
    const tok_t *t = peek_current();

    switch (t->type) {
    case TOK_OPEN_CURLY_BRACKET:
        return parse_block();
    case TOK_IF:
        return parse_selection_stmt();
    case TOK_FOR:
    case TOK_DO:
    case TOK_WHILE: /// Fall through.
        return parse_iteration_stmt();
    case TOK_RETURN:
        return parse_jump_stmt();
    case TOK_INT:
    case TOK_CHAR:
    case TOK_FLOAT:
    case TOK_BOOL: /// Fall through.
        return parse_var_decl();
    case TOK_SYMBOL: {
        /// Expression like `a *b` means structure
        /// variable declaration only in global context
        /// (most top level in block), elsewise this is
        /// a multiplication operator.
        return (tok_is(tok_begin + 1, '*') || (tok_begin + 1)->type == TOK_SYMBOL)
            ? parse_struct_var_decl()
            : parse_expr();
    }
    case TOK_BIT_AND: /// Address operator `&`.
    case TOK_STAR: /// Dereference operator `*`.
    case TOK_INC:
    case TOK_DEC: /// Fall through.
        return parse_assignment();
    case TOK_OPEN_PAREN:
        return parse_primary();
    default:
        weak_compile_error(
            t->line_no,
            t->col_no,
            "Unexpected token %s\n",
            tok_to_string(t->type)
        );
    }
}

static ast_node_t *parse_loop_stmt()
{
    const tok_t *t = peek_next();

    switch (t->type) {
    case TOK_BREAK:
        return ast_break_init(t->line_no, t->col_no);
    case TOK_CONTINUE:
        return ast_continue_init(t->line_no, t->col_no);
    default:
        --tok_begin;
        return parse_stmt();
    }
}

static ast_node_t *parse_iteration_block()
{
    ast_array_t stmts = {0};
    const tok_t *start = require_char('{');

    while (!tok_is(peek_current(), '}')) {
        vector_push_back(stmts, parse_loop_stmt());
        ast_type_e t = vector_at(stmts, stmts.count - 1)->type;

        switch (t) {
        case AST_BINARY:
        case AST_POSTFIX_UNARY:
        case AST_PREFIX_UNARY:
        case AST_SYMBOL:
        case AST_RETURN_STMT:
        case AST_DO_WHILE_STMT:
        case AST_VAR_DECL:
        case AST_ARRAY_DECL:
        case AST_ARRAY_ACCESS:
        case AST_MEMBER:
        case AST_FUNCTION_CALL:
        case AST_BREAK_STMT:
        case AST_CONTINUE_STMT: /// Fall through.
            require_char(';');
            break;
        default:
            break;
        }
    }

    require_char('}');

    return ast_compound_init(
        stmts.count,
        stmts.data,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_block()
{
    if (loops_depth > 0)
        return parse_iteration_block();

    ast_array_t stmts = {0};
    const tok_t *start = require_char('{');

    while (!tok_is(peek_current(), '}')) {
        vector_push_back(stmts, parse_stmt());
        ast_type_e t = vector_at(stmts, stmts.count - 1)->type;

        switch (t) {
        case AST_BINARY:
        case AST_POSTFIX_UNARY:
        case AST_PREFIX_UNARY:
        case AST_SYMBOL:
        case AST_RETURN_STMT:
        case AST_DO_WHILE_STMT:
        case AST_VAR_DECL:
        case AST_ARRAY_DECL:
        case AST_ARRAY_ACCESS:
        case AST_MEMBER:
        case AST_FUNCTION_CALL: /// Fall through.
            require_char(';');
            break;
        default:
            break;
        }
    }

    require_char('}');

    return ast_compound_init(
        stmts.count,
        stmts.data,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_selection_stmt()
{
    ast_node_t *cond = NULL;
    ast_node_t *then_body = NULL;
    ast_node_t *else_body = NULL;
    const tok_t *start = require_token(TOK_IF);

    require_char('(');
    cond = parse_logical_or();
    require_char(')');

    then_body = parse_block();

    if (peek_current()->type == TOK_ELSE) {
        peek_next();
        else_body = parse_block();
    }

    return ast_if_init(
        cond,
        then_body,
        else_body,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_iteration_stmt()
{
    const tok_t *t = peek_current();

    switch (t->type) {
    case TOK_FOR:
        return parse_for();
    case TOK_DO:
        return parse_do_while();
    case TOK_WHILE:
        return parse_while();
    default:
        weak_unreachable("Loop types are checked in function above");
    }
}

static ast_node_t *parse_jump_stmt()
{
    const tok_t *start = require_token(TOK_RETURN);
    ast_node_t *body = NULL;

    if (!tok_is(peek_current(), ';'))
        body = parse_logical_or();

    return ast_return_init(body, start->line_no, start->col_no);
}

static ast_node_t *parse_for()
{
    const tok_t *start = require_token(TOK_FOR);
    require_char('(');

    ast_node_t *init = NULL;
    ast_node_t *cond = NULL;
    ast_node_t *increment = NULL;

    if (!tok_is(peek_next(), ';')) {
        --tok_begin;
        init = parse_expr();
        require_char(';');
    }

    if (!tok_is(peek_next(), ';')) {
        --tok_begin;
        cond = parse_expr();
        require_char(';');
    }

    if (!tok_is(peek_next(), ')')) {
        --tok_begin;
        increment = parse_expr();
        require_char(')');
    }

    ++loops_depth;
    ast_node_t *body = parse_block();
    --loops_depth;

    return ast_for_init(
        init,
        cond,
        increment,
        body,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_do_while()
{
    const tok_t *start = require_token(TOK_DO);

    ++loops_depth;
    ast_node_t *body = parse_block();
    --loops_depth;

    require_token(TOK_WHILE);

    require_char('(');
    ast_node_t *cond = parse_logical_or();
    require_char(')');

    return ast_do_while_init(
        body,
        cond,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_while()
{
    const tok_t *start = require_token(TOK_WHILE);

    require_char('(');
    ast_node_t *cond = parse_logical_or();
    require_char(')');

    ++loops_depth;
    ast_node_t *body = parse_block();
    --loops_depth;

    return ast_while_init(
        cond,
        body,
        start->line_no,
        start->col_no
    );
}

static ast_node_t *parse_logical_or()
{
    ast_node_t *expr = parse_logical_and();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_OR:
            expr = ast_binary_init(t->type, expr, parse_logical_or(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_logical_and()
{
    ast_node_t *expr = parse_inclusive_or();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_AND:
            expr = ast_binary_init(t->type, expr, parse_logical_and(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_inclusive_or()
{
    ast_node_t *expr = parse_exclusive_or();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_BIT_OR:
            expr = ast_binary_init(t->type, expr, parse_inclusive_or(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_exclusive_or()
{
    ast_node_t *expr = parse_and();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_XOR:
            expr = ast_binary_init(t->type, expr, parse_exclusive_or(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_and()
{
    ast_node_t *expr = parse_equality();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_BIT_AND:
            expr = ast_binary_init(t->type, expr, parse_and(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_equality()
{
    ast_node_t *expr = parse_relational();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_EQ:
        case TOK_NEQ: /// Fall through.
            expr = ast_binary_init(t->type, expr, parse_equality(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_relational()
{
    ast_node_t *expr = parse_shift();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_GT:
        case TOK_LT:
        case TOK_GE:
        case TOK_LE: /// Fall through.
            expr = ast_binary_init(t->type, expr, parse_relational(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_shift()
{
    ast_node_t *expr = parse_additive();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_SHL:
        case TOK_SHR: /// Fall through.
            expr = ast_binary_init(t->type, expr, parse_shift(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_additive()
{
    ast_node_t *expr = parse_multiplicative();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_PLUS:
        case TOK_MINUS: /// Fall through.
            expr = ast_binary_init(t->type, expr, parse_additive(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_multiplicative()
{
    ast_node_t *expr = parse_prefix_unary();

    while (true) {
        const tok_t *t = peek_next();
        switch (t->type) {
        case TOK_STAR:
        case TOK_SLASH:
        case TOK_MOD: /// Fall through.
            expr = ast_binary_init(t->type, expr, parse_multiplicative(), t->line_no, t->col_no);
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }
    return expr;
}

static ast_node_t *parse_prefix_unary()
{
   const tok_t *t = peek_next();

    switch (t->type) {
    case TOK_BIT_AND: /// Address operator `&`.
    case TOK_STAR: /// Dereference operator `*`.
    case TOK_INC:
    case TOK_DEC: /// Fall through.
        return ast_unary_init(
            AST_PREFIX_UNARY,
            t->type,
            parse_prefix_unary(),
            t->line_no,
            t->col_no
        );
    default:
        /// Rollback current token pointer because there's no unary operator.
        --tok_begin;
        return parse_postfix_unary();
    }
}

static ast_node_t *parse_postfix_unary()
{
    ast_node_t *expr = parse_primary();
    const tok_t *t = peek_next();

    switch (t->type) {
    case TOK_INC:
    case TOK_DEC: /// Fall through.
        return ast_unary_init(
            AST_POSTFIX_UNARY,
            t->type,
            expr,
            t->line_no,
            t->col_no
        );
    default:
      --tok_begin;
      return expr;
    }
}

static ast_node_t *parse_symbol()
{
    const tok_t *start = tok_begin - 1;
    const tok_t *curr_tok = tok_begin;

    switch (curr_tok->type) {
    /// symbol(
    case TOK_OPEN_PAREN:
        --tok_begin;
        return parse_function_call();
    /// symbol[
    case TOK_OPEN_BOX_BRACKET:
        --tok_begin;
        return parse_array_access();
    /// symbol.
    case TOK_DOT:
        --tok_begin;
        return parse_struct_field_access();
    /// symbol
    default:
        return ast_symbol_init(strdup(start->data), start->line_no, start->col_no);
    }
}

static ast_node_t *parse_primary()
{
    const tok_t *t = peek_next();

    switch (t->type) {
    case TOK_SYMBOL:
        return parse_symbol();
    case TOK_OPEN_PAREN: {
        ast_node_t *expr = parse_logical_or();
        require_char(')');
        if (tok_is(peek_current(), '.')) {
            peek_next();
            expr = ast_member_init(
                expr,
                parse_struct_field_access(),
                expr->line_no,
                expr->col_no
            );
        }
        return expr;
    }
    default:
        --tok_begin;
        return parse_constant();
    }
}

static ast_node_t *parse_struct_var_decl()
{
    localized_data_type_t dt = parse_type();
    const tok_t *name = require_token(TOK_SYMBOL);

    assert(dt.data_type == D_T_STRUCT);
    ast_array_t arity_list = {0};

    while (tok_is(peek_current(), '[')) {
        require_char('[');
        /// \todo: Just peek number.
        ast_node_t *constant = parse_constant();

        if (constant->type != AST_INTEGER_LITERAL)
            weak_compile_error(
                constant->line_no,
                constant->col_no,
                "Integer size declarator expected"
            );

        vector_push_back(arity_list, constant->ast);
        require_char(']');
    }

    if (arity_list.count > 0) {
        ast_node_t *arity_list_ast = ast_compound_init(
            arity_list.count,
            arity_list.data,
            dt.line_no,
            dt.col_no
        );
        return ast_array_decl_init(
            D_T_STRUCT,
            strdup(name->data),
            dt.type_name, /// Already strdup()'ed.
            arity_list_ast,
            dt.indirection_lvl,
            dt.line_no,
            dt.col_no
        );
    }

    return ast_var_decl_init(
        D_T_STRUCT,
        strdup(name->data),
        dt.type_name, /// Already strdup()'ed.
        dt.indirection_lvl,
        /*body=*/NULL,
        dt.line_no,
        dt.col_no
    );
}

static ast_node_t *parse_struct_field_access()
{
    const tok_t *symbol = require_token(TOK_SYMBOL);
    const tok_t *next = peek_next();

    if (tok_is(next, '.'))
        return ast_member_init(
            ast_symbol_init(strdup(symbol->data), symbol->line_no, symbol->col_no),
            parse_struct_field_access(),
            symbol->line_no,
            symbol->col_no
        );

    --tok_begin;
    return ast_symbol_init(strdup(symbol->data), symbol->line_no, symbol->col_no);
}

static ast_node_t *parse_array_access()
{
    const tok_t *symbol = peek_next();

    if (!tok_is(peek_current(), '['))
        weak_compile_error(
            symbol->line_no,
            symbol->col_no,
            "`[` expected"
        );

    ast_array_t access_list = {0};

    while (tok_is(peek_current(), '[')) {
        require_char('[');
        vector_push_back(access_list, parse_expr());
        require_char(']');
    }

    ast_node_t *args = ast_compound_init(
        access_list.count,
        access_list.data,
        symbol->line_no,
        symbol->col_no
    );

    return ast_array_access_init(
        strdup(symbol->data),
        args,
        symbol->line_no,
        symbol->col_no
    );
}

static ast_node_t *parse_expr()
{
    const tok_t *t = peek_current();

    switch (t->type) {
    case TOK_INT:
    case TOK_CHAR:
    case TOK_FLOAT:
    case TOK_BOOL: /// Fall through.
      return parse_var_decl();
    default:
      return parse_assignment();
    }
}

static ast_node_t *parse_assignment()
{
    ast_node_t *expr = parse_logical_or();

    while (true) {
        const tok_t *t = peek_next();

        switch (t->type) {
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
        case TOK_XOR_ASSIGN: /// Fall through.
            expr = ast_binary_init(
                t->type,
                expr,
                parse_assignment(),
                t->line_no,
                t->col_no
            );
            continue;
        default:
            --tok_begin;
            break;
        }
        break;
    }

    return expr;
}

static ast_node_t *parse_function_call()
{
    const tok_t *name = peek_next();

    ast_array_t args_list = {0};

    require_char('(');

    if (tok_is(peek_next(), ')'))
        return ast_function_call_init(
            strdup(name->data),
            ast_compound_init(
                0,
                NULL,
                name->line_no,
                name->col_no
            ),
            name->line_no,
            name->col_no
        );

    --tok_begin;
    while (!tok_is(peek_current(), ')')) {
        vector_push_back(args_list, parse_logical_or());
        if (tok_is(peek_current(), ','))
            require_char(',');
    }

    require_char(')');

    ast_node_t *args = ast_compound_init(
        args_list.count,
        args_list.data,
        name->line_no,
        name->col_no
    );

    return ast_function_call_init(
        strdup(name->data),
        args,
        name->line_no,
        name->col_no
    );
}

static ast_node_t *parse_constant()
{
    const tok_t *t = peek_next();

    switch (t->type) {
    case TOK_INTEGRAL_LITERAL:
        return ast_num_init(atoi(t->data), t->line_no, t->col_no);
    case TOK_FLOATING_POINT_LITERAL:
        return ast_float_init(atof(t->data), t->line_no, t->col_no);
    case TOK_STRING_LITERAL:
        return ast_string_init(t->data, t->line_no, t->col_no);
    case TOK_CHAR_LITERAL:
        return ast_char_init(t->data[0], t->line_no, t->col_no);
    case TOK_TRUE:
    case TOK_FALSE:
        return ast_bool_init(strcmp(t->data, "true") == 0, t->line_no, t->col_no);
    default:
        weak_compile_error(
            t->line_no,
            t->col_no,
            "Literal expected, got ",
            tok_to_string(t->type)
        );
    }
}