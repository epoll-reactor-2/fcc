/* ast.h - All AST statements.
 * Copyright (C) 2022-2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_H
#define WEAK_COMPILER_FRONTEND_AST_H

#include <stdbool.h>
#include <stdint.h>
#include "front_end/ast/ast_type.h"
#include "front_end/lex/data_type.h"
#include "front_end/lex/tok_type.h"


///////////////////////////////////////////////
///              AST Node                   ///
///////////////////////////////////////////////

/// Typed pointer to AST node of any type.
///
/// Each implemented AST node must have methods
/// - ast_%name%_init(...)
/// - ast_%name%_cleanup(...)
/// .
///
/// \note Cleanup methods for all AST's located in ast_cleanup.c
typedef struct ast_node_t {
    ast_type_e  type;
    void       *ast;
    uint16_t    line_no;
    uint16_t    col_no;
} ast_node_t;

/// Allocate AST node of given type.
ast_node_t *ast_node_init(ast_type_e type, void *ast, uint16_t line_no, uint16_t col_no);

/// Cleanup whole given AST tree through call
/// to proper functions for each node type.
///
/// \note Implemented in ast_cleanup.c file because for that
///       needed all AST header files.
void ast_node_cleanup(ast_node_t *ast);


///////////////////////////////////////////////
///              Array access               ///
///////////////////////////////////////////////
typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *indices;
} ast_array_access_t;

ast_node_t *ast_array_access_init(char *name, ast_node_t *indices, uint16_t line_no, uint16_t col_no);
void        ast_array_access_cleanup(ast_array_access_t *ast);


///////////////////////////////////////////////
///              Array declaration          ///
///////////////////////////////////////////////
typedef struct {
    /// Data type of array.
    data_type_e dt;

    /// Variable name.
    ///
    /// \note Must be dynamically allocated.
    char *name;

    /// Optional type name for arrays of structure type.
    ///
    /// \note If present, must be dynamically allocated.
    char *type_name;

    /// This stores information about array arity (dimension)
    /// and size for each dimension, e.g.,
    /// for array[1][2][3], ArityList equal to { 1, 2, 3 }.
    ast_node_t *arity_list;

    /// Depth of pointer, like for
    /// int ***ptr[2] indirection level = 3, for
    /// int *ptr[2] = 1, for
    /// int var[2] = 0.
    uint16_t indirection_lvl;
} ast_array_decl_t;

/// \note type_name may be NULL.
ast_node_t *ast_array_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    ast_node_t  *arity_list,
    uint16_t     indirection_lvl,
    uint16_t     line_no,
    uint16_t     col_no
);
void ast_array_decl_cleanup(ast_array_decl_t *ast);


///////////////////////////////////////////////
///              Binary expression          ///
///////////////////////////////////////////////
typedef struct {
    tok_type_e  operation;
    ast_node_t *lhs;
    ast_node_t *rhs;
} ast_binary_t;

ast_node_t *ast_binary_init(
    tok_type_e  operation,
    ast_node_t *lhs,
    ast_node_t *rhs,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_binary_cleanup(ast_binary_t *ast);


///////////////////////////////////////////////
///              Boolean                    ///
///////////////////////////////////////////////
typedef struct {
    bool value;
} ast_bool_t;

ast_node_t *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no);
void        ast_bool_cleanup(ast_bool_t *ast);


///////////////////////////////////////////////
///              Break statemen             ///
///////////////////////////////////////////////
typedef struct {
    /// Empty.
} ast_break_t;

ast_node_t *ast_break_init(uint16_t line_no, uint16_t col_no);
void        ast_break_cleanup(ast_break_t *ast);


///////////////////////////////////////////////
///              Character                  ///
///////////////////////////////////////////////
typedef struct {
    char value;
} ast_char_t;

ast_node_t *ast_char_init(char value, uint16_t line_no, uint16_t col_no);
void        ast_char_cleanup(ast_char_t *ast);


///////////////////////////////////////////////
///              Compound statement         ///
///////////////////////////////////////////////
typedef struct {
    uint64_t     size;
    ast_node_t **stmts;
} ast_compound_t;

ast_node_t *ast_compound_init(uint64_t size, ast_node_t **stmts, uint16_t line_no, uint16_t col_no);
void        ast_compound_cleanup(ast_compound_t *ast);


///////////////////////////////////////////////
///              Continue statement         ///
///////////////////////////////////////////////
typedef struct {
    /// Empty.
} ast_continue_t;

ast_node_t *ast_continue_init(uint16_t line_no, uint16_t col_no);
void        ast_continue_cleanup(ast_continue_t *ast);


///////////////////////////////////////////////
///              Do while                   ///
///////////////////////////////////////////////
typedef struct {
    ast_node_t *body;
    ast_node_t *condition;
} ast_do_while_t;

ast_node_t *ast_do_while_init(ast_node_t *body, ast_node_t *condition, uint16_t line_no, uint16_t col_no);
void        ast_do_while_cleanup(ast_do_while_t *ast);


///////////////////////////////////////////////
///         Floating point literal          ///
///////////////////////////////////////////////
typedef struct {
    float value;
} ast_float_t;

ast_node_t *ast_float_init(float value, uint16_t line_no, uint16_t col_no);
void        ast_float_cleanup(ast_float_t *ast);


///////////////////////////////////////////////
///              For statement              ///
///////////////////////////////////////////////
typedef struct {
    ast_node_t *init; /// \note May be NULL.
    ast_node_t *condition; /// \note May be NULL.
    ast_node_t *increment; /// \note May be NULL.
    ast_node_t *body;
} ast_for_t;

ast_node_t *ast_for_init(
    ast_node_t *init,
    ast_node_t *condition,
    ast_node_t *increment,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
);
void ast_for_cleanup(ast_for_t *ast);


///////////////////////////////////////////////
///              Function call              ///
///////////////////////////////////////////////
typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *args;
} ast_function_call_t;

ast_node_t *ast_function_call_init(
    char       *name,
    ast_node_t *args,
    uint16_t    line_no,
    uint16_t    col_no
);
void ast_function_call_cleanup(ast_function_call_t *ast);


///////////////////////////////////////////////
///              Function declaration       ///
///////////////////////////////////////////////
typedef struct {
    data_type_e  data_type;
    char        *name; /// \note Must be dynamically allocated.
    ast_node_t  *args;
    ast_node_t  *body; /// \note May be NULL. If so, this statement represents
                       ///       function prototype.
} ast_function_decl_t;

ast_node_t *ast_function_decl_init(
    data_type_e  data_type,
    char        *name,
    ast_node_t  *args,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
);
void ast_function_decl_cleanup(ast_function_decl_t *ast);


///////////////////////////////////////////////
///              If statement               ///
///////////////////////////////////////////////
typedef struct {
    ast_node_t *condition;
    ast_node_t *body;
    ast_node_t *else_body; /// \note May be NULL.
} ast_if_t;

ast_node_t *ast_if_init(
    ast_node_t *condition,
    ast_node_t *body,
    ast_node_t *else_body,
    uint16_t    line_no,
    uint16_t    col_no
);
void ast_if_cleanup(ast_if_t *ast);


///////////////////////////////////////////////
///              Structure access           ///
///////////////////////////////////////////////
typedef struct {
    /// This represents left side of member operator.
    /// May represent ast_symbol_t, ast_unary_t and so on.
    ast_node_t *structure;
    /// This represents right side of member operator.
    /// May represent ast_member_t and form nested operator.
    ast_node_t *member;
} ast_member_t;

ast_node_t *ast_member_init(
    ast_node_t *structure,
    ast_node_t *member,
    uint16_t    line_no,
    uint16_t    col_no
);
void ast_member_cleanup(ast_member_t *ast);


///////////////////////////////////////////////
///              Integral literal           ///
///////////////////////////////////////////////
typedef struct {
    int32_t value;
} ast_num_t;

ast_node_t *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no);
void        ast_num_cleanup(ast_num_t *ast);


///////////////////////////////////////////////
///              Return statement           ///
///////////////////////////////////////////////
typedef struct {
    ast_node_t *operand; /// \note May be NULL to represent return from void function.
} ast_return_t;

ast_node_t *ast_return_init(ast_node_t *operand, uint16_t line_no, uint16_t col_no);
void        ast_return_cleanup(ast_return_t *ast);


///////////////////////////////////////////////
///              String literal             ///
///////////////////////////////////////////////
typedef struct {
    char *value; /// \note Must be dynamically allocated.
} ast_string_t;

ast_node_t *ast_string_init(char *value, uint16_t line_no, uint16_t col_no);
void        ast_string_cleanup(ast_string_t *ast);


///////////////////////////////////////////////
///              Structure declaration      ///
///////////////////////////////////////////////
typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *decls;
} ast_struct_decl_t;

ast_node_t *ast_struct_decl_init(char *name, ast_node_t *decls, uint16_t line_no, uint16_t col_no);
void        ast_struct_decl_cleanup(ast_struct_decl_t *ast);


///////////////////////////////////////////////
///              Symbol                     ///
///////////////////////////////////////////////
typedef struct {
    char *value; /// \note Must be dynamically allocated.
} ast_symbol_t;

ast_node_t *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no);
void        ast_symbol_cleanup(ast_symbol_t *ast);


///////////////////////////////////////////////
///              Unary statement            ///
///////////////////////////////////////////////
typedef struct {
    ast_type_e  type; /// Prefix or postfix.
    tok_type_e  operation;
    ast_node_t *operand;
} ast_unary_t;

ast_node_t *ast_unary_init(
    ast_type_e  type,
    tok_type_e  operation,
    ast_node_t *operand,
    uint16_t    line_no,
    uint16_t    col_no
);
void ast_unary_cleanup(ast_unary_t *ast);


///////////////////////////////////////////////
///              Variable declaration       ///
///////////////////////////////////////////////
typedef struct {
    /// Data type of array.
    data_type_e dt;

    /// Variable name.
    ///
    /// \note Must be dynamically allocated.
    char *name;

    /// Optional type name for arrays of structure type.
    ///
    /// \note - If present, must be dynamically allocated.
    ///       - May be NULL. If so, this statement represents
    ///         primitive type declaration.
    char *type_name;

    /// Depth of pointer, like for
    /// int ***ptr indirection level = 3, for
    /// int *ptr = 1, for
    /// int var = 0.
    uint16_t indirection_lvl;

    /// Declaration body (expression after `=`).
    ///
    /// \note May be NULL. If so, this statement represents declarator
    ///       without initializer.
    ast_node_t *body;
} ast_var_decl_t;

/// \note type_name may be NULL.
ast_node_t *ast_var_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    uint16_t     indirection_lvl,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
);
void ast_var_decl_cleanup(ast_var_decl_t *ast);


///////////////////////////////////////////////
///              While statement            ///
///////////////////////////////////////////////
typedef struct {
    ast_node_t *condition;
    ast_node_t *body;
} ast_while_t;

ast_node_t *ast_while_init(ast_node_t *condition, ast_node_t *body, uint16_t line_no, uint16_t col_no);
void        ast_while_cleanup(ast_while_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_H