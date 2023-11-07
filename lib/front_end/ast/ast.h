/* ast.h - All AST statements.
 * Copyright (C) 2022-2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_H
#define WEAK_COMPILER_FRONTEND_AST_H

#include <stdbool.h>
#include <stdint.h>
#include "util/compiler.h"
#include "front_end/ast/ast_type.h"
#include "front_end/lex/data_type.h"
#include "front_end/lex/tok_type.h"


/**********************************************
 **              AST Node                   ***
 **********************************************/

/** Typed pointer to AST node of any type.
   
    Each implemented AST node must have methods
    - ast_%name%_init(...)
    - ast_%name%_cleanup(...)
    .
   
    \note Cleanup methods for all AST's located in ast_cleanup.c */
struct ast_node {
    enum ast_type  type;
    void          *ast;
    uint16_t       line_no;
    uint16_t       col_no;
};

/** Allocate AST node of given type. */
__weak_wur struct ast_node *ast_node_init(enum ast_type type, void *ast, uint16_t line_no, uint16_t col_no);

/** Cleanup whole given AST tree through call
    to proper functions for each node type.
   
    \note Implemented in ast_cleanup.c file because for that
          needed all AST header files. */
void ast_node_cleanup(struct ast_node *ast);


/**********************************************
 **              Array access               ***
 **********************************************/
struct ast_array_access {
    char            *name;    /** \note Must be dynamically allocated. */
    struct ast_node *indices; /** \note Must be of type ast_compound */
};

__weak_wur struct ast_node *ast_array_access_init(
    char            *name,
    struct ast_node *indices,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_array_access_cleanup(struct ast_array_access *ast);


/**********************************************
 **              Array declaration          ***
 **********************************************/
struct ast_array_decl {
    /** Data type of array. */
    enum data_type dt;

    /** Variable name.
       
        \note Must be dynamically allocated. */
    char *name;

    /** Optional type name for arrays of structure type.
       
        \note If present, must be dynamically allocated. */
    char *type_name;

    /** This stores information about array enclosure (dimension)
        and size for each dimension, e.g.,
        for array[1][2][3], EnclosureList equal to { 1, 2, 3 }.
       
        Represented as ast_compound of ast_num's. */
    struct ast_node *enclosure_list;

    /** Depth of pointer, like for
        int ***ptr[2] indirection level = 3, for
        int *ptr[2] = 1, for
        int var[2] = 0. */
    uint16_t indirection_lvl;

    /** Declaration body (expression after `=`).
       
        \note Must be initialized only if indirection_lvl >= 1.
              1) int  mem[1]; <- OK
              2) int *mem[1] = &other_mem[0];
                              <- OK
              3) int *mem[1]; <- Error: pointer declaration
                              <-        points to nothing. */
    struct ast_node *body;
};

/** \note type_name may be NULL. */
__weak_wur struct ast_node *ast_array_decl_init(
    enum data_type   dt,
    char            *name,
    char            *type_name,
    struct ast_node *enclosure_list,
    uint16_t         indirection_lvl,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_array_decl_cleanup(struct ast_array_decl *ast);


/**********************************************
 **              Binary expression          ***
 **********************************************/
struct ast_binary {
    enum token_type  operation;
    struct ast_node *lhs;
    struct ast_node *rhs;
};

__weak_wur struct ast_node *ast_binary_init(
    enum token_type  operation,
    struct ast_node *lhs,
    struct ast_node *rhs,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_binary_cleanup(struct ast_binary *ast);


/**********************************************
 **              Boolean                    ***
 **********************************************/
struct ast_bool {
    bool value;
};

__weak_wur
struct ast_node *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no);
void             ast_bool_cleanup(struct ast_bool *ast);


/**********************************************
 **              Break statement            ***
 **********************************************/
struct ast_break {
    /** Empty. */
};

__weak_wur
struct ast_node *ast_break_init(uint16_t line_no, uint16_t col_no);
void             ast_break_cleanup(struct ast_break *ast);


/**********************************************
 **              Character                  ***
 **********************************************/
struct ast_char {
    char value;
};

__weak_wur
struct ast_node *ast_char_init(char value, uint16_t line_no, uint16_t col_no);
void             ast_char_cleanup(struct ast_char *ast);


/**********************************************
 **              Compound statement         ***
 **********************************************/
struct ast_compound {
    uint64_t          size;
    struct ast_node **stmts;
};

__weak_wur struct ast_node *ast_compound_init(
    uint64_t          size,
    struct ast_node **stmts,
    uint16_t          line_no,
    uint16_t          col_no
);
void ast_compound_cleanup(struct ast_compound *ast);


/**********************************************
 **              Continue statement         ***
 **********************************************/
struct ast_continue {
    /** Empty. */
};

__weak_wur
struct ast_node *ast_continue_init(uint16_t line_no, uint16_t col_no);
void             ast_continue_cleanup(struct ast_continue *ast);


/**********************************************
 **              Do while                   ***
 **********************************************/
struct ast_do_while {
    struct ast_node *body;
    struct ast_node *condition;
};

__weak_wur struct ast_node *ast_do_while_init(
    struct ast_node *body,
    struct ast_node *condition,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_do_while_cleanup(struct ast_do_while *ast);


/**********************************************
 **          Floating point literal         ***
 **********************************************/
struct ast_float {
    float value;
};

__weak_wur
struct ast_node *ast_float_init(float value, uint16_t line_no, uint16_t col_no);
void             ast_float_cleanup(struct ast_float *ast);


/**********************************************
 **              For statement              ***
 **********************************************/
struct ast_for {
    struct ast_node *init;      /** \note May be NULL. */
    struct ast_node *condition; /** \note May be NULL. */
    struct ast_node *increment; /** \note May be NULL. */
    struct ast_node *body;
};

__weak_wur struct ast_node *ast_for_init(
    struct ast_node *init,
    struct ast_node *condition,
    struct ast_node *increment,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_for_cleanup(struct ast_for *ast);


/**********************************************
 **           Range for statement           ***
 **********************************************/
struct ast_for_range {
    struct ast_node *iter; /** Variable or array declarator. */
    struct ast_node *range_target; /** Expression. */
    struct ast_node *body;
};

__weak_wur struct ast_node *ast_for_range_init(
    struct ast_node *iter,
    struct ast_node *range_target,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_for_range_cleanup(struct ast_for_range *ast);


/**********************************************
 **              Function call              ***
 **********************************************/
struct ast_function_call {
    char            *name; /** \note Must be dynamically allocated. */
    struct ast_node *args;
};

__weak_wur struct ast_node *ast_function_call_init(
    char            *name,
    struct ast_node *args,
    uint16_t        line_no,
    uint16_t        col_no
);
void ast_function_call_cleanup(struct ast_function_call *ast);


/**********************************************
 **              Function declaration       ***
 **********************************************/
struct ast_function_decl {
    enum data_type   data_type;
    uint16_t         indirection_lvl;
    char            *name; /** \note Must be dynamically allocated. */
    struct ast_node *args;
    struct ast_node *body; /** \note May be NULL. If so, this statement represents
                                     function prototype. */
};

__weak_wur struct ast_node *ast_function_decl_init(
    enum data_type   data_type,
    uint16_t         indirection_lvl,
    char            *name,
    struct ast_node *args,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_function_decl_cleanup(struct ast_function_decl *ast);


/**********************************************
 **              If statement               ***
 **********************************************/
struct ast_if {
    struct ast_node *condition;
    struct ast_node *body;
    struct ast_node *else_body; /** \note May be NULL. */
};

__weak_wur struct ast_node *ast_if_init(
    struct ast_node *condition,
    struct ast_node *body,
    struct ast_node *else_body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_if_cleanup(struct ast_if *ast);


/**********************************************
 **              Structure access           ***
 **********************************************/
struct ast_member {
    /** This represents left side of member operator.
        May represent struct ast_symbol, struct ast_unary and so on. */
    struct ast_node *structure;
    /** This represents right side of member operator.
        May represent struct ast_member and form nested operator. */
    struct ast_node *member;
};

__weak_wur struct ast_node *ast_member_init(
    struct ast_node *structure,
    struct ast_node *member,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_member_cleanup(struct ast_member *ast);


/**********************************************
 **              Integral literal           ***
 **********************************************/
struct ast_num {
    int32_t value;
};

__weak_wur
struct ast_node *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no);
void             ast_num_cleanup(struct ast_num *ast);


/**********************************************
 **              Return statement           ***
 **********************************************/
struct ast_return {
    struct ast_node *operand; /** \note May be NULL to represent
                                        return from void function. */
};

__weak_wur
struct ast_node *ast_return_init(struct ast_node *operand, uint16_t line_no, uint16_t col_no);
void             ast_return_cleanup(struct ast_return *ast);


/**********************************************
 **              String literal             ***
 **********************************************/
struct ast_string {
    uint64_t  len;
    char     *value; /** \note Must be dynamically allocated. */
};

__weak_wur
struct ast_node *ast_string_init(
    uint64_t  len,
    char     *value,
    uint16_t  line_no,
    uint16_t col_no
);
void ast_string_cleanup(struct ast_string *ast);


/**********************************************
 **          Structure declaration          ***
 **********************************************/
struct ast_struct_decl {
    char            *name; /** \note Must be dynamically allocated. */
    struct ast_node *decls;
};

__weak_wur struct ast_node *ast_struct_decl_init(
    char            *name,
    struct ast_node *decls,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_struct_decl_cleanup(struct ast_struct_decl *ast);


/**********************************************
 **              Symbol                     ***
 **********************************************/
struct ast_symbol {
    char *value; /** \note Must be dynamically allocated. */
};

__weak_wur
struct ast_node *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no);
void             ast_symbol_cleanup(struct ast_symbol *ast);


/**********************************************
 **              Unary statement            ***
 **********************************************/
struct ast_unary {
    enum ast_type    type; /** Prefix or postfix. */
    enum token_type  operation;
    struct ast_node *operand;
};

__weak_wur struct ast_node *ast_unary_init(
    enum ast_type    type,
    enum token_type  operation,
    struct ast_node *operand,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_unary_cleanup(struct ast_unary *ast);


/**********************************************
 **              Variable declaration       ***
 **********************************************/
struct ast_var_decl {
    /** Data type of array. */
    enum data_type dt;

    /** Variable name.
       
        \note Must be dynamically allocated. */
    char *name;

    /** Optional type name for arrays of structure type.
       
        \note - If present, must be dynamically allocated.
              - May be NULL. If so, this statement represents
                primitive type declaration. */
    char *type_name;

    /** Depth of pointer, like for
        int ***ptr indirection level = 3, for
        int *ptr = 1, for
        int var = 0. */
    uint16_t indirection_lvl;

    /** Declaration body (expression after `=`).
       
        \note May be NULL. If so, this statement represents declarator
              without initializer. */
    struct ast_node *body;
};

/** \note type_name may be NULL. */
__weak_wur struct ast_node *ast_var_decl_init(
    enum data_type    dt,
    char             *name,
    char             *type_name,
    uint16_t          indirection_lvl,
    struct ast_node  *body,
    uint16_t          line_no,
    uint16_t          col_no
);
void ast_var_decl_cleanup(struct ast_var_decl *ast);


/**********************************************
 **              While statement            ***
 **********************************************/
struct ast_while {
    struct ast_node *condition;
    struct ast_node *body;
};

__weak_wur struct ast_node *ast_while_init(
    struct ast_node *condition,
    struct ast_node *body,
    uint16_t         line_no,
    uint16_t         col_no
);
void ast_while_cleanup(struct ast_while *ast);

/** Decrease abstraction level of AST.
   
    1. Replace range-based for loop with usual. */
void ast_lower(struct ast_node **ast);

#endif // WEAK_COMPILER_FRONTEND_AST_H