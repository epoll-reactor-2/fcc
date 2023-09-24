/* ir.h - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_H
#define WEAK_COMPILER_MIDDLE_END_IR_H

#include "front_end/lex/data_type.h"
#include "front_end/lex/tok_type.h"
#include "util/compiler.h"
#include <stdbool.h>
#include <stdint.h>

enum ir_type {
    IR_ALLOCA,
    IR_ALLOCA_ARRAY,
    /// Immediate value.
    IR_IMM,
    IR_SYM,
    IR_STORE,
    IR_BIN,
    IR_JUMP,
    IR_COND,
    IR_RET,
    /// This used in ret instruction to represent
    /// `return;` from void functions.
    IR_RET_VOID,
    IR_MEMBER,
    /// Code generator should store type declarations
    /// and refer to it in order to compute type
    /// size and member offsets.
    IR_TYPE_DECL,
    IR_FUNC_DECL,
    IR_FUNC_CALL,
};

/// This IR node designed to be able to represent
/// Control Flow Graph (CFG). Each concrete IR node has
/// pointer to the next statement in execution flow,
/// if such needed.
///
/// Each implemented IR node must have methods
/// - ir_%name%_init(...)
/// - ir_%name%_cleanup(...)
/// .
struct ir_node {
    enum ir_type     type;
    int32_t          instr_idx;
    void            *ir;
    /// Immediate dominator. Used to compute dominator tree.
    struct ir_node  *idom;

    struct ir_node  *next;
    struct ir_node  *next_else;

    struct ir_node  *prev;
    struct ir_node  *prev_else;

    /// Meta information. Used for analysis
    /// and optimizations.
    ///
    /// If NULL, there is no metadata for given
    /// node.
    void            *meta;
};

struct ir_alloca {
    enum data_type   dt;
    bool             ptr;
    /// This is index of an variable. Like
    /// D_T_INT %1.
    /// Alternatively, string names can be stored.
    int32_t          idx;
};

struct ir_alloca_array {
    enum data_type   dt;
    /// Possible multiple dimensions.
    uint64_t         enclosure_lvls[16];
    uint64_t         enclosure_lvls_size;
    int32_t          idx;
};

enum ir_imm_type {
    IMM_BOOL,
    IMM_CHAR,
    IMM_FLOAT,
    IMM_INT
};

union ir_imm_val {
    bool    __bool;
    char    __char;
    float   __float;
    int32_t __int;
};

struct ir_imm {
    enum ir_imm_type type;
    /// Immediate value. Used as argument of
    /// store or binary instructions.
    union ir_imm_val imm;
};

struct ir_sym {
    /// Are we dereferencing pointer or not?
    /// Like *ptr.
    bool    deref;
    int32_t idx;
};

struct ir_store {
    /// Accepted types:
    /// - ir_sym
    struct ir_node *idx;
    /// Accepted types:
    /// - ir_imm
    /// - ir_sym
    /// - ir_bin
    struct ir_node *body;
};

struct ir_bin {
    /// Allowed body for binary instruction:
    /// - var op var
    /// - var op imm
    /// - imm op var
    /// - imm op imm
    ///
    /// \note: There is no unary operators.
    ///        They can be expressed through binary ones.
    enum token_type  op;
    struct ir_node  *lhs;
    struct ir_node  *rhs;
};

struct ir_jump {
    /// Unconditonal jump.
    int32_t          idx;
};

struct ir_cond {
    /// Condition. Requires binary operator as
    /// operand. In case of expressions like
    ///   if (x)
    /// it should looks like
    ///   if cmpneq x, 0.
    /// Requires only binary IR instruction.
    struct ir_node  *cond;
    int32_t          goto_label;
};

struct ir_ret {
    /// Requires IR_RET or IR_RET_VOID. In case
    /// of the last one, op is NULL.
    bool is_void;
    /// Accepted values:
    /// - symbol (variable index),
    /// - immediate value.
    struct ir_node *body;
};

struct ir_member {
    /// This looks like
    /// struct x {
    ///     int a;
    ///     int b;
    /// }
    ///
    /// %1 = allocation of x
    /// %1.0 = x.a
    /// %1.1 = x.b
    int32_t idx;
    int32_t field_idx;
};

struct ir_type_decl {
    const char *name;
    /// Accepted values:
    /// - struct ir_alloca (primitive type),
    /// - struct ir_type_decl_t (compound type, nested).
    struct ir_node *decls;
};

struct ir_func_decl {
    enum data_type   ret_type;
    /// Name instead of index required though
    /// (to be able to view something at all in assembly file).
    const char      *name;
    /// Accepted values:
    /// - struct ir_alloca (primitive type),
    /// - struct ir_type_decl_t (compound type, nested).
    struct ir_node  *args;
    struct ir_node  *body;
};

struct ir_func_call {
    const char      *name;
    /// Accepted values:
    /// - struct ir_sym,
    /// - struct ir_imm.
    /// Correct argument types is code generator responsibility.
    struct ir_node  *args;
};

void ir_reset_internal_state();

__weak_wur struct ir_node *ir_node_init(enum ir_type type, void *ir);
__weak_wur struct ir_node *ir_alloca_init(enum data_type dt, bool ptr, int32_t idx);
__weak_wur struct ir_node *ir_alloca_array_init(
    enum data_type  dt,
    uint64_t       *enclosure_lvls,
    uint64_t        enclosure_lvls_size,
    int32_t         idx
);

__weak_wur struct ir_node *ir_imm_init(enum ir_imm_type t, union ir_imm_val imm);
__weak_wur struct ir_node *ir_imm_bool_init(bool imm);
__weak_wur struct ir_node *ir_imm_char_init(char imm);
__weak_wur struct ir_node *ir_imm_float_init(float imm);
__weak_wur struct ir_node *ir_imm_int_init(int32_t imm);

__weak_wur struct ir_node *ir_sym_init(int32_t idx);
__weak_wur struct ir_node *ir_sym_ptr_init(int32_t idx);

__weak_wur struct ir_node *ir_store_init(struct ir_node *idx, struct ir_node *body);
__weak_wur struct ir_node *ir_store_sym_init(int32_t idx, struct ir_node *body);

__weak_wur struct ir_node *ir_bin_init(enum token_type op, struct ir_node *lhs, struct ir_node *rhs);
__weak_wur struct ir_node *ir_jump_init(int32_t idx);
__weak_wur struct ir_node *ir_cond_init(struct ir_node *cond, int32_t goto_label);
__weak_wur struct ir_node *ir_ret_init(bool is_void, struct ir_node *body);
__weak_wur struct ir_node *ir_member_init(int32_t idx, int32_t field_idx);
__weak_wur struct ir_node *ir_type_decl_init(const char *name, struct ir_node *decls);
__weak_wur struct ir_node *ir_func_decl_init(enum data_type ret_type, const char *name, struct ir_node *args, struct ir_node *body);
__weak_wur struct ir_node *ir_func_call_init(const char *name, struct ir_node *args);

void ir_node_cleanup(struct ir_node *ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_H