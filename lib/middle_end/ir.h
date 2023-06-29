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
    /// Immediate value.
    IR_IMM,
    IR_SYM,
    IR_STORE,
    IR_BIN,
    IR_LABEL,
    IR_JUMP,
    IR_COND,
    IR_RET,
    /// This used in ret instruction to represent
    /// `return;` from void functions.
    IR_RET_VOID,
    IR_MEMBER,
    IR_ARRAY_ACCESS,
    /// Code generator should store type declarations
    /// and refer to it in order to compute type
    /// size and member offsets.
    IR_TYPE_DECL,
    IR_FUNC_DECL,
    IR_FUNC_CALL,
};

struct ir {
    uint64_t        decls_size;
    /// Accepted values: struct ir_func_decl.
    struct ir_node *decls;
};

/// This IR node designed to be able to represent
/// Control Flow Graph (CFG), so each node has `visited`
/// flag for convenience. Each concrete IR node has
/// pointer to the next statement in execution flow,
/// if such needed. Thus, statements, contained only
/// inside other statements cannot have such link
/// (immediate, symbol, binary operation).
///
/// Each implemented IR node must have methods
/// - ir_%name%_init(...)
/// - ir_%name%_cleanup(...)
/// .
struct ir_node {
    enum ir_type type;
    /// Instruction index. Needed to build
    /// Control Flow Graph from this IR in order
    /// to do graph-bases analysis.
    int32_t      instr_idx;
    void        *ir;
    bool         visited;
};

struct ir_alloca {
    enum data_type  dt;
    /// This is index of an variable. Like
    /// D_T_INT %1.
    /// Alternatively, string names can be stored.
    int32_t         idx;
    struct ir_node *next;
};

enum ir_imm_type {
    IMM_BOOL,
    IMM_CHAR,
    IMM_FLOAT,
    IMM_INT
};

struct ir_imm {
    enum ir_imm_type type;
    /// Immediate value. Used as argument of
    /// store or binary instructions.
    union {
        bool         imm_bool;
        char         imm_char;
        float        imm_float;
        int32_t      imm_int;
    };
};

struct ir_sym {
    int32_t idx;
};

enum ir_store_type {
    IR_STORE_IMM,
    IR_STORE_VAR,
    IR_STORE_BIN,
};

struct ir_store {
    /// Variable name, or index.
    /// %1 = ...
    int32_t idx;
    /// Allowed body for store instruction:
    /// - immediate value,
    /// - binary operation,
    /// - variable (var).
    enum ir_store_type  type;
    struct ir_node      body;
    struct ir_node     *next;
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
    enum token_type op;
    struct ir_node  lhs;
    struct ir_node  rhs;
};

struct ir_label {
    /// Label used to jump to.
    int32_t         idx;
    struct ir_node *next;
};

struct ir_jump {
    /// Unconditonal jump.
    int32_t         idx;
    struct ir_node *next;
};

struct ir_cond {
    /// Condition. Requires binary operator as
    /// operand. In case of expressions like
    ///   if (x)
    /// it should looks like
    ///   if cmpneq x, 0.
    /// Requires only binary IR instruction.
    struct           ir_node cond;
    int32_t          goto_label;
    struct ir_node  *next_true;
    struct ir_node  *next_false;
};

struct ir_ret {
    /// Requires IR_RET or IR_RET_VOID. In case
    /// of the last one, op is NULL.
    bool is_void;
    /// Accepted values:
    /// - symbol (variable index),
    /// - immediate value.
    struct ir_node  op;
    struct ir_node *next;
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

struct ir_array_access {
    int32_t idx;
    /// Accepted values:
    /// - symbol (variable index),
    /// - immediate value.
    struct ir_node op;
};

struct ir_type_decl {
    const char *name;
    uint64_t    decls_size;
    /// Accepted values:
    /// - struct ir_alloca (primitive type),
    /// - struct ir_type_decl_t (compound type, nested).
    struct ir_node  *decls;
};

struct ir_func_decl {
    /// Name instead of index required though
    /// (to be able to view something at all in assembly file).
    const char     *name;
    uint64_t        args_size;
    /// Accepted values:
    /// - struct ir_alloca (primitive type),
    /// - struct ir_type_decl_t (compound type, nested).
    struct ir_node *args;
    struct ir_node *body;
    uint64_t        body_size;
};

struct ir_func_call {
    const char     *name;
    uint64_t        args_size;
    /// Accepted values:
    /// - struct ir_sym,
    /// - struct ir_imm.
    /// Correct argument types is code generator responsibility.
    struct ir_node *args;
    struct ir_node *next;
};

void ir_reset_internal_state();

__weak_wur struct ir_node ir_node_init(enum ir_type type, void *ir);
__weak_wur struct ir_node ir_alloca_init(enum data_type dt, int32_t idx);

__weak_wur struct ir_node ir_imm_bool_init(bool imm);
__weak_wur struct ir_node ir_imm_char_init(char imm);
__weak_wur struct ir_node ir_imm_float_init(float imm);
__weak_wur struct ir_node ir_imm_int_init(int32_t imm);

__weak_wur struct ir_node ir_sym_init(int32_t idx);

__weak_wur struct ir_node ir_store_imm_init(int32_t idx, struct ir_node imm);
__weak_wur struct ir_node ir_store_var_init(int32_t idx, int32_t var_idx);
__weak_wur struct ir_node ir_store_bin_init(int32_t idx, struct ir_node bin);

__weak_wur struct ir_node ir_bin_init(enum token_type op, struct ir_node lhs, struct ir_node rhs);
__weak_wur struct ir_node ir_label_init(int32_t idx);
__weak_wur struct ir_node ir_jump_init(int32_t idx);
__weak_wur struct ir_node ir_cond_init(struct ir_node cond, int32_t goto_label);
__weak_wur struct ir_node ir_ret_init(bool is_void, struct ir_node op);
__weak_wur struct ir_node ir_member_init(int32_t idx, int32_t field_idx);
__weak_wur struct ir_node ir_array_access_init(int32_t idx, struct ir_node op);
__weak_wur struct ir_node ir_type_decl_init(const char *name, uint64_t decls_size, struct ir_node *decls);
__weak_wur struct ir_node ir_func_decl_init(const char *name, uint64_t args_size, struct ir_node *args, uint64_t body_size, struct ir_node *body);
__weak_wur struct ir_node ir_func_call_init(const char *name, uint64_t args_size, struct ir_node *args);

void ir_node_cleanup(struct ir_node ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_H