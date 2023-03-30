/* ir.h - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_H
#define WEAK_COMPILER_MIDDLE_END_IR_H

#include "front_end/lex/data_type.h"
#include "front_end/lex/tok_type.h"
#include <stdbool.h>
#include <stdint.h>

typedef enum {
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
    IR_TYPE_DECL,
    IR_FUNC_DECL,
    IR_FUNC_CALL,
} ir_type_e;

/// Typed pointer to the IR node of any type.
///
/// Each implemented IR node must have methods
/// - ir_%name%_init(...)
/// - ir_%name%_cleanup(...)
/// .
typedef struct ir_node_t {
    ir_type_e  type;
    /// Instruction index. Needed to build
    /// Control Flow Graph from this IR in order
    /// to do graph-bases analysis.
    int32_t    instr_idx;
    void      *ir;
} ir_node_t;

typedef struct {
    data_type_e dt;
    /// This is index of an variable. Like
    /// D_T_INT %1.
    /// Alternatively, string names can be stored.
    int32_t idx;
} ir_alloca_t;

typedef struct {
    /// Immediate value. Used as argument of
    /// store or binary instructions.
    int32_t imm;
} ir_imm_t;

typedef struct {
    int32_t idx;
} ir_sym_t;

typedef enum {
    IR_STORE_IMM,
    IR_STORE_VAR,
    IR_STORE_BIN,
} ir_store_type_e;

typedef struct {
    /// Variable name, or index.
    /// %1 = ...
    int32_t         idx;
    /// Allowed body for store instruction:
    /// - immediate value,
    /// - binary operation,
    /// - variable (var).
    ir_store_type_e type;
    ir_node_t       body;
} ir_store_t;

typedef struct {
    /// Allowed body for binary instruction:
    /// - var op var
    /// - var op imm
    /// - imm op var
    /// - imm op imm
    ///
    /// \note: There is no unary operators.
    ///        They can be expressed through binary ones.
    tok_type_e op;
    ir_node_t  lhs;
    ir_node_t  rhs;
} ir_bin_t;

typedef struct {
    /// Label used to jump to.
    int32_t idx;
} ir_label_t;

typedef struct {
    /// Unconditonal jump.
    int32_t idx;
} ir_jump_t;

typedef struct {
    /// Condition. Requires binary operator as
    /// operand. In case of expressions like
    ///   if (x)
    /// it should looks like
    ///   if cmpneq x, 0.
    /// Requires only binary IR instruction.
    ir_node_t cond;
    /// Where to jump if condition passes.
    int32_t   goto_label;
} ir_cond_t;

typedef struct {
    /// Requires IR_RET or IR_RET_VOID. In case
    /// of the last one, op is NULL.
    bool is_void;
    /// Accepted values:
    /// - symbol (variable index),
    /// - immediate value.
    ir_node_t op;
} ir_ret_t;

typedef struct {
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
} ir_member_t;

typedef struct {
    int32_t  idx;
    /// Accepted values:
    /// - symbol (variable index),
    /// - immediate value.
    ir_node_t op;
} ir_array_access_t;

typedef struct {
    const char *name;
    uint64_t    decls_size;
    /// Accepted values:
    /// - ir_alloca_t (primitive type),
    /// - ir_type_decl_t (compound type, nested).
    ir_node_t  *decls;
} ir_type_decl_t;

typedef struct {
    /// Name instead of index required though
    /// (to be able to view something at all in assembly file).
    const char   *name;
    uint64_t      args_size;
    /// Accepted values:
    /// - ir_alloca_t (primitive type),
    /// - ir_type_decl_t (compound type, nested).
    ir_node_t    *args;
    uint64_t      body_size;
    ir_node_t    *body;
} ir_func_decl_t;

typedef struct {
    const char *name;
    uint64_t    args_size;
    /// Accepted values:
    /// - ir_sym_t,
    /// - ir_imm_t.
    /// Correct argument types is code generator responsibility.
    ir_node_t  *args;
} ir_func_call_t;

void ir_reset_internal_state();

ir_node_t ir_node_init(ir_type_e type, void *ir);
ir_node_t ir_alloca_init(data_type_e dt, int32_t idx);
ir_node_t ir_imm_init(int32_t imm);
ir_node_t ir_sym_init(int32_t idx);

ir_node_t ir_store_imm_init(int32_t idx, int32_t imm);
ir_node_t ir_store_var_init(int32_t idx, int32_t var_idx);
ir_node_t ir_store_binary_init(int32_t idx, ir_node_t bin);

ir_node_t ir_bin_init(tok_type_e op, ir_node_t lhs, ir_node_t rhs);
ir_node_t ir_label_init(int32_t idx);
ir_node_t ir_jump_init(int32_t idx);
ir_node_t ir_cond_init(ir_node_t cond, int32_t goto_label);
ir_node_t ir_ret_init(bool is_void, ir_node_t op);
ir_node_t ir_member_init(int32_t idx, int32_t field_idx);
ir_node_t ir_array_access_init(int32_t idx, ir_node_t op);
ir_node_t ir_type_decl_init(const char *name, uint64_t decls_size, ir_node_t *decls);
ir_node_t ir_func_decl_init(const char *name, uint64_t args_size, ir_node_t *args, uint64_t body_size, ir_node_t *body);
ir_node_t ir_func_call_init(const char *name, uint64_t args_size, ir_node_t *args);

void ir_node_cleanup(ir_node_t ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_H