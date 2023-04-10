/* ir_gen.h - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GEN_H
#define WEAK_COMPILER_MIDDLE_END_IR_GEN_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;
typedef struct ir_node_t ir_node_t;

typedef struct {
    uint64_t   decls_size;
    /// This is allocated dynamically.
    /// Accepted values: ir_func_decl_t.
    ir_node_t *decls;
} ir_t;

/// Create IR from AST. Implemented as recursive visitor.
///
/// Preconditions:
/// - Applied all front-end analysis
///   - variable_use_analysis
///   - functions_analysis
///   - type_analysis 
ir_t ir_gen(ast_node_t *ast);
void ir_cleanup(ir_t *ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GEN_H