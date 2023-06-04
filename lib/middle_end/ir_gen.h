/* ir_gen.h - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GEN_H
#define WEAK_COMPILER_MIDDLE_END_IR_GEN_H

#include <stdint.h>

struct ast_node;
struct ir_node;
struct ir;

/// Create IR from AST. Implemented as recursive visitor.
///
/// Preconditions:
/// - Applied all front-end analysis
///   - variable_use_analysis
///   - functions_analysis
///   - type_analysis 
struct ir ir_gen(struct ast_node *ast);
void   ir_cleanup(struct ir *ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GEN_H
