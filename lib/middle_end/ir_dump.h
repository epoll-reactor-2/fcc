/* ir_dump.h - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_DUMP_H
#define WEAK_COMPILER_MIDDLE_END_IR_DUMP_H

#include "middle_end/ir.h"
#include <stdio.h>

const char *ir_type_to_string(enum ir_type t);

/// Print IR to given stream.
///
/// \param ir      Pointer to the function IR.
void ir_dump(FILE *mem, struct ir_func_decl *ir);

/// Print IR node to given stream.
///
/// \param ir      Pointer to IR the statement.
void ir_dump_node(FILE *mem, struct ir_node ir);

/// Print IR as dot graph. May be used to generate images.
///
/// $ dot -Tpng graph.dot -o graph.png
///
/// \param ir      First statement in a function.
void ir_dump_graph_dot(FILE *mem, struct ir_func_decl *ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_DUMP_H