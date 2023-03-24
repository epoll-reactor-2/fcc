/* ir_dump.h - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

 #ifndef WEAK_COMPILER_MIDDLE_END_IR_DUMP_H
 #define WEAK_COMPILER_MIDDLE_END_IR_DUMP_H

#include "middle_end/ir.h"
#include <stdio.h>

/// Print IR to given stream.
///
/// \param ir      Pointer to IR statements array.
/// \param ir_size Array size.
/// \return 0 on success
///         1 on following errors:
///           - memory stream is NULL
///           - ir is NULL
int32_t ir_dump(FILE *mem, ir_node_t *ir, uint64_t ir_size);

 #endif // WEAK_COMPILER_MIDDLE_END_IR_DUMP_H