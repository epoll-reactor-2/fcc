/* ddg.h - Data dependence graph.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_DDG_H
#define WEAK_COMPILER_MIDDLE_END_DDG_H

struct ir_func_decl;

/// Build data dependence graph. Read operation
/// is dependent on write operation.
///
/// \note It makes sense to call this function only
///       after optimizations.
void ir_ddg_build(struct ir_func_decl *decl);

#endif // WEAK_COMPILER_MIDDLE_END_DDG_H