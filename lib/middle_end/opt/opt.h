/* opt.h - IR-based optimizations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_OPT_H
#define WEAK_COMPILER_MIDDLE_END_OPT_H

struct ir;

/// Invariant code motion.
///
/// This is based on dominator tree analyis (probably).
///
/// \pre Computed dominator tree.
void ir_opt_motion(struct ir *ir);

#endif // WEAK_COMPILER_MIDDLE_END_OPT_H