/* opt.h - IR-based optimizations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_OPT_H
#define WEAK_COMPILER_MIDDLE_END_OPT_H

struct ir_node;

/// Invariant code motion.
///
/// This is based on dominator tree analyis (probably).
///
/// \pre Computed dominator tree.
void ir_opt_motion(struct ir_node *ir);

/// Constant and expressions folding.
void ir_opt_fold(struct ir_node *ir);

/// Transform arithmetic operations.
///
///     1. Negation laws:
///        - A - (-B) = A + B
///        -(-A) = A
///
///     2. Double negation laws:
///        - ~(~A) = A
///
///     3. Bitwise complement laws:
///        - ~A + 1 = -A
///        - ~(-A) - 1 = A
///
///     4. Zero laws:
///        - A + 0 = A
///        - A - 0 = A
///        - A * 0 = 0
///        - A & 0 = 0
///        - A | 0 = A
///
///     5. Identity laws:
///        - A + (-A) = 0
///        - A - A = 0
///        - A * 1 = A
///        - A & 1 = A
///        - A | 1 = 1
///
///     6. De Morgan's laws:
///        - ~(A & B) = ~A | ~B
///        - ~(A | B) = ~A & ~B
///
///     7. Distributive laws:
///        - A * (B + C) = (A * B) + (A * C)
///        - A + (B * C) = (A + B) * (A + C)
///
///     8. Associative laws:
///        - (A + B) + C = A + (B + C)
///        - (A * B) * C = A * (B * C)
///
///     9. Commutative laws:
///        - A + B = B + A
///        - A * B = B * A
///        - A & B = B & A
///        - A | B = B | A
void ir_opt_arith(struct ir_node *ir);

#endif // WEAK_COMPILER_MIDDLE_END_OPT_H