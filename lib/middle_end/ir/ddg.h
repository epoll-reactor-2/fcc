/* ddg.h - Data dependence graph.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_DDG_H
#define WEAK_COMPILER_MIDDLE_END_DDG_H

struct ir_fn_decl;

/** Build data dependence graph. Read operation
    is dependent on write operation.
   
    \note It makes sense to call this function before
          and after optimization to maintain correct
          links.
   
    \todo This algorithm does not take care of loops
          and what is going on in future (after
          loop header, for example). */
void ir_ddg_build(struct ir_fn_decl *decl);

#endif // WEAK_COMPILER_MIDDLE_END_DDG_H