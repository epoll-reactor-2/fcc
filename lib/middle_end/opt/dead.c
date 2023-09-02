/* dead.c - Dead code elimination.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/opt/opt.h"
#include "middle_end/ir/ir.h"
#include "util/unreachable.h"
#include "util/alloc.h"
#include <assert.h>

/*
fun main():
       0:   alloca int %0
       1:   store %0 $1
       2:   store %0 $2
       3:   store %0 $3
       4:   ret %0

    * used = {}

    * Iterate over i0
    * * put i0 to used

    * Iterate over i1 (store)
    * * check used array for %0
    * * put i1 to used

    * Iterate over i2 (store)
    * * check used array for %0
    * * %0 found
    * * remove %0 (i1) from used array
    * * put i2 to used

    * Iterate over i3 (store)
    * * check used array for %0
    * * %0 found
    * * remove %0 (i2) from used array
    * * put i2 to used

    * Iterate over i4 (ret)
    * * check used array for %0
    * * if %0 found in used
    * * * do nothing
    * * else
    * * * 

    TODO: dominators?
*/

static void opt_dce(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;

    while (it) {

        it = it->next;
    }
}

void ir_opt_dead_code_elimination(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        opt_dce(it->ir);
        it = it->next;
    }
}