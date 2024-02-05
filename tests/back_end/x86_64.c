/* x86_64.c - Test cases for x86_64 codegen.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/x86_64.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool x86_64_test(const char *path, const char *filename)
{
    (void) filename;

    bool    ok               = 1;
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    struct  ir_unit    *unit = NULL;
    struct  ir_node    *it   = NULL;

    if (!setjmp(weak_fatal_error_buf)) {
        unit = gen_ir(path);
        ir_type_pass(unit);

        get_init_comment(yyin, expected_stream, NULL);

        /* ir_dump_unit(stdout, ir); */

        it = unit->fn_decls;
        while (it) {
            struct ir_fn_decl *decl = it->ir;
            /* Reordering before building CFG links. */
            ir_opt_reorder(decl);
            ir_opt_arith(decl);

            ir_cfg_build(decl);

            /* ir_dump(stdout, decl); */

            /* Wrong
               ir_opt_unreachable_code(decl); */

            /* There is some trouble with
               data flow of input function
               parameters.

               ir_opt_data_flow(decl); */

            /* ir_dump_cfg(tmp_cfg, decl); */
            /* ir_dump(stdout, decl); */
            /* cfg_edges_dump(stdout, decl); */
            it = it->next;
        }

        x86_64_gen(generated_stream, unit);

        fflush(expected_stream);
        fflush(generated_stream);

        int r = istrcmp(generated, expected);
        if (r != 0) {
            printf("Code mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            ok = 0;
            goto exit;
        }

        puts("Success!");
    } else {
        /// Error, will be printed in main.
        return 0;
    }

exit:
    yylex_destroy();
    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);
    ir_unit_cleanup(unit);

    return ok;
}

int main()
{
    return do_on_each_file("x86_64", x86_64_test);
}