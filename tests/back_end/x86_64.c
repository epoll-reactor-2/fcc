#include "back_end/x86_64.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool ir_test(const char *path, const char *filename)
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

        extract_assertion_comment(yyin, expected_stream);

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
    int     ret          = 0;
    char   *err_buf      = NULL;
    char   *warn_buf     = NULL;
    size_t  err_buf_len  = 0;
    size_t  warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    if (!do_on_each_file("/test_inputs/x86_64", ir_test)) {
        ret = -1;

        if (err_buf)
            fputs(err_buf, stderr);

        if (warn_buf)
            fputs(warn_buf, stderr);
    }

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return ret;
}