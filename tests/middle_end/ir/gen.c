/* gen.c - Tests for IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir_dump.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int dom_test(const char *path, const char *filename)
{
    (void) filename;

    int     rc               = 0;
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);

    if (!setjmp(weak_fatal_error_buf)) {
        /* NOTE: CFG is not strictly needed there. */
        struct ir_unit ir = gen_ir(path);

        get_init_comment(yyin, expected_stream, NULL);

        ir_dump_unit(generated_stream, &ir);
        fflush(generated_stream);
        ir_unit_cleanup(&ir);

        if (strcmp(expected, generated) != 0) {
            printf("IR mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            rc = -1;
            goto exit;
        }
    } else {
        /* Error, will be printed in main. */
        return -1;
    }

exit:
    fclose(yyin);
    yylex_destroy();
    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);

    return rc;
}

int main()
{
    return do_on_each_file("ir_gen", dom_test);
}