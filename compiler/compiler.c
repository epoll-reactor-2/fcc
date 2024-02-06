#include "back_end/eval.h"
#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include <errno.h>
#include <string.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();



void tokens_cleanup(tok_array_t *toks)
{
    for (uint64_t i = 0; i < toks->count; ++i) {
        struct token *t = &toks->data[i];
        if (t->data)
            free(t->data);
    }
    vector_free(*toks);
}


/**********************************************
 **              Analysis                    **
 **********************************************/
void analyze(struct ast_node *ast)
{
    analysis_variable_use_analysis(ast);
    analysis_functions_analysis(ast);
    analysis_type_analysis(ast);
}

/**********************************************
 **             Generators                   **
 **********************************************/
tok_array_t *gen_tokens(const char *filename)
{
    lex_reset_state();
    lex_init_state();

    if (!yyin) yyin = fopen(filename, "r");
    else yyin = freopen(filename, "r", yyin);
    if (yyin == NULL) {
        printf("Could not open filename %s: %s\n", filename, strerror(errno));
        exit(1);
    }
    yylex();
    fseek(yyin, 0, SEEK_SET);
    weak_set_source_stream(yyin);

    return lex_consumed_tokens();
}

struct ast_node *gen_ast(const char *filename)
{
    tok_array_t *t = gen_tokens(filename);
    struct ast_node *ast = parse(t->data, t->data + t->count);
    tokens_cleanup(t);
    analyze(ast);
    return ast;
}

struct ir_unit gen_ir(const char *filename)
{
    return ir_gen(gen_ast(filename));
}


/**********************************************
 **              Stringify                   **
 **********************************************/
void dump_tokens(tok_array_t *toks)
{
    printf(
        "|             |               |                 \n"
        "| Location    | Type          | Value           \n"
        "|             |               |                 \n"
        "------------------------------------------------\n"
    );
    for (uint64_t i = 0; i < toks->count; ++i) {
        struct token *t = &toks->data[i];
        printf(
            "% 4ld:% 4ld     %-15s %s\n",
            t->line_no,
            t->col_no,
            tok_to_string(t->type),
            t->data ? t->data : ""
        );
    }
}

void dump_ast(struct ast_node *ast)
{
    ast_dump(stdout, ast);
}

void dump_ir(struct ir_unit *ir)
{
    ir_dump_unit(stdout, ir);
}


/**********************************************
 **             Interpreter                  **
 **********************************************/
void opt(struct ir_unit *ir)
{
    struct ir_node *it = ir->fn_decls;
    ir_type_pass(ir);
    while (it) {
        struct ir_fn_decl *decl = it->ir;
        ir_opt_reorder(decl);
        ir_opt_arith(decl);
        ir_cfg_build(decl);
        it = it->next;
    }
}

#ifdef CONFIG_USE_BACKEND_EVAL
void run_backend(const char *filename)
{
    struct ir_unit unit = gen_ir(filename);
    opt(&unit);

    int r = eval(&unit);
    printf("Exit with %d\n", r);
}
#endif /* CONFIG_USE_BACKEND_EVAL */

#ifdef CONFIG_USE_BACKEND_X86_64
void run_backend(const char *filename)
{
    (void) filename;
}
#endif /* CONFIG_USE_BACKEND_X86_64 */


/**********************************************
 **             Driver code                  **
 **********************************************/
void parse_cmdline(int argc, char *argv[])
{
    bool  tokens = 0;
    bool  ast    = 0;
    bool  ir     = 0;
    int   file_i = 0;
    char *file   = NULL;

    /* This simple algorithm allows us to have
       command line args of type:

         1) <filename> --args...
         2) --args...  <filename> */
    for (int i = 1; i < argc; ++i)
        if      (!strcmp(argv[i], "--dump-tokens")) tokens = 1;
        else if (!strcmp(argv[i], "--dump-ast"))    ast    = 1;
        else if (!strcmp(argv[i], "--dump-ir"))     ir     = 1;
        else                                        file_i = i;

    file = argv[file_i];

    if (tokens) {
        tok_array_t *t = gen_tokens(file);
        dump_tokens(t);
        tokens_cleanup(t);
        exit(0);
    }

    if (ast) {
        struct ast_node *ast = gen_ast(file);
        dump_ast(ast);
        ast_node_cleanup(ast);
        exit(0);
    }

    if (ir) {
        struct ir_unit unit = gen_ir(file);
        dump_ir(&unit);
        ir_unit_cleanup(&unit);
        exit(0);
    }

    run_backend(file);
}

void help();

void configure()
{
    struct diag_config diag_config = {
        .ignore_warns  = 0,
        .show_location = 1
    };
    weak_diag_set_config(&diag_config);

    struct ast_dump_config ast_config = {
        .omit_pos = 0,
        .colored  = 1
    };
    ast_dump_set_config(&ast_config);
}

int main(int argc, char *argv[])
{
    if (argc < 2)
        help();

    configure();

    parse_cmdline(argc, argv);
}

void help()
{
    printf(
        "Usage: weak_compiler <options...> | <input-file>\n"
        "\n"
        "\t--dump-tokens\n"
        "\t--dump-ast\n"
        "\t--dump-ir\n"
    );
    exit(0);
}