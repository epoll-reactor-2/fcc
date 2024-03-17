#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/ir_bin.h"
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
    ana_var_usage(ast);
    ana_fn(ast);
    ana_type(ast);
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
    fcc_set_source_stream(yyin);

    return lex_consumed_tokens();
}

struct ast_node *gen_ast(const char *filename)
{
    tok_array_t *t = gen_tokens(filename);
    struct ast_node *ast = parse(t->data, t->data + t->count);
    tokens_cleanup(t);
    return ast;
}

struct ir_unit gen_ir(const char *filename)
{
    struct ast_node *ast = gen_ast(filename);
    analyze(ast);
    return ir_gen(ast);
}


/**********************************************
 **              Stringify                   **
 **********************************************/
void dump_tokens(tok_array_t *toks)
{
    printf(
        "|             |                         |                 \n"
        "| Location    | Type                    | Value           \n"
        "|             |                         |                 \n"
        "----------------------------------------------------------\n"
    );
    for (uint64_t i = 0; i < toks->count; ++i) {
        struct token *t = &toks->data[i];
        printf(
            "% 4hd:% 4hd     %-25s %s\n",
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

void configure_ast(bool simple)
{
    struct ast_dump_config ast_config = {
        .omit_pos = simple,
        .colored  = 1
    };
    ast_dump_set_config(&ast_config);
}

/**********************************************
 **             Driver code                  **
 **********************************************/
void parse_cmdline(int argc, char *argv[])
{
    bool  tokens      = 0;
    bool  ast         = 0;
    bool  ast_simple  = 0;
    bool  ir          = 0;
    bool  read_bin_ir = 0;
    int   file_i      = -1;
    char *file        = NULL;

    /* This simple algorithm allows us to have
       command line args of type:

         1) <filename> --args...
         2) --args...  <filename> */
    for (int i = 1; i < argc; ++i)
        if      (!strcmp(argv[i], "--dump-tokens"))     tokens      = 1;
        else if (!strcmp(argv[i], "--dump-ast"))        ast         = 1;
        else if (!strcmp(argv[i], "--dump-ast-simple")) ast_simple  = 1;
        else if (!strcmp(argv[i], "--dump-ir"))         ir          = 1;
        else if (!strcmp(argv[i], "--read-ir"))         read_bin_ir = 1;
        else                                            file_i      = i;

    if (file_i == -1) {
        puts("No input file was given.");
        return;
    }

    file = argv[file_i];

    if (tokens) {
        tok_array_t *t = gen_tokens(file);
        dump_tokens(t);
        tokens_cleanup(t);
        exit(0);
    }

    if (ast_simple)
        ast = 1;

    if (ast) {
        configure_ast(/*simple=*/ast_simple);
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

    if (read_bin_ir) {
        struct ir_unit unit = ir_read_binary(file);
        dump_ir(&unit);
        ir_unit_cleanup(&unit);
        exit(0);
    }
}

void help();

void configure_diag()
{
    struct diag_config diag_config = {
        .ignore_warns  = 0,
        .show_location = 1
    };
    fcc_diag_set_config(&diag_config);
}

int main(int argc, char *argv[])
{
    if (argc < 2)
        help();

    configure_diag();

    parse_cmdline(argc, argv);
}

void help()
{
    printf(
        "Usage: fcc_compiler <options...> | <input-file>\n"
        "\n"
        "\t--dump-tokens\n"
        "\t--dump-ast\n"
        "\t--dump-ast-simple\n"
        "\t--dump-ir\n"
        "\t--read-ir\n"
    );
    exit(0);
}
