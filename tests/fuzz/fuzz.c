/* fuzz.c - Fuzz test.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

/* Usage: scripts/fuzz.sh or other way to start process
          from user shell. */

#include "front_end/lex/lex.h"
#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/ir_dump.h"
#include "util/vector.h"
#include "utils/test_utils.h"
#include <unistd.h>

/* ==========================
   Configuration.
   ========================== */

#define COMPLEX_STMT_LIMIT   \
    { static int limit = 0;  \
      if (limit++ >= 150)    \
          return; }

/* Bigger = larger expressions. */
#define BIN_EXPR_LEN 15

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

static void fprintf_n(FILE *stream, uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i)
        fputc(c, stream);
}



/* ==========================
   Source generator.
   ========================== */

#define __rand_array_entry(x) (x[rand() % (sizeof ((x)) / sizeof (*(x)))])

struct random_type {
    enum data_type dt;
    char           name[32];
};

const char *ops_int[] = {
    "+",
    "-",
    "<<",
    ">>",
    "%",
    "/",
    "*",
    "|",
    "&",
    "^"
};

const char *ops_float[] = {
    "+",
    "-",
    "*",
    "/"
};

const char *ops_bool[] = {
    "&&",
    "||",
    "==",
    "!=",
    ">",
    "<",
    ">=",
    "<="
};

struct random_type data_types[] = {
    { D_T_INT, "int" },
    { D_T_FLOAT, "float" },
    { D_T_CHAR, "char" },
    { D_T_BOOL, "bool" }
};

const char letters_set[] = {
    'A','B','C','D','E','F',
    'G','H','I','J','K',
    'L','M','N','O','P',
    'Q','R','S','T','U',
    'V','W','X','Y','Z',
    'a','b','c','d','e','f',
    'g','h','i','j','k',
    'l','m','n','o','p',
    'q','r','s','t','u',
    'v','w','x','y','z'
};

struct var_stack_entry {
    enum data_type dt;
    char           name[32];
};

struct fn_entry {
    char rt[32];
    char name[32];
    vector_t(enum data_type) args;
};

typedef vector_t(struct var_stack_entry) var_stack_t;

vector_t(var_stack_t) var_stack;
vector_t(struct fn_entry) fn_stack;

int emit_int()
{
    return rand();
}

double emit_float()
{
    float max = 99999.999;
    return ((float) rand() / (float) RAND_MAX) * max;
}

char emit_letter()
{
    return __rand_array_entry(letters_set);
}

void emit_string(char *out, uint64_t len)
{
    for (uint64_t i = 0; i < len; ++i)
        out[i] = emit_letter();
    out[len - 1] = '\0';
}

bool emit_bool()
{
    return rand() % 2 == 0;
}

struct random_type *emit_data_type()
{
    return &__rand_array_entry(data_types);
}

const char *emit_int_op()
{
    return __rand_array_entry(ops_int);
}

const char *emit_float_op()
{
    return __rand_array_entry(ops_float);
}

const char *emit_bool_op()
{
    return __rand_array_entry(ops_bool);
}



void emit_block(FILE *s);
void emit_assign(FILE *s);
void emit_bin(FILE *s, enum data_type dt);



void emit_bin_int_op(FILE *s, var_stack_t *top)
{
    if (top->count == 0)
        fprintf(s, "%d", emit_int());
    else {
        struct var_stack_entry *e =
            &vector_at(*top, rand() % top->count);

        if (e->dt == D_T_INT)
            fprintf(s, e->name);
        else
            fprintf(s, "%d", emit_int());
    }
}

void emit_bin_int(FILE *s)
{
    var_stack_t *top = &vector_back(var_stack);

    emit_bin_int_op(s, top);

    if (rand() % BIN_EXPR_LEN > 2) {
        fprintf(s, " %s ", emit_int_op());
        emit_bin_int(s);
    }
}



void emit_bin_float_op(FILE *s, var_stack_t *top)
{
    if (top->count == 0)
        fprintf(s, "%lf", emit_float());
    else {
        struct var_stack_entry *e =
            &vector_at(*top, rand() % top->count);

        if (e->dt == D_T_FLOAT)
            fprintf(s, e->name);
        else
            fprintf(s, "%lf", emit_float());
    }
}

void emit_bin_float(FILE *s)
{
    var_stack_t *top = &vector_back(var_stack);

    emit_bin_float_op(s, top);

    if (rand() % BIN_EXPR_LEN > 2) {
        fprintf(s, " %s ", emit_float_op());
        emit_bin_float(s);
    }
}



void emit_bin_char_op(FILE *s, var_stack_t *top)
{
    if (top->count == 0)
        fprintf(s, "'%c'", emit_letter());
    else {
        struct var_stack_entry *e =
            &vector_at(*top, rand() % top->count);

        if (e->dt == D_T_CHAR)
            fprintf(s, e->name);
        else
        fprintf(s, "'%c'", emit_letter());
    }
}

void emit_bin_char(FILE *s)
{
    var_stack_t *top = &vector_back(var_stack);

    emit_bin_char_op(s, top);

    if (rand() % BIN_EXPR_LEN > 2) {
        fprintf(s, " %s ", emit_int_op());
        emit_bin_char(s);
    }
}


void emit_bin(FILE *s, enum data_type dt)
{
    switch (dt) {
    case D_T_INT:
        emit_bin_int(s);
        break;
    case D_T_FLOAT:
        emit_bin_float(s);
        break;
    case D_T_CHAR:
        emit_bin_char(s);
        break;
    case D_T_BOOL:
        fprintf(s, "%s", rand() % 2 ? "true" : "false");
        break;
    default:
        break;
    }
}

void emit_var_decl(FILE *s)
{
    char name[32];
    struct random_type *type = emit_data_type();

    emit_string(name, sizeof (name));

    fprintf(s, "%s %s = ", type->name, name);

    emit_bin(s, type->dt);

    fprintf(s, ";");

    struct var_stack_entry e = { .dt = type->dt };
    strncpy(e.name, name, sizeof (e.name) - 1);

    vector_push_back(vector_back(var_stack), e);
}

void emit_arr_decl(FILE *s)
{
    char name[32];
    struct random_type *type = emit_data_type();

    emit_string(name, sizeof (name));

    fprintf(s, "%s %s", type->name, name);

    uint64_t max = rand() % 10 + 1;

    for (uint64_t i = 0; i < max; ++i) {
        fprintf(s, "[%ld]", rand() % 100 + 1);
    }

    fprintf(s, ";");

    struct var_stack_entry e = { .dt = type->dt };
    strncpy(e.name, name, sizeof (e.name) - 1);

    vector_push_back(vector_back(var_stack), e);
}

void emit_if(FILE *s)
{
    COMPLEX_STMT_LIMIT

    fprintf(s, "if (");
    emit_bin_int(s);
    fprintf(s, ")");

    emit_block(s);
}

void emit_for(FILE *s)
{
    COMPLEX_STMT_LIMIT

    fprintf(s, "for (");
    emit_var_decl(s);
    fprintf(s, " ");
    emit_bin_int(s);
    fprintf(s, "; )");

    emit_block(s);
}

void emit_while(FILE *s)
{
    COMPLEX_STMT_LIMIT

    fprintf(s, "while (");
    emit_bin_int(s);
    fprintf(s, ")");

    emit_block(s);
}

void emit_assign(FILE *s)
{
    var_stack_t *top = &vector_back(var_stack);

    if (top->count == 0)
        return;

    struct var_stack_entry *e =
        &vector_at(*top, rand() % top->count);

    fprintf(s, "%s = ", e->name);

    emit_bin(s, e->dt);

    fprintf(s, ";");
}

void emit_unary(FILE *s)
{
    fprintf(s, "una");
}

void emit_stmt(FILE *s)
{
    switch (rand() % 100) {
    case 0:           emit_block(s); break;
    case 10 ... 20:   emit_if(s); break;
    case 21 ... 30:   emit_for(s); break;
    case 31 ... 40:   emit_while(s); break;
    case 41 ... 60:   emit_assign(s); break;
    // case 51 ... 60:   emit_unary(s); break;
    case 61 ... 80:   emit_var_decl(s); break;
    case 81 ... 99:   emit_arr_decl(s); break;
    }
}

void emit_block(FILE *s)
{
    var_stack_t e = {0};

    uint64_t init = 1;
    uint64_t end  = 4;

    static int nest = 0;

    fprintf(s, "\n");
    fprintf_n(s, nest, ' ');
    fprintf(s, "{\n");

    ++nest;

    for (uint64_t i = init; i < end; ++i) {
        fprintf_n(s, nest, ' ');
        vector_push_back(var_stack, e);
        emit_stmt(s);
        vector_pop_back(var_stack);
        fprintf(s, "\n");
    }

    --nest;

    fprintf_n(s, nest, ' ');
    fprintf(s, "}");
}

void emit_block_main(FILE *s)
{
    var_stack_t e = {0};

    uint64_t init = 1;
    uint64_t end  = 4;

    static int nest = 0;

    fprintf(s, "int main() {\n");

    ++nest;

    vector_push_back(var_stack, e);
    for (uint64_t i = 0; i < 100; ++i) {
        fprintf_n(s, nest, ' ');
        emit_var_decl(s);
        fprintf(s, "\n");
    }

    for (uint64_t i = init; i < end; ++i) {
        fprintf_n(s, nest, ' ');
        vector_push_back(var_stack, e);
        emit_stmt(s);
        vector_pop_back(var_stack);
        fprintf(s, "\n");
    }
    --nest;

    fprintf_n(s, nest, ' ');
    fprintf(s, " return 0; }\n");
    vector_pop_back(var_stack);
}


void fuzz_print_source()
{
    char ch = 0;
    int lineno = 2;

    printf("% 6d: ", 1);

    while ((ch = fgetc(yyin)) != EOF) {
        putchar(ch);
        if (ch == '\n')
            printf("% 6d: ", lineno++);
    }

    fseek(yyin, 0, SEEK_SET);
}



/* ==========================
   Driver code.
   ========================== */

void compile(tok_array_t *tokens)
{
    struct ast_node *ast = parse(tokens->data, tokens->data + tokens->count);

    /* Preconditions for IR generator. */
    analysis_variable_use_analysis(ast);
    analysis_functions_analysis(ast);
    analysis_type_analysis(ast);

    tokens_cleanup(tokens);
    struct ir_unit unit = ir_gen(ast);
    ast_node_cleanup(ast);

    ir_dump_unit(stdout, &unit);
    ir_unit_cleanup(&unit);
}

void fuzz()
{
    if (yyin)
        fclose(yyin);

    lex_reset_state();
    lex_init_state();

    char   *buf = NULL;
    size_t _    = 0;

    yyin = open_memstream(&buf, &_);
    if (!yyin) {
        perror("open_memstream()");
        exit(1);
    }

    emit_block_main(yyin);

    yylex();
    fseek(yyin, 0, SEEK_SET);
    weak_set_source_stream(yyin);

    fuzz_print_source();

    compile(lex_consumed_tokens());
}

int main()
{
    srand(getpid());

    fuzz();

    return 0;
}