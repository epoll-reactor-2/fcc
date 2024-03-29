/* parse.c - Syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast.h"
#include "front_end/data_type.h"
#include "front_end/parse.h"
#include "front_end/tok.h"
#include "util/alloc.h"
#include "util/diagnostic.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>

/**********************************************
 **              Lex callback                **
 **********************************************/

extern int yylex();
extern void yyrestart(FILE *input_file);

/* We use stack because C grammar may require from us
   lookahead by few tokens. */
static vector_t(struct token) token_stack;
struct token current_token;

void lex_token(struct token *t)
{
    memcpy(&current_token, t, sizeof (*t));
}

static void lex_free()
{
    vector_free(token_stack);
}

static struct token *peek_current()
{
    return &current_token;
}

/* TODO: Such API
         1) Clear stack
         2) peek_next(2)
            \
             Lex 2 elements, next process.
         
         Don't keep everything for no reason. */
static struct token *peek_next()
{
    if (yylex() <= 0)
        return NULL;
    return peek_current();
}

/**********************************************
 **                Parser                    **
 **********************************************/

typedef vector_t(struct ast_node *) ast_array_t;

struct localized_data_type {
    enum data_type  data_type;
    char           *type_name;
    uint16_t        ptr_depth;
    uint16_t        line_no;
    int16_t         col_no;
};

noreturn static void report_unexpected(struct token *t)
{
    fcc_compile_error(t->line_no, t->col_no, "Unexpected token `%s`", tok_to_string(t->type));
}

struct token *require_token(enum token_type t)
{
    struct token *curr_tok = peek_current();

    if (curr_tok->type != t)
        fcc_compile_error(
            curr_tok->line_no,
            curr_tok->col_no,
            "Expected `%s`, got `%s`",
            tok_to_string(t), tok_to_string(curr_tok->type)
        );
    
    peek_next();

    return curr_tok;
}

struct token *require_char(char c)
{
    return require_token(tok_char_to_tok(c));
}

unused static enum data_type tok_to_data_type(enum token_type t)
{
    switch (t) {
    case T_VOID:   return D_T_VOID;
    case T_INT:    return D_T_INT;
    case T_FLOAT:  return D_T_FLOAT;
    case T_CHAR:   return D_T_CHAR;
    case T_BOOL:   return D_T_BOOL;
    case T_SYM:    return D_T_STRUCT;
    default:
        fcc_unreachable(
            "Cannot convert token `%s` to the data type",
            tok_to_string(t)
        );
    }
}

/* https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1548.pdf */
unused static enum token_type             parse_punctuator(); /* 6.4.6 */
unused static struct ast_node            *parse_storage_class_specifier(); /* 6.7.1 */
unused static struct localized_data_type  parse_type_specifier(); /* 6.7.2 */
unused static enum token_type             parse_struct_or_union(); /* 6.7.2.1 */
unused static struct ast_node            *parse_enum_specifier(); /* 6.7.2.2 */
unused static enum token_type             parse_type_qualifier(); /* 6.7.3 */
unused static enum token_type             parse_function_specifier(); /* 6.7.4 */
unused static struct ast_node            *parse_translation_unit(); /* 6.9 */

static enum token_type parse_punctuator() /* 6.4.6 */
{
    struct token *c = peek_next();
    switch (c->type) {
    case T_OPEN_BRACKET: /* [ */
    case T_CLOSE_BRACKET: /* ] */
    case T_OPEN_PAREN: /* ( */
    case T_CLOSE_PAREN: /* ) */
    case T_OPEN_BRACE: /* { */
    case T_CLOSE_BRACE: /* } */
    case T_DOT: /* . */
    case T_ARROW: /* -> */

    case T_INC: /* ++ */
    case T_DEC: /* -- */
    case T_BIT_AND: /* & */
    case T_STAR: /* * */
    case T_PLUS: /* + */
    case T_MINUS: /* - */
    case T_TILDE: /* ~ */
    case T_EXCLAMATION: /* ! */

    case T_SLASH: /* / */
    case T_MOD: /* % */
    case T_SHL: /* << */
    case T_SHR: /* >> */
    case T_LT: /* < */
    case T_GT: /* > */
    case T_LE: /* <= */
    case T_GE: /* >= */
    case T_EQ: /* == */
    case T_NEQ: /* != */
    case T_BIT_XOR: /* ^ */
    case T_BIT_OR: /* | */
    case T_AND: /* && */
    case T_OR: /* || */

    case T_QUESTION_MARK: /* ? */
    case T_COLON: /* : */
    case T_SEMICOLON: /* ; */
    case T_ELLIPSIS: /* ... */

    case T_ASSIGN: /* = */
    case T_MUL_ASSIGN: /* *= */
    case T_DIV_ASSIGN: /* /= */
    case T_MOD_ASSIGN: /* %= */
    case T_PLUS_ASSIGN: /* += */
    case T_MINUS_ASSIGN: /* -= */
    case T_SHL_ASSIGN: /* <<= */
    case T_SHR_ASSIGN: /* >>= */
    case T_BIT_AND_ASSIGN: /* &= */
    case T_BIT_XOR_ASSIGN: /* &= */
    case T_BIT_OR_ASSIGN: /* |= */

    case T_COMMA: /* , */
    case T_HASH: /* # */
    case T_HASH_HASH: /* ## */
        return c->type;
    default:
        report_unexpected(c);
    }
}

static struct ast_node *parse_storage_class_specifier() /* 6.7.1 */
{
    struct token *c = peek_next();
    switch (c->type) {
    case T_TYPEDEF:
    case T_EXTERN:
    case T_STATIC:
    case T_THREAD_LOCAL:
    case T_AUTO:
    case T_REGISTER:
        return NULL;
    default:
        report_unexpected(c);
    }
}

static struct localized_data_type parse_type_specifier() /* 6.7.2 */
{
    struct token *c = peek_next();
    struct localized_data_type dt = {
        .col_no  = c->col_no,
        .line_no = c->line_no,
    };
    enum data_type t = 0;

    switch (c->type) {
    case T_VOID: t = D_T_VOID; break;
    case T_CHAR: t = D_T_CHAR; break;
    case T_SHORT: t = D_T_SHORT; break;
    case T_INT: t = D_T_INT; break;
    case T_LONG: t = D_T_LONG; break;
    case T_FLOAT: t = D_T_FLOAT; break;
    case T_DOUBLE: t = D_T_DOUBLE; break;
    case T_SIGNED: t = D_T_SIGNED; break;
    case T_UNSIGNED: t = D_T_UNSIGNED; break;
    case T_BOOL: t = D_T_BOOL; break;
    case T_COMPLEX: t = D_T_COMPLEX; break;
    default:
        report_unexpected(c);
    }
    dt.data_type = t;

    return dt;
}

static enum token_type parse_struct_or_union() /* 6.7.2.1 */
{
    struct token *c = peek_next();
    switch (c->type) {
    case T_STRUCT:
    case T_UNION:
        return c->type;
    default:
        report_unexpected(c);
    }
}

static struct ast_node *parse_enum_specifier() /* 6.7.2.2 */
{
    require_token(T_ENUM);
    struct token *c = peek_current();

    switch (c->type) {
    case T_SYM:
        return NULL;
    case T_OPEN_BRACE:
        return NULL;
    default:
        report_unexpected(c);
    }
}

static enum token_type parse_type_qualifier() /* 6.7.3 */
{
    struct token *c = peek_next();
    switch (c->type) {
    case T_CONST:
    case T_RESTRICT:
    case T_VOLATILE:
    case T_ATOMIC:
        return c->type;
    default:
        report_unexpected(c);
    }
}

static enum token_type parse_function_specifier() /* 6.7.4 */
{
    struct token *c = peek_next();
    switch (c->type) {
    case T_INLINE:
    case T_NORETURN:
        return c->type;
    default:
        report_unexpected(c);
    }
}

static struct ast_node *parse_translation_unit() /* 6.9 */
{
    return NULL;
}

/**********************************************
 **             Preprocessor                 **
 **********************************************/

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

static vector_t(char *) pp_paths;

void pp_init()
{
    static char *p[] = {
        "/usr/include",
        "/usr/include/bits",
        "/usr/include/linux",
        "/usr/include/c++/13.2.1",
        "/usr/include/c++/13.2.1/tr1",
        "/usr/include/c++/13.2.1/bits",
        "/usr/include/c++/13.2.1/x86_64-pc-linux-gnu",
        "/usr/include/x86_64-linux-gnu",
        NULL
    };
    char **it = p;

    while (*it)
        vector_push_back(pp_paths, strdup(*it++));
}

void pp_deinit()
{
    vector_foreach(pp_paths, i) {
        char *s = vector_at(pp_paths, i);
        free(s);
    }
    vector_free(pp_paths);
}

void pp_add_include_path(const char *path)
{
    printf("PP: adding %s\n", path);
    vector_push_back(pp_paths, strdup(path));
}

static FILE *pp_try_open(const char *filename)
{
    char path[512] = {0};

    vector_foreach(pp_paths, i) {
        const char *pp_path = vector_at(pp_paths, i);
        snprintf(path, sizeof (path) - 1, "%s/%s", pp_path, filename);

        printf("PP: Searching %s\n", path);

        FILE *f = fopen(path, "rb");
        if (f)
            return f;
    }

    printf("Cannot open file %s\n", filename);
    exit(-1);
}

static void pp_read();

static void pp(const char *filename)
{
    FILE *f = pp_try_open(filename);

    char line[512] = {0};
    while (1) {
        if (!fgets(line, 512, f)) {
            fclose(f);
            return;
        }

        fwrite(line, strlen(line), 1, yyin);

        /* TODO: Now theoretically parser can operate on one
                 source code fragment of some small size. As an
                 option, we can put the whole source tokens into
                 one token table and start to parse with it. */
        pp_read();
    }
}

/**********************************************
 **                #include                  **
 **********************************************/

static void pp_include_path_user(char *path)
{
    strcpy(path, peek_current()->data);
}

static void pp_include_path_system(char *path)
{
    struct token *t = peek_next();
    while (!tok_is(t, '>')) {
        path = strcat(path, t->data ? t->data : tok_to_string(t->type));
        t = peek_next();
    }

    require_char('>');
}

static void pp_include()
{
    struct token *t = peek_next();

    bool is_system = tok_is(t, '<');
    bool is_user   = t->type == T_STRING_LITERAL;

    if (!is_system && !is_user)
        report_unexpected(t);

    char path[512] = {0};

    if (is_user)   pp_include_path_user(path);
    if (is_system) pp_include_path_system(path);

    pp(path);
}

/**********************************************
 **                #define                   **
 **********************************************/

unused static void pp_define_macro(unused struct token *t)
{}

unused static void pp_define_id(unused struct token *t)
{}

/* 1. #define macro
   2. #define macro(...) */
static void pp_define()
{
    const struct token *t = peek_next();

    if (t->type == T_MACRO)
        pp_define_macro(t);
    else
        pp_define_id(t);

    while (1) {
        switch (peek_current()->type) {
        case T_BACKSLASH:
            peek_next();
            break;
        case T_NEWLINE:
            goto out;
        default:
            peek_next();
            break;
        }
    }

out:
    return;
}

static void pp_directive()
{
    struct token *t = peek_next();

    switch (t->type) {
    /* 6.10 if-group */
    case T_IFDEF:
        break;
    case T_IFNDEF:
        break;
    case T_IF:
        break;
    /* 6.10 elif-groups */
    case T_ELIF:
        break;
    /* 6.10 endif-line */
    case T_ENDIF:
        break;
    /* 6.10 control-line */
    case T_INCLUDE:
        pp_include();
        break;
    case T_DEFINE:
        pp_define();
        break;
    case T_UNDEF:
        break;
    case T_LINE:
        break;
    case T_ERROR:
        break;
    case T_PRAGMA:
        break;
    default:
        report_unexpected(t);
    }
}

static void pp_read()
{
    struct token *t = peek_next();

    while (t) {
        switch (t->type) {
        case T_HASH:
            pp_directive();
            break;
        default:
            /* Rest of tokens dedicated for parser not preprocessor. */
            vector_push_back(token_stack, *t);
            break;
        }
        t = peek_next();
    }
}

/**********************************************
 **                Parser                    **
 **********************************************/

struct ast_node *parse(const char *filename)
{
    char  *_  = NULL;
    size_t __ = 0;
    yyin = open_memstream(&_, &__);

    pp(filename);

    vector_foreach(token_stack, i) {
        struct token *t = &vector_at(token_stack, i);
        printf("Consume %s %s\n", tok_to_string(t->type), t->data);
    }

    lex_free();
    return NULL;
}

/*
Однажды болезнями, стонами, страхами затаёнными
Ты придёшь на голос мой - я позову.
Тропы родными протоптаны,
Мрамор высечен, ямы закопаны.
С головой под землёй в нижнем ряду.
Горя слезами невечными,
Зеркалами завешанными
Ты пойдёшь вслед за мной - я провожу.
*/