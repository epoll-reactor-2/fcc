/* grammar.lex - Language acceptable tokens specification.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

%{

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wanalyzer-allocation-size"
#pragma GCC diagnostic ignored "-Wanalyzer-deref-before-check"
#pragma GCC diagnostic ignored "-Wanalyzer-double-fclose"
#pragma GCC diagnostic ignored "-Wanalyzer-double-free"
#pragma GCC diagnostic ignored "-Wanalyzer-exposure-through-output-file"
#pragma GCC diagnostic ignored "-Wanalyzer-exposure-through-uninit-copy"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-access-mode-mismatch"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-double-close"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-leak"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-phase-mismatch"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-type-mismatch"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-use-after-close"
#pragma GCC diagnostic ignored "-Wanalyzer-fd-use-without-check"
#pragma GCC diagnostic ignored "-Wanalyzer-file-leak"
#pragma GCC diagnostic ignored "-Wanalyzer-free-of-non-heap"
#pragma GCC diagnostic ignored "-Wanalyzer-imprecise-fp-arithmetic"
#pragma GCC diagnostic ignored "-Wanalyzer-infinite-recursion"
#pragma GCC diagnostic ignored "-Wanalyzer-jump-through-null"
#pragma GCC diagnostic ignored "-Wanalyzer-malloc-leak"
#pragma GCC diagnostic ignored "-Wanalyzer-mismatching-deallocation"
#pragma GCC diagnostic ignored "-Wanalyzer-null-argument"
#pragma GCC diagnostic ignored "-Wanalyzer-null-dereference"
#pragma GCC diagnostic ignored "-Wanalyzer-out-of-bounds"
#pragma GCC diagnostic ignored "-Wanalyzer-possible-null-argument"
#pragma GCC diagnostic ignored "-Wanalyzer-possible-null-dereference"
#pragma GCC diagnostic ignored "-Wanalyzer-putenv-of-auto-var"
#pragma GCC diagnostic ignored "-Wanalyzer-shift-count-negative"
#pragma GCC diagnostic ignored "-Wanalyzer-shift-count-overflow"
#pragma GCC diagnostic ignored "-Wanalyzer-stale-setjmp-buffer"
#pragma GCC diagnostic ignored "-Wanalyzer-unsafe-call-within-signal-handler"
#pragma GCC diagnostic ignored "-Wanalyzer-use-after-free"
#pragma GCC diagnostic ignored "-Wanalyzer-use-of-pointer-in-stale-stack-frame"
#pragma GCC diagnostic ignored "-Wanalyzer-use-of-uninitialized-value"
#pragma GCC diagnostic ignored "-Wanalyzer-va-arg-type-mismatch"
#pragma GCC diagnostic ignored "-Wanalyzer-va-list-exhausted"
#pragma GCC diagnostic ignored "-Wanalyzer-va-list-leak"
#pragma GCC diagnostic ignored "-Wanalyzer-va-list-use-after-va-end"
#pragma GCC diagnostic ignored "-Wanalyzer-write-to-const"
#pragma GCC diagnostic ignored "-Wanalyzer-write-to-string-literal"

#include "front_end/lex/tok.h"

int yycolumn = 1;

#define YY_USER_ACTION                                                   \
  lex_lineno = prev_yylineno;                                            \
  lex_colno = yycolumn;                                                  \
  if (yylineno == prev_yylineno) {                                       \
      yycolumn += yyleng;                                                \
  } else {                                                               \
    for (yycolumn = 1; yytext[yyleng - yycolumn] != '\n'; ++yycolumn) {} \
    prev_yylineno = yylineno;                                            \
  }

extern void lex_consume_token(struct token *tok);

#define LEX_CONSUME_WORD(tok_type) do {                                  \
    struct token t = {                                                   \
        .data    = strdup(yytext),                                       \
        .type    = tok_type,                                             \
        .line_no = lex_lineno,                                           \
        .col_no  = lex_colno                                             \
    };                                                                   \
    lex_consume_token(&t);                                               \
} while (0);

/* Operator can have no data, since all information about it contained
   in type. */
#define LEX_CONSUME_OPERATOR(tok_type) do {                              \
    struct token t = {                                                   \
        .data    = NULL,                                                 \
        .type    = tok_type,                                             \
        .line_no = lex_lineno,                                           \
        .col_no  = lex_colno                                             \
    };                                                                   \
    lex_consume_token(&t);                                               \
} while (0);

%}
%option noyywrap nounput noinput
%option yylineno

%%
 int lex_lineno, lex_colno;
 int prev_yylineno = yylineno;
   
\/\/.*\n                     /* Requirement [2.3.1] */
\/\*.*\*\/                   /* Requirement [2.3.2] */
[[:space:]]                  /* Ignore whitespace. */

-?[0-9]+                     LEX_CONSUME_WORD(TOK_INTEGRAL_LITERAL)
-?[0-9]+\.[0-9]+             LEX_CONSUME_WORD(TOK_FLOATING_POINT_LITERAL)
\"([^\"\\]*(\\.[^\"\\]*)*)\" LEX_CONSUME_WORD(TOK_STRING_LITERAL)
\'.\'                        LEX_CONSUME_WORD(TOK_CHAR_LITERAL)

"bool"                       LEX_CONSUME_WORD(TOK_BOOL)
"break"                      LEX_CONSUME_WORD(TOK_BREAK)
"char"                       LEX_CONSUME_WORD(TOK_CHAR)
"continue"                   LEX_CONSUME_WORD(TOK_CONTINUE)
"do"                         LEX_CONSUME_WORD(TOK_DO)
"else"                       LEX_CONSUME_WORD(TOK_ELSE)
"false"                      LEX_CONSUME_WORD(TOK_FALSE)
"float"                      LEX_CONSUME_WORD(TOK_FLOAT)
"for"                        LEX_CONSUME_WORD(TOK_FOR)
"if"                         LEX_CONSUME_WORD(TOK_IF)
"int"                        LEX_CONSUME_WORD(TOK_INT)
"return"                     LEX_CONSUME_WORD(TOK_RETURN)
"struct"                     LEX_CONSUME_WORD(TOK_STRUCT)
"true"                       LEX_CONSUME_WORD(TOK_TRUE)
"void"                       LEX_CONSUME_WORD(TOK_VOID)
"while"                      LEX_CONSUME_WORD(TOK_WHILE)

"="                          LEX_CONSUME_OPERATOR(TOK_ASSIGN)
"/="                         LEX_CONSUME_OPERATOR(TOK_DIV_ASSIGN)
"%="                         LEX_CONSUME_OPERATOR(TOK_MOD_ASSIGN)
"+="                         LEX_CONSUME_OPERATOR(TOK_PLUS_ASSIGN)
"-="                         LEX_CONSUME_OPERATOR(TOK_MINUS_ASSIGN)
">>="                        LEX_CONSUME_OPERATOR(TOK_SHR_ASSIGN)
"<<="                        LEX_CONSUME_OPERATOR(TOK_SHL_ASSIGN)
"&="                         LEX_CONSUME_OPERATOR(TOK_BIT_AND_ASSIGN)
"|="                         LEX_CONSUME_OPERATOR(TOK_BIT_OR_ASSIGN)
"^="                         LEX_CONSUME_OPERATOR(TOK_XOR_ASSIGN)
"&&"                         LEX_CONSUME_OPERATOR(TOK_AND)
"||"                         LEX_CONSUME_OPERATOR(TOK_OR)
"&"                          LEX_CONSUME_OPERATOR(TOK_BIT_AND)
"|"                          LEX_CONSUME_OPERATOR(TOK_BIT_OR)
"=="                         LEX_CONSUME_OPERATOR(TOK_EQ)
"!="                         LEX_CONSUME_OPERATOR(TOK_NEQ)
">"                          LEX_CONSUME_OPERATOR(TOK_GT)
"<"                          LEX_CONSUME_OPERATOR(TOK_LT)
">="                         LEX_CONSUME_OPERATOR(TOK_GE)
"<="                         LEX_CONSUME_OPERATOR(TOK_LE)
"<<"                         LEX_CONSUME_OPERATOR(TOK_SHL)
">>"                         LEX_CONSUME_OPERATOR(TOK_SHR)
"+"                          LEX_CONSUME_OPERATOR(TOK_PLUS)
"-"                          LEX_CONSUME_OPERATOR(TOK_MINUS)
"*"                          LEX_CONSUME_OPERATOR(TOK_STAR)
"/"                          LEX_CONSUME_OPERATOR(TOK_SLASH)
"%"                          LEX_CONSUME_OPERATOR(TOK_MOD)
"++"                         LEX_CONSUME_OPERATOR(TOK_INC)
"--"                         LEX_CONSUME_OPERATOR(TOK_DEC)
"."                          LEX_CONSUME_OPERATOR(TOK_DOT)
","                          LEX_CONSUME_OPERATOR(TOK_COMMA)
";"                          LEX_CONSUME_OPERATOR(TOK_SEMICOLON)
"!"                          LEX_CONSUME_OPERATOR(TOK_NOT)
"^"                          LEX_CONSUME_OPERATOR(TOK_XOR)
"["                          LEX_CONSUME_OPERATOR(TOK_OPEN_BOX_BRACKET)
"]"                          LEX_CONSUME_OPERATOR(TOK_CLOSE_BOX_BRACKET)
"("                          LEX_CONSUME_OPERATOR(TOK_OPEN_PAREN)
")"                          LEX_CONSUME_OPERATOR(TOK_CLOSE_PAREN)
"{"                          LEX_CONSUME_OPERATOR(TOK_OPEN_CURLY_BRACKET)
"}"                          LEX_CONSUME_OPERATOR(TOK_CLOSE_CURLY_BRACKET)

[_a-zA-Z][_a-zA-Z0-9]*       LEX_CONSUME_WORD(TOK_SYMBOL)

.                            { fprintf(stderr, "Illegal token `%s`\n", yytext);
                               fflush (stderr);
                               __builtin_trap();
                             }

%%

#pragma GCC diagnostic pop