/* grammar.lex - Language acceptable tokens specification.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

%{

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

/* Don't include quotes to match. Lex has no lookahead in their regular
   expression engine, so we emulate it by hand. */
#define LEX_CONSUME_QUOTED_LITERAL(tok_type) do {                        \
    ++yytext;                                                            \
    struct token t = {                                                   \
        .data    = strdup(yytext),                                       \
        .type    = tok_type,                                             \
        .line_no = lex_lineno,                                           \
        .col_no  = lex_colno                                             \
    };                                                                   \
    --yytext;                                                            \
    size_t data_len = strlen(t.data);                                    \
    if (data_len > 0)                                                    \
        t.data[data_len - 1] = '\0';                                     \
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
\"([^\"\\]*(\\.[^\"\\]*)*)\" LEX_CONSUME_QUOTED_LITERAL(TOK_STRING_LITERAL)
\'.\'                        LEX_CONSUME_QUOTED_LITERAL(TOK_CHAR_LITERAL)

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
":"                          LEX_CONSUME_OPERATOR(TOK_COLON)
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