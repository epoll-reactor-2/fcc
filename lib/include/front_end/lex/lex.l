%{
#include "front_end/lex/tok.h"

int yycolumn = 1;
extern const char *path;

#define YY_USER_ACTION                                                   \
  lex_lineno = prev_yylineno;                                            \
  lex_colno = yycolumn;                                                  \
  if (yylineno == prev_yylineno) {                                       \
      yycolumn += yyleng;                                                \
  } else {                                                               \
    for (yycolumn = 1; yytext[yyleng - yycolumn] != '\n'; ++yycolumn) {} \
    prev_yylineno = yylineno;                                            \
  }

#define LEX_CONSUME_WORD(tok_type) do {                                  \
    tok_t t = {                                                          \
        .data = strdup(yytext),                                          \
        .type = tok_type,                                                \
        .line_no = lex_lineno,                                           \
        .col_no = lex_colno                                              \
    };                                                                   \
    lex_get_token(&t);                                                   \
} while (0);

extern void lex_get_token(tok_t *tok);

%}
%option noyywrap nounput noinput
%option yylineno

%%
 int lex_lineno, lex_colno;
 int prev_yylineno = yylineno;
   
 /* Requirement [2.3.1] */
\/\/.*\n
 /* Requirement [2.3.2] */
\/\*.*\*\/
 /* Ignore whitespace. */
" "|"\a"|"\b"|"\f"|"\n"|"\r"|"\t"|"\v"

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

"="                          LEX_CONSUME_WORD(TOK_ASSIGN)
"/="                         LEX_CONSUME_WORD(TOK_DIV_ASSIGN)
"%="                         LEX_CONSUME_WORD(TOK_MOD_ASSIGN)
"+="                         LEX_CONSUME_WORD(TOK_PLUS_ASSIGN)
"-="                         LEX_CONSUME_WORD(TOK_MINUS_ASSIGN)
">>="                        LEX_CONSUME_WORD(TOK_SHR_ASSIGN)
"<<="                        LEX_CONSUME_WORD(TOK_SHL_ASSIGN)
"&="                         LEX_CONSUME_WORD(TOK_BIT_AND_ASSIGN)
"|="                         LEX_CONSUME_WORD(TOK_BIT_OR_ASSIGN)
"^="                         LEX_CONSUME_WORD(TOK_XOR_ASSIGN)
"&&"                         LEX_CONSUME_WORD(TOK_AND)
"||"                         LEX_CONSUME_WORD(TOK_OR)
"&"                          LEX_CONSUME_WORD(TOK_BIT_AND)
"|"                          LEX_CONSUME_WORD(TOK_BIT_OR)
"=="                         LEX_CONSUME_WORD(TOK_EQ)
"!="                         LEX_CONSUME_WORD(TOK_NEQ)
">"                          LEX_CONSUME_WORD(TOK_GT)
"<"                          LEX_CONSUME_WORD(TOK_LT)
">="                         LEX_CONSUME_WORD(TOK_GE)
"<="                         LEX_CONSUME_WORD(TOK_LE)
"<<"                         LEX_CONSUME_WORD(TOK_SHL)
">>"                         LEX_CONSUME_WORD(TOK_SHR)
"+"                          LEX_CONSUME_WORD(TOK_PLUS)
"-"                          LEX_CONSUME_WORD(TOK_MINUS)
"*"                          LEX_CONSUME_WORD(TOK_STAR)
"/"                          LEX_CONSUME_WORD(TOK_SLASH)
"%"                          LEX_CONSUME_WORD(TOK_MOD)
"++"                         LEX_CONSUME_WORD(TOK_INC)
"--"                         LEX_CONSUME_WORD(TOK_DEC)
"."                          LEX_CONSUME_WORD(TOK_DOT)
","                          LEX_CONSUME_WORD(TOK_COMMA)
";"                          LEX_CONSUME_WORD(TOK_SEMICOLON)
"!"                          LEX_CONSUME_WORD(TOK_NOT)
"["                          LEX_CONSUME_WORD(TOK_OPEN_BOX_BRACKET)
"]"                          LEX_CONSUME_WORD(TOK_CLOSE_BOX_BRACKET)
"("                          LEX_CONSUME_WORD(TOK_OPEN_PAREN)
")"                          LEX_CONSUME_WORD(TOK_CLOSE_PAREN)
"{"                          LEX_CONSUME_WORD(TOK_OPEN_CURLY_BRACKET)
"}"                          LEX_CONSUME_WORD(TOK_CLOSE_CURLY_BRACKET)

[_a-zA-Z][_a-zA-Z0-9]*       LEX_CONSUME_WORD(TOK_SYMBOL)

.                            { fprintf(stderr, "Illegal token `%s`\n", yytext);
                               fflush (stderr);
                               __builtin_trap();
                             }

%%
