%option prefix="bconf"
%option noyywrap
%option yylineno

%{
/* Kmax                                                                   */
/* Copyright (C) 2012-2015 Paul Gazzillo                                  */
/*                                                                        */
/* This program is free software: you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation, either version 3 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#define MAX_SOURCE_DEPTH 20

struct source_file {
  YY_BUFFER_STATE buffer;
  char *name;
  int lineno;
};

static struct source_file source_stack[MAX_SOURCE_DEPTH];
static int source_index = 0;

extern char *filename;
%}

WORD [a-zA-Z_/\.][0-9a-zA-Z_/\.]*
WORD_BROKEN [a-zA-Z_/\.][0-9a-zA-Z_/\.\-]*
FULL_WORD [0-9a-zA-Z_/\.\-]+

FILENAME [0-9a-zA-Z_\-/\.]+

/* Tristate constants */
TRISTATE_CONST  y|n|m

/* Strings */
SIMPLE_ESCAPE   [abefnrtv\'\"?\\]
OCTAL_ESCAPE    [0-7]{1,3}
HEX_ESCAPE      "x"[0-9a-fA-F]+
ESCAPE_SEQUENCE [\\]({SIMPLE_ESCAPE}|{OCTAL_ESCAPE}|{HEX_ESCAPE})
STRING_CHAR_D   [^\"\\\n]|{ESCAPE_SEQUENCE}|{CONTINUATION}
STRING_CHAR_S   [^\'\\\n]|{ESCAPE_SEQUENCE}|{CONTINUATION}

/* Whitespace and newlines */
NEWLINE_CHAR \r|\n|\r\n
NEWLINE      {NEWLINE_CHAR}|"#"[^\r\n]*{NEWLINE_CHAR}
TAB          [\011]
CONTINUATION "\\\n"
WHITESPACE   ([ ]|{TAB})+|{CONTINUATION}

/* separate lexing for test conditions */
%x IN_TEST

/* include other config files */
%x IN_SOURCE
%x OPEN_SOURCE

%%

<INITIAL>{
source BEGIN(IN_SOURCE);

if     return IF;
then   return THEN;
else   return ELSE;
elif   return ELIF;
fi     return FI;
unset  return UNSET;

mainmenu_option return MAINMENU_OPTION;
mainmenu_name   return MAINMENU_NAME;
endmenu         return ENDMENU;
help            return HELP;
readln          return READLN;
comment         return COMMENT;
define_bool     return DEFINE_BOOL;
define_tristate return DEFINE_TRISTATE;
bool            return BOOL;
tristate        return TRISTATE;
dep_tristate    return DEP_TRISTATE;
dep_bool        return DEP_BOOL;
dep_mbool       return DEP_MBOOL;
define_int      return DEFINE_INT;
int             return INT;
define_hex      return DEFINE_HEX;
hex             return HEX;
define_string   return DEFINE_STRING;
string          return STRING;
choice          return CHOICE;

"[["|"]]"       { fprintf(stderr, "error:%s:%d: \"%s\"ksh-style conditionals unsupported\n", filename, yylineno, yytext); exit(1); }

"["             BEGIN(IN_TEST);

{TRISTATE_CONST} {
  switch (yytext[0]) {
  case 'y': yylval.string = "y"; break;
  case 'n': yylval.string = "n"; break;
  case 'm': yylval.string = "m"; break;
  default:
    fprintf(stderr, "lexer error:%s:%d: incorrect tristate const\n", \
            filename, yylineno);
    break;
  }

  return TRISTATE_CONST;
}

\"({STRING_CHAR_D})*\"|\'({STRING_CHAR_S})*\' {
  char *c;
  yytext[yyleng-1] = '\0'; yytext += 1;
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  for (c = yylval.string; *c != '\0'; c++) {
    if (*c == '\\' && *(c + 1) == '\n') {
      *c = ' ';
      *(c+1) = ' ';
    }
  }
  return STRING_CONST;
}

${WORD} {
  yytext += 1;
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  return CONFIG_VAR;
}

{FULL_WORD} {
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  return WORD;
}
}

<IN_SOURCE>{
{FILENAME} {
  if (source_index >= MAX_SOURCE_DEPTH) {
    fprintf(stderr, "fatal error: maximum depth of source includes, %d, "
            "reached.  Set the\nMAX_SOURCE_DEPTH macro to a bigger value.\n",
            MAX_SOURCE_DEPTH);
    exit(1);
  }
  source_stack[source_index].buffer = YY_CURRENT_BUFFER;
  source_stack[source_index].name = filename;
  source_stack[source_index].lineno = yylineno;
  source_index++;
  filename = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(filename, yytext, strlen(yytext) + 1);
  BEGIN(OPEN_SOURCE);
}
}

<OPEN_SOURCE>{
;|{NEWLINE} {
  yyin = fopen(filename, "r");
  if (!yyin) {
    fprintf(stderr, "lexer error:%s:%d: file not found, \"%s\"\n",
            source_stack[source_index - 1].name, yylineno, filename);
    exit(1);
  }
  yy_switch_to_buffer(yy_create_buffer(yyin, YY_BUF_SIZE));
  yylineno = 1;
  BEGIN(INITIAL);
#ifdef TRACE_LEXER
  fprintf(stderr, "trace:%s:%d: entering %s, depth %d\n", source_stack[source_index-1].name, yylineno, filename, source_index);
#endif //TRACE_LEXER
}
}

<<EOF>> {
#ifdef TRACE_LEXER
fprintf(stderr, "trace:%s:%d: leaving\n", filename, yylineno);
#endif //TRACE_LEXER
if (--source_index < 0) {
  yyterminate();
} else {
  yy_delete_buffer(YY_CURRENT_BUFFER);
  yy_switch_to_buffer(source_stack[source_index].buffer);
  free(filename);
  filename = source_stack[source_index].name;
  yylineno = source_stack[source_index].lineno + 1;  // plus one for the "source filename\n" command
}
}

<IN_TEST>{
"]"             BEGIN(INITIAL);
"="             return TEST_STREQ;
"!="            return TEST_STRNE;
"-n"            return TEST_N;
"-z"            return TEST_Z;
"-eq"           return TEST_EQ;
"-ne"           return TEST_NE;
"-ge"           return TEST_GE;
"-gt"           return TEST_GT;
"-le"           return TEST_LE;
"-lt"           return TEST_LT;
"-a"            return TEST_AND;
"-o"            return TEST_OR;
"!"             return TEST_BANG;
\"{TRISTATE_CONST}\" {
  yytext[yyleng-1] = '\0'; yytext += 1;
  switch (yytext[0]) {
  case 'y': yylval.string = "y"; break;
  case 'n': yylval.string = "n"; break;
  case 'm': yylval.string = "m"; break;
  default:
    fprintf(stderr, "lexer error:%s:%d: incorrect tristate const\n", \
            filename, yylineno);
    break;
  }
  return TRISTATE_CONST;
}
\"${WORD}\" {
  yytext[yyleng-1] = '\0'; yytext += 2;
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  return CONFIG_VAR;
}
\"{WORD}\" {
  yytext[yyleng-1] = '\0'; yytext += 2;
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  return STRING_CONST;
}
\"[0-9]+\" {
  yytext[yyleng-1] = '\0'; yytext += 1;
  yylval.string = malloc(sizeof(char) * (strlen(yytext) + 1));
  strncpy(yylval.string, yytext, strlen(yytext) + 1);
  return NUMBER;
}
}

<INITIAL,IN_TEST,IN_SOURCE,OPEN_SOURCE>{
{WHITESPACE}+
}

<INITIAL>{
({NEWLINE}|;)+  return NEWLINE;
. { fprintf(stderr, "lexer error:%s:%d: %s\n", filename, yylineno, yytext); exit(1); }
}

<IN_TEST>{
. { fprintf(stderr, "lexer error:%s:%d: %s\n", filename, yylineno, yytext); exit(1); }
}
