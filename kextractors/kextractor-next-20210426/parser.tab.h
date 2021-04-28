/* A Bison parser, made by GNU Bison 3.5.1.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2020 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Undocumented macros, especially those whose name start with YY_,
   are private implementation details.  Do not rely on them.  */

#ifndef YY_YY_SCRIPTS_KCONFIG_PARSER_TAB_H_INCLUDED
# define YY_YY_SCRIPTS_KCONFIG_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    T_HELPTEXT = 258,
    T_WORD = 259,
    T_WORD_QUOTE = 260,
    T_BOOL = 261,
    T_CHOICE = 262,
    T_CLOSE_PAREN = 263,
    T_COLON_EQUAL = 264,
    T_COMMENT = 265,
    T_CONFIG = 266,
    T_DEFAULT = 267,
    T_DEF_BOOL = 268,
    T_DEF_TRISTATE = 269,
    T_DEPENDS = 270,
    T_ENDCHOICE = 271,
    T_ENDIF = 272,
    T_ENDMENU = 273,
    T_HELP = 274,
    T_HEX = 275,
    T_IF = 276,
    T_IMPLY = 277,
    T_INT = 278,
    T_MAINMENU = 279,
    T_MENU = 280,
    T_MENUCONFIG = 281,
    T_MODULES = 282,
    T_ON = 283,
    T_OPEN_PAREN = 284,
    T_OPTIONAL = 285,
    T_PLUS_EQUAL = 286,
    T_PROMPT = 287,
    T_RANGE = 288,
    T_SELECT = 289,
    T_SOURCE = 290,
    T_STRING = 291,
    T_TRISTATE = 292,
    T_VISIBLE = 293,
    T_EOL = 294,
    T_ASSIGN_VAL = 295,
    T_OR = 296,
    T_AND = 297,
    T_EQUAL = 298,
    T_UNEQUAL = 299,
    T_LESS = 300,
    T_LESS_EQUAL = 301,
    T_GREATER = 302,
    T_GREATER_EQUAL = 303,
    T_NOT = 304
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{

	char *string;
	struct symbol *symbol;
	struct expr *expr;
	struct menu *menu;
	enum symbol_type type;
	enum variable_flavor flavor;


};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_SCRIPTS_KCONFIG_PARSER_TAB_H_INCLUDED  */
