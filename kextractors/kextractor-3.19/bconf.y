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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lkc.h"

#define printd(mask, fmt...) if (cdebug & (mask)) printf(fmt)

#define PRINTD		0x0001
#define DEBUG_PARSE	0x0002

extern int cdebug;

extern char *filename;
extern int bconflineno;

extern int bconflex(void);

#define MAX_IF_DEPTH 100

static struct expr *current_expr = NULL;
static struct expr *if_stack[MAX_IF_DEPTH];
static int if_index = 0;


struct linked_list {
  struct linked_list *next;
  void *data;
};


void
add_config_var(char *var, enum symbol_type stype, char *def, struct linked_list *dep_list)
{
  struct symbol *sym = sym_lookup(var, 0);
  sym->flags |= SYMBOL_OPTIONAL;
  menu_add_entry(sym);
  printd(DEBUG_PARSE, "%s:%d:config %s\n", filename, bconflineno, var);
  menu_set_type(stype);
  printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
         filename, bconflineno,
         stype);
  if (NULL != def) {
    menu_add_symbol(P_DEFAULT, sym_lookup(def, 0), NULL);
    printd(DEBUG_PARSE, "%s:%d:default\n",
           filename, bconflineno);
  }
  for (; NULL != dep_list; dep_list = dep_list->next) {
    menu_add_dep(expr_alloc_symbol(sym_lookup((char *) dep_list->data, 0)));
    printd(DEBUG_PARSE, "%s:%d:depends on %s\n", filename, bconflineno, dep_list->data);
  }
  menu_end_entry();
  printd(DEBUG_PARSE, "%s:%d:endconfig\n", filename, bconflineno);
}

static void
enter_if_branch(struct expr *expr)
{
  if (if_index >= MAX_IF_DEPTH)
    bconferror("MAX_IF_DEPTH exceeded");

  if_stack[if_index++] = current_expr;
  current_expr = expr;

	printd(DEBUG_PARSE, "%s:%d:if\n", filename, bconflineno);
	menu_add_entry(NULL);
	menu_add_dep(current_expr);
  menu_add_menu();
}

static void
enter_elif_branch(struct expr *expr)
{
  bconferror("not yet implemented");
}

static void
enter_else_branch()
{
  menu_end_menu();
  printd(DEBUG_PARSE, "%s:%d:endif\n", filename, bconflineno);

  current_expr = expr_alloc_one(E_NOT, expr_copy(current_expr));

	printd(DEBUG_PARSE, "%s:%d:if\n", filename, bconflineno);
	menu_add_entry(NULL);
	menu_add_dep(current_expr);
  menu_add_menu();
}

static void
exit_if_block(void)
{
  menu_end_menu();
  printd(DEBUG_PARSE, "%s:%d:endif\n", filename, bconflineno);

  current_expr = if_stack[--if_index];
}

%}

%union
{
	char *string;
  struct linked_list *list;
	struct expr *expr;
  struct symbol *symbol;
}

/* bash reserved words */
%token IF THEN ELSE ELIF FI

/* bconf reserved words */
%token MAINMENU_OPTION
%token MAINMENU_NAME
%token ENDMENU
%token HELP
%token READLN
%token COMMENT
%token DEFINE_BOOL
%token DEFINE_TRISTATE
%token BOOL
%token TRISTATE
%token DEP_TRISTATE
%token DEP_BOOL
%token DEP_MBOOL
%token DEFINE_INT
%token INT
%token DEFINE_HEX
%token HEX
%token DEFINE_STRING
%token STRING
%token CHOICE

/* bconf values */
%token <string> CONFIG_VAR WORD NUMBER

/* bconf literals */
%token <string> STRING_CONST TRISTATE_CONST

/* bconf conditional expressions */
%token TEST_STREQ TEST_STRNE TEST_N TEST_Z TEST_EQ TEST_NE TEST_GE TEST_GT
%token TEST_LE TEST_LT TEST_AND TEST_OR TEST_BANG

/* bash built-ins */
%token UNSET

/* bash statements appear on one line at a time, or followed by a semicolon */
%token NEWLINE

%type <string> tristate_value tristate_value_opt

%type <list> dep_list

%type <expr> conditional_expression term factor

%type <symbol> id


%%

inputunit:
    /* empty */
  | statement_list ;

statement_list:
    statement
  | statement_list statement ;

statement:
    /* empty statement */ NEWLINE
  | MAINMENU_OPTION WORD NEWLINE /* do nothing */
  | MAINMENU_NAME   STRING_CONST NEWLINE /* do nothing */
  | ENDMENU         NEWLINE /* do nothing */
  | COMMENT         STRING_CONST NEWLINE /* do nothing */
  | DEFINE_BOOL     WORD tristate_value NEWLINE
    {
      add_config_var($2, S_BOOLEAN, $3, NULL);
    }
  | DEFINE_TRISTATE WORD tristate_value NEWLINE
    {
      add_config_var($2, S_TRISTATE, $3, NULL);
    }
  | BOOL            STRING_CONST WORD tristate_value_opt NEWLINE
    {
      add_config_var($3, S_BOOLEAN, $4, NULL);
    }
  | TRISTATE        STRING_CONST WORD tristate_value_opt NEWLINE
    {
      add_config_var($3, S_TRISTATE, $4, NULL);
    }
  | DEP_TRISTATE    STRING_CONST WORD dep_list NEWLINE
    {
      add_config_var($3, S_TRISTATE, NULL, $4);
    }
  | DEP_BOOL        STRING_CONST WORD dep_list NEWLINE
    {
      add_config_var($3, S_BOOLEAN, NULL, $4);
    }
  | DEP_MBOOL       STRING_CONST WORD dep_list NEWLINE
    {
      add_config_var($3, S_BOOLEAN, NULL, $4);
    }
  | DEFINE_INT      WORD WORD NEWLINE
    {
      add_config_var($2, S_INT, $3, NULL);
    }
  | INT             STRING_CONST WORD WORD min_max_opt NEWLINE
    {
      // ignores min max option
      add_config_var($3, S_INT, $4, NULL);
    }
  | DEFINE_HEX      WORD WORD NEWLINE
    {
      add_config_var($2, S_HEX, $3, NULL);
    }
  | HEX             STRING_CONST WORD WORD NEWLINE
    {
      add_config_var($3, S_HEX, $4, NULL);
    }
  /* | DEFINE_STRING */
  | STRING          STRING_CONST WORD STRING_CONST NEWLINE
    {
      add_config_var($3, S_STRING, $4, NULL);
    }
  | STRING          STRING_CONST WORD WORD NEWLINE
    {
      add_config_var($3, S_STRING, $4, NULL);
    }
  | CHOICE          STRING_CONST STRING_CONST WORD NEWLINE
    {
      char *t;
      int entry;

      struct symbol *sym = sym_lookup(NULL, SYMBOL_CHOICE);
      sym->flags |= SYMBOL_AUTO;
      menu_add_entry(sym);
      menu_add_expr(P_CHOICE, NULL, NULL);
      printd(DEBUG_PARSE, "%s:%d:choice\n", filename, bconflineno);

      menu_add_menu();

      t = strtok($3, " \t\n");
      entry = 0;
      while (NULL != t) {
        if (1 == entry) { // choice string contains description/config var pairs
          struct symbol *sym = sym_lookup(t, 0);
          sym->flags |= SYMBOL_OPTIONAL;
          menu_add_entry(sym);
          printd(DEBUG_PARSE, "%s:%d:config %s\n", filename, bconflineno, t);
          menu_set_type(S_BOOLEAN);
          printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
                 filename, bconflineno,
                 S_BOOLEAN);
          menu_end_entry();
          printd(DEBUG_PARSE, "%s:%d:endconfig\n", filename, bconflineno);
        }
        t = strtok(NULL, " \t\n");
        entry = (entry + 1) % 2;
      }

      menu_end_menu();
      printd(DEBUG_PARSE, "%s:%d:endchoice\n", filename, bconflineno);
    }
  | UNSET           WORD NEWLINE /* do nothing */
  | if_block /* do nothing */
  ;

tristate_value:
    TRISTATE_CONST { $$ = $1; }
  | CONFIG_VAR { $$ = $1; }
  ;

tristate_value_opt:
    /* empty */ { $$ = NULL; }
  | tristate_value { $$ = $1; }
  ;

dep_list:
    tristate_value
    {
      $$ = malloc(sizeof(struct linked_list));
      $$->next = NULL;
      $$->data = $1;
    }
  | dep_list tristate_value
    {
      $$ = malloc(sizeof(struct linked_list));
      $$->next = $1;
      $$->data = $2;
    }
  ;

min_max_opt:
    /* empty */
  | WORD
  | WORD WORD
  ;

if_block: if_branch elif_opt else_opt FI NEWLINE { exit_if_block(); } ;

if_branch: IF conditional_expression { enter_if_branch($2); } NEWLINE THEN statement_list ;

elif_opt:
    /* empty */
  | elif_opt elif_branch
  ;

elif_branch: ELIF conditional_expression { enter_elif_branch($2); } NEWLINE THEN statement_list ;

else_opt:
    /* empty */
  | else_branch
  ;

else_branch: ELSE { enter_else_branch(); } statement_list ;

conditional_expression:
    term { $$ = $1; }
  | conditional_expression TEST_OR term { $$ = expr_alloc_two(E_OR, $1, $3); }
  ;

term:
    factor { $$ = $1; }
  | term TEST_AND factor { $$ = expr_alloc_two(E_AND, $1, $3); }
  ;

factor:
    id { $$ = expr_alloc_symbol($1); }
  | TEST_BANG factor { $$ = expr_alloc_one(E_NOT, $2); }
  | id TEST_STREQ id
    {
      if (strlen($3->name) == 1) {
        switch ($3->name[0]) {
        case 'y':
          // Fall through
        case 'm':
          $$ = expr_alloc_symbol($1);
          break;
        case 'n':
          $$ = expr_alloc_symbol($1);
          break;
        default:
          $$ = expr_alloc_comp(E_EQUAL, $1, $3);
          break;
        }
      } else {
        $$ = expr_alloc_comp(E_EQUAL, $1, $3);
      }
    }
  | id TEST_STRNE id
    {
      $$ = expr_alloc_comp(E_UNEQUAL, $1, $3);
    }
  | TEST_N id { $$ = expr_alloc_one(E_NOT, expr_alloc_symbol($2)); }
  | TEST_Z id { bconferror("not yet implemented"); }
  | NUMBER TEST_EQ NUMBER { bconferror("not yet implemented"); }
  | NUMBER TEST_NE NUMBER { bconferror("not yet implemented"); }
  | NUMBER TEST_GE NUMBER { bconferror("not yet implemented"); }
  | NUMBER TEST_GT NUMBER { bconferror("not yet implemented"); }
  | NUMBER TEST_LE NUMBER { bconferror("not yet implemented"); }
  | NUMBER TEST_LT NUMBER { bconferror("not yet implemented"); }
  ;

id:
    CONFIG_VAR { $$ = sym_lookup($1, 0); }
  | TRISTATE_CONST { $$ = sym_lookup($1, 0); }
  | STRING_CONST { $$ = sym_lookup($1, SYMBOL_CONST); }
  | NUMBER { $$ = sym_lookup($1, 0); }
  ;

%%

#include "bconf.lex.c"

char *filename;

bconf_parse(char *file)
{
	struct symbol *sym;
	int i;

#ifdef TRACE_BISON
  yydebug = 1;
#endif //TRACE_BISON
#ifdef TRACE_ZCONF
  cdebug = 2;
#endif //TRACE_ZCONF
  bconfin = fopen(file, "r");
  filename = file;
  bconflineno = 1;

	sym_init();
	_menu_init();
	modules_sym = sym_lookup(NULL, 0);
	modules_sym->type = S_BOOLEAN;
	modules_sym->flags |= SYMBOL_AUTO;
	rootmenu.prompt = menu_add_prompt(P_MENU, "Linux Kernel Configuration", NULL);

	/* if (getenv("ZCONF_DEBUG")) */
	/* 	zconfdebug = 1; */
  bconfparse();
	if (!modules_sym->prop) {
		struct property *prop;

		prop = prop_alloc(P_DEFAULT, modules_sym);
		prop->expr = expr_alloc_symbol(sym_lookup("MODULES", 0));
	}

	rootmenu.prompt->text = _(rootmenu.prompt->text);
	rootmenu.prompt->text = sym_expand_string_value(rootmenu.prompt->text);

	menu_finalize(&rootmenu);
	/* for_all_symbols(i, sym) { */
	/* 	if (sym_check_deps(sym)) */
  /*     exit(1); */
  /* } */
	/* sym_set_change_count(1); */
}

bconf_test_lexer(char *file)
{
  int t;

  bconfin = fopen(file, "r");
  filename = file;
  bconflineno = 1;
  while (t = bconflex()) {
    printf("%s: %s\n", yytname[t - 255], bconftext);
  }
}

bconferror(char *msg) {
  fprintf(stderr, "error:%s:%d: %s\n", filename, bconflineno, msg);
  exit(1);
}
