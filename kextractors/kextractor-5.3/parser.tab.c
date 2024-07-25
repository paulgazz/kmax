/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
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
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */


#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "lkc.h"

#define printd(mask, fmt...) if (cdebug & (mask)) printf(fmt)

#define PRINTD		0x0001
#define DEBUG_PARSE	0x0002

int cdebug = PRINTD;

static void yyerror(const char *err);
static void zconfprint(const char *err, ...);
static void zconf_error(const char *err, ...);
static bool zconf_endtoken(const char *tokenname,
			   const char *expected_tokenname);

struct symbol *symbol_hash[SYMBOL_HASHSIZE];

static struct menu *current_menu, *current_entry;



# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif


/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    T_HELPTEXT = 258,              /* T_HELPTEXT  */
    T_WORD = 259,                  /* T_WORD  */
    T_WORD_QUOTE = 260,            /* T_WORD_QUOTE  */
    T_ALLNOCONFIG_Y = 261,         /* T_ALLNOCONFIG_Y  */
    T_BOOL = 262,                  /* T_BOOL  */
    T_CHOICE = 263,                /* T_CHOICE  */
    T_CLOSE_PAREN = 264,           /* T_CLOSE_PAREN  */
    T_COLON_EQUAL = 265,           /* T_COLON_EQUAL  */
    T_COMMENT = 266,               /* T_COMMENT  */
    T_CONFIG = 267,                /* T_CONFIG  */
    T_DEFAULT = 268,               /* T_DEFAULT  */
    T_DEFCONFIG_LIST = 269,        /* T_DEFCONFIG_LIST  */
    T_DEF_BOOL = 270,              /* T_DEF_BOOL  */
    T_DEF_TRISTATE = 271,          /* T_DEF_TRISTATE  */
    T_DEPENDS = 272,               /* T_DEPENDS  */
    T_ENDCHOICE = 273,             /* T_ENDCHOICE  */
    T_ENDIF = 274,                 /* T_ENDIF  */
    T_ENDMENU = 275,               /* T_ENDMENU  */
    T_HELP = 276,                  /* T_HELP  */
    T_HEX = 277,                   /* T_HEX  */
    T_IF = 278,                    /* T_IF  */
    T_IMPLY = 279,                 /* T_IMPLY  */
    T_INT = 280,                   /* T_INT  */
    T_MAINMENU = 281,              /* T_MAINMENU  */
    T_MENU = 282,                  /* T_MENU  */
    T_MENUCONFIG = 283,            /* T_MENUCONFIG  */
    T_MODULES = 284,               /* T_MODULES  */
    T_ON = 285,                    /* T_ON  */
    T_OPEN_PAREN = 286,            /* T_OPEN_PAREN  */
    T_OPTION = 287,                /* T_OPTION  */
    T_OPTIONAL = 288,              /* T_OPTIONAL  */
    T_PLUS_EQUAL = 289,            /* T_PLUS_EQUAL  */
    T_PROMPT = 290,                /* T_PROMPT  */
    T_RANGE = 291,                 /* T_RANGE  */
    T_SELECT = 292,                /* T_SELECT  */
    T_SOURCE = 293,                /* T_SOURCE  */
    T_STRING = 294,                /* T_STRING  */
    T_TRISTATE = 295,              /* T_TRISTATE  */
    T_VISIBLE = 296,               /* T_VISIBLE  */
    T_EOL = 297,                   /* T_EOL  */
    T_ASSIGN_VAL = 298,            /* T_ASSIGN_VAL  */
    T_OR = 299,                    /* T_OR  */
    T_AND = 300,                   /* T_AND  */
    T_EQUAL = 301,                 /* T_EQUAL  */
    T_UNEQUAL = 302,               /* T_UNEQUAL  */
    T_LESS = 303,                  /* T_LESS  */
    T_LESS_EQUAL = 304,            /* T_LESS_EQUAL  */
    T_GREATER = 305,               /* T_GREATER  */
    T_GREATER_EQUAL = 306,         /* T_GREATER_EQUAL  */
    T_NOT = 307                    /* T_NOT  */
  };
  typedef enum yytokentype yytoken_kind_t;
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



/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_T_HELPTEXT = 3,                 /* T_HELPTEXT  */
  YYSYMBOL_T_WORD = 4,                     /* T_WORD  */
  YYSYMBOL_T_WORD_QUOTE = 5,               /* T_WORD_QUOTE  */
  YYSYMBOL_T_ALLNOCONFIG_Y = 6,            /* T_ALLNOCONFIG_Y  */
  YYSYMBOL_T_BOOL = 7,                     /* T_BOOL  */
  YYSYMBOL_T_CHOICE = 8,                   /* T_CHOICE  */
  YYSYMBOL_T_CLOSE_PAREN = 9,              /* T_CLOSE_PAREN  */
  YYSYMBOL_T_COLON_EQUAL = 10,             /* T_COLON_EQUAL  */
  YYSYMBOL_T_COMMENT = 11,                 /* T_COMMENT  */
  YYSYMBOL_T_CONFIG = 12,                  /* T_CONFIG  */
  YYSYMBOL_T_DEFAULT = 13,                 /* T_DEFAULT  */
  YYSYMBOL_T_DEFCONFIG_LIST = 14,          /* T_DEFCONFIG_LIST  */
  YYSYMBOL_T_DEF_BOOL = 15,                /* T_DEF_BOOL  */
  YYSYMBOL_T_DEF_TRISTATE = 16,            /* T_DEF_TRISTATE  */
  YYSYMBOL_T_DEPENDS = 17,                 /* T_DEPENDS  */
  YYSYMBOL_T_ENDCHOICE = 18,               /* T_ENDCHOICE  */
  YYSYMBOL_T_ENDIF = 19,                   /* T_ENDIF  */
  YYSYMBOL_T_ENDMENU = 20,                 /* T_ENDMENU  */
  YYSYMBOL_T_HELP = 21,                    /* T_HELP  */
  YYSYMBOL_T_HEX = 22,                     /* T_HEX  */
  YYSYMBOL_T_IF = 23,                      /* T_IF  */
  YYSYMBOL_T_IMPLY = 24,                   /* T_IMPLY  */
  YYSYMBOL_T_INT = 25,                     /* T_INT  */
  YYSYMBOL_T_MAINMENU = 26,                /* T_MAINMENU  */
  YYSYMBOL_T_MENU = 27,                    /* T_MENU  */
  YYSYMBOL_T_MENUCONFIG = 28,              /* T_MENUCONFIG  */
  YYSYMBOL_T_MODULES = 29,                 /* T_MODULES  */
  YYSYMBOL_T_ON = 30,                      /* T_ON  */
  YYSYMBOL_T_OPEN_PAREN = 31,              /* T_OPEN_PAREN  */
  YYSYMBOL_T_OPTION = 32,                  /* T_OPTION  */
  YYSYMBOL_T_OPTIONAL = 33,                /* T_OPTIONAL  */
  YYSYMBOL_T_PLUS_EQUAL = 34,              /* T_PLUS_EQUAL  */
  YYSYMBOL_T_PROMPT = 35,                  /* T_PROMPT  */
  YYSYMBOL_T_RANGE = 36,                   /* T_RANGE  */
  YYSYMBOL_T_SELECT = 37,                  /* T_SELECT  */
  YYSYMBOL_T_SOURCE = 38,                  /* T_SOURCE  */
  YYSYMBOL_T_STRING = 39,                  /* T_STRING  */
  YYSYMBOL_T_TRISTATE = 40,                /* T_TRISTATE  */
  YYSYMBOL_T_VISIBLE = 41,                 /* T_VISIBLE  */
  YYSYMBOL_T_EOL = 42,                     /* T_EOL  */
  YYSYMBOL_T_ASSIGN_VAL = 43,              /* T_ASSIGN_VAL  */
  YYSYMBOL_T_OR = 44,                      /* T_OR  */
  YYSYMBOL_T_AND = 45,                     /* T_AND  */
  YYSYMBOL_T_EQUAL = 46,                   /* T_EQUAL  */
  YYSYMBOL_T_UNEQUAL = 47,                 /* T_UNEQUAL  */
  YYSYMBOL_T_LESS = 48,                    /* T_LESS  */
  YYSYMBOL_T_LESS_EQUAL = 49,              /* T_LESS_EQUAL  */
  YYSYMBOL_T_GREATER = 50,                 /* T_GREATER  */
  YYSYMBOL_T_GREATER_EQUAL = 51,           /* T_GREATER_EQUAL  */
  YYSYMBOL_T_NOT = 52,                     /* T_NOT  */
  YYSYMBOL_YYACCEPT = 53,                  /* $accept  */
  YYSYMBOL_input = 54,                     /* input  */
  YYSYMBOL_mainmenu_stmt = 55,             /* mainmenu_stmt  */
  YYSYMBOL_stmt_list = 56,                 /* stmt_list  */
  YYSYMBOL_common_stmt = 57,               /* common_stmt  */
  YYSYMBOL_config_entry_start = 58,        /* config_entry_start  */
  YYSYMBOL_config_stmt = 59,               /* config_stmt  */
  YYSYMBOL_menuconfig_entry_start = 60,    /* menuconfig_entry_start  */
  YYSYMBOL_menuconfig_stmt = 61,           /* menuconfig_stmt  */
  YYSYMBOL_config_option_list = 62,        /* config_option_list  */
  YYSYMBOL_config_option = 63,             /* config_option  */
  YYSYMBOL_choice = 64,                    /* choice  */
  YYSYMBOL_choice_entry = 65,              /* choice_entry  */
  YYSYMBOL_choice_end = 66,                /* choice_end  */
  YYSYMBOL_choice_stmt = 67,               /* choice_stmt  */
  YYSYMBOL_choice_option_list = 68,        /* choice_option_list  */
  YYSYMBOL_choice_option = 69,             /* choice_option  */
  YYSYMBOL_type = 70,                      /* type  */
  YYSYMBOL_logic_type = 71,                /* logic_type  */
  YYSYMBOL_default = 72,                   /* default  */
  YYSYMBOL_choice_block = 73,              /* choice_block  */
  YYSYMBOL_if_entry = 74,                  /* if_entry  */
  YYSYMBOL_if_end = 75,                    /* if_end  */
  YYSYMBOL_if_stmt = 76,                   /* if_stmt  */
  YYSYMBOL_menu = 77,                      /* menu  */
  YYSYMBOL_menu_entry = 78,                /* menu_entry  */
  YYSYMBOL_menu_end = 79,                  /* menu_end  */
  YYSYMBOL_menu_stmt = 80,                 /* menu_stmt  */
  YYSYMBOL_menu_option_list = 81,          /* menu_option_list  */
  YYSYMBOL_source_stmt = 82,               /* source_stmt  */
  YYSYMBOL_comment = 83,                   /* comment  */
  YYSYMBOL_comment_stmt = 84,              /* comment_stmt  */
  YYSYMBOL_comment_option_list = 85,       /* comment_option_list  */
  YYSYMBOL_help_start = 86,                /* help_start  */
  YYSYMBOL_help = 87,                      /* help  */
  YYSYMBOL_depends = 88,                   /* depends  */
  YYSYMBOL_visible = 89,                   /* visible  */
  YYSYMBOL_prompt_stmt_opt = 90,           /* prompt_stmt_opt  */
  YYSYMBOL_prompt = 91,                    /* prompt  */
  YYSYMBOL_end = 92,                       /* end  */
  YYSYMBOL_if_expr = 93,                   /* if_expr  */
  YYSYMBOL_expr = 94,                      /* expr  */
  YYSYMBOL_nonconst_symbol = 95,           /* nonconst_symbol  */
  YYSYMBOL_symbol = 96,                    /* symbol  */
  YYSYMBOL_word_opt = 97,                  /* word_opt  */
  YYSYMBOL_assignment_stmt = 98,           /* assignment_stmt  */
  YYSYMBOL_assign_op = 99,                 /* assign_op  */
  YYSYMBOL_assign_val = 100                /* assign_val  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_uint8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if !defined yyoverflow

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* !defined yyoverflow */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  8
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   187

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  53
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  48
/* YYNRULES -- Number of rules.  */
#define YYNRULES  106
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  186

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   307


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   112,   112,   112,   116,   121,   123,   124,   125,   126,
     127,   131,   132,   133,   134,   135,   136,   141,   148,   153,
     160,   169,   171,   172,   173,   176,   184,   190,   200,   206,
     212,   218,   223,   228,   235,   245,   250,   258,   261,   263,
     264,   265,   268,   274,   281,   287,   295,   296,   297,   298,
     301,   302,   305,   306,   307,   309,   311,   316,   324,   332,
     337,   344,   349,   357,   360,   362,   363,   366,   375,   382,
     385,   387,   392,   398,   416,   423,   430,   432,   437,   438,
     441,   442,   443,   446,   447,   450,   451,   452,   453,   454,
     455,   456,   457,   458,   459,   460,   464,   466,   467,   470,
     471,   475,   478,   479,   480,   484,   485
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "T_HELPTEXT", "T_WORD",
  "T_WORD_QUOTE", "T_ALLNOCONFIG_Y", "T_BOOL", "T_CHOICE", "T_CLOSE_PAREN",
  "T_COLON_EQUAL", "T_COMMENT", "T_CONFIG", "T_DEFAULT",
  "T_DEFCONFIG_LIST", "T_DEF_BOOL", "T_DEF_TRISTATE", "T_DEPENDS",
  "T_ENDCHOICE", "T_ENDIF", "T_ENDMENU", "T_HELP", "T_HEX", "T_IF",
  "T_IMPLY", "T_INT", "T_MAINMENU", "T_MENU", "T_MENUCONFIG", "T_MODULES",
  "T_ON", "T_OPEN_PAREN", "T_OPTION", "T_OPTIONAL", "T_PLUS_EQUAL",
  "T_PROMPT", "T_RANGE", "T_SELECT", "T_SOURCE", "T_STRING", "T_TRISTATE",
  "T_VISIBLE", "T_EOL", "T_ASSIGN_VAL", "T_OR", "T_AND", "T_EQUAL",
  "T_UNEQUAL", "T_LESS", "T_LESS_EQUAL", "T_GREATER", "T_GREATER_EQUAL",
  "T_NOT", "$accept", "input", "mainmenu_stmt", "stmt_list", "common_stmt",
  "config_entry_start", "config_stmt", "menuconfig_entry_start",
  "menuconfig_stmt", "config_option_list", "config_option", "choice",
  "choice_entry", "choice_end", "choice_stmt", "choice_option_list",
  "choice_option", "type", "logic_type", "default", "choice_block",
  "if_entry", "if_end", "if_stmt", "menu", "menu_entry", "menu_end",
  "menu_stmt", "menu_option_list", "source_stmt", "comment",
  "comment_stmt", "comment_option_list", "help_start", "help", "depends",
  "visible", "prompt_stmt_opt", "prompt", "end", "if_expr", "expr",
  "nonconst_symbol", "symbol", "word_opt", "assignment_stmt", "assign_op",
  "assign_val", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-70)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-4)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      -3,    12,    43,   -70,    30,   -70,   -70,    23,   -70,    55,
      27,    18,    40,    12,    68,     9,    12,    68,    12,   -70,
     -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,
     -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,    32,   -70,
     -70,   -70,    36,   -70,    44,    45,   -70,    47,   -70,     9,
       9,    31,   -70,   119,    52,    54,    60,   110,   110,   123,
     101,    80,     4,    80,    92,   -70,   -70,    72,   -70,   -70,
     -70,    26,   -70,   -70,     9,     9,    28,    28,    28,    28,
      28,    28,   -70,   -70,   -70,   -70,   -70,   -70,   -70,    85,
      74,   -70,    68,   -70,    33,    12,    28,    68,   -70,   -70,
     -70,    12,   -70,     9,   125,   -70,   -70,    68,    91,    12,
     -70,    12,   -70,   -70,    14,    95,    96,    99,   -70,   -70,
     -70,   -70,   -70,   120,   -70,   -70,   -70,   -70,   -70,   -70,
     -70,    77,   -70,   -70,   -70,   -70,   -70,   -70,   -70,     9,
     -70,   120,   106,   111,   112,   120,    28,   120,   130,   120,
       6,   -70,   120,   -70,   120,   133,   -70,   -70,   -70,     9,
     134,   129,   136,   -70,   -70,   -70,   137,   120,   138,   -70,
     -70,   139,   140,   141,   -70,    -8,   -70,   -70,   -70,   -70,
     142,   -70,   -70,   -70,   -70,   -70
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       5,     0,     0,     5,     0,    78,    79,     0,     1,     0,
       0,     0,    99,     0,     0,     0,     0,     0,     0,     6,
      21,    13,    21,    14,    38,    55,     7,     5,    11,    64,
       5,     8,    15,    70,    12,    16,     4,    10,     0,   103,
     104,   102,   105,   100,     0,     0,    96,     0,    98,     0,
       0,     0,    97,    85,     0,     0,     0,    18,    20,    35,
       0,     0,    61,     0,    69,     9,   106,     0,    34,    68,
      17,     0,    93,    57,     0,     0,     0,     0,     0,     0,
       0,     0,    60,    19,    67,    50,    52,    53,    54,     0,
       0,    48,     0,    47,     0,     0,     0,     0,    49,    51,
      22,    76,    46,     0,     0,    24,    23,     0,     0,     0,
      39,    76,    41,    40,     0,     0,     0,     0,    56,    37,
      36,    59,    58,    83,    66,    65,    63,    62,    71,   101,
      92,    94,    95,    90,    91,    86,    87,    88,    89,     0,
      72,    83,     0,     0,     0,    83,     0,    83,     0,    83,
      83,    73,    83,    44,    83,     0,    81,    82,    80,     0,
       0,     0,     0,    33,    32,    31,     0,    83,     0,    25,
      77,     0,     0,     0,    43,    84,    75,    74,    29,    26,
       0,    28,    27,    45,    42,    30
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -70,   -70,   -70,    19,   126,   -70,   -70,   -70,   -70,   163,
     -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,    93,   -70,
     -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,   -70,
     -70,   -70,   -70,   -70,   102,    42,   -70,    76,     2,   -57,
      10,   -49,   -12,   -69,   -70,   -70,   -70,   -70
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_uint8 yydefgoto[] =
{
       0,     2,     3,     4,    19,    20,    21,    22,    23,    57,
     100,    24,    25,   119,    26,    59,   110,   101,   102,   103,
      60,    27,   121,    28,    29,    30,   126,    31,    62,    32,
      33,    34,    64,   104,   105,   106,   125,   148,   149,   120,
     160,    51,    52,    53,    44,    35,    42,    67
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      71,    72,    47,     7,   122,    55,   127,   133,   134,   135,
     136,   137,   138,    46,    48,    45,     5,     6,    54,    38,
      56,    89,     9,     1,    39,   131,   132,   146,    39,   159,
      -3,    10,    46,    48,    11,   130,    74,    75,    12,   142,
      49,    13,    14,     8,    43,   123,    61,   143,    40,    63,
      74,    75,    40,    15,   150,    -2,    10,    16,    17,    11,
      41,    50,   144,    12,    41,    36,    13,    14,    18,    37,
      74,    75,    46,    73,    65,    74,    75,   167,    15,    66,
     141,    10,    16,    17,    11,   147,    68,    69,    12,    70,
     161,    13,    14,    18,    82,   152,    83,   145,   115,   116,
     117,   113,    84,    15,   124,   114,   128,    16,    17,    89,
     175,   154,    13,    14,   129,   139,   140,    85,    18,   115,
     116,   117,    75,    86,    15,    87,    88,    89,   151,    17,
      85,    90,    91,   153,    92,    93,   107,   156,   157,    18,
      89,   158,    94,   159,    90,    95,    96,    97,   163,    98,
      99,   162,   111,   164,   165,   166,   108,   168,   109,   170,
     171,   112,   172,    99,   173,    76,    77,    78,    79,    80,
      81,   177,   169,    74,    75,   174,   176,   180,   178,   179,
     181,   182,   183,   184,   185,    58,   118,   155
};

static const yytype_uint8 yycheck[] =
{
      49,    50,    14,     1,    61,    17,    63,    76,    77,    78,
      79,    80,    81,     4,     5,    13,     4,     5,    16,     1,
      18,    17,     3,    26,    10,    74,    75,    96,    10,    23,
       0,     1,     4,     5,     4,     9,    44,    45,     8,     6,
      31,    11,    12,     0,     4,    41,    27,    14,    34,    30,
      44,    45,    34,    23,   103,     0,     1,    27,    28,     4,
      46,    52,    29,     8,    46,    42,    11,    12,    38,    42,
      44,    45,     4,    42,    42,    44,    45,   146,    23,    43,
      92,     1,    27,    28,     4,    97,    42,    42,     8,    42,
     139,    11,    12,    38,    42,   107,    42,    95,    18,    19,
      20,    59,    42,    23,    62,     4,    64,    27,    28,    17,
     159,   109,    11,    12,    42,    30,    42,     7,    38,    18,
      19,    20,    45,    13,    23,    15,    16,    17,     3,    28,
       7,    21,    22,    42,    24,    25,    13,    42,    42,    38,
      17,    42,    32,    23,    21,    35,    36,    37,    42,    39,
      40,   141,    59,    42,    42,   145,    33,   147,    35,   149,
     150,    59,   152,    40,   154,    46,    47,    48,    49,    50,
      51,    42,    42,    44,    45,    42,    42,   167,    42,    42,
      42,    42,    42,    42,    42,    22,    60,   111
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,    26,    54,    55,    56,     4,     5,    91,     0,    56,
       1,     4,     8,    11,    12,    23,    27,    28,    38,    57,
      58,    59,    60,    61,    64,    65,    67,    74,    76,    77,
      78,    80,    82,    83,    84,    98,    42,    42,     1,    10,
      34,    46,    99,     4,    97,    91,     4,    95,     5,    31,
      52,    94,    95,    96,    91,    95,    91,    62,    62,    68,
      73,    56,    81,    56,    85,    42,    43,   100,    42,    42,
      42,    94,    94,    42,    44,    45,    46,    47,    48,    49,
      50,    51,    42,    42,    42,     7,    13,    15,    16,    17,
      21,    22,    24,    25,    32,    35,    36,    37,    39,    40,
      63,    70,    71,    72,    86,    87,    88,    13,    33,    35,
      69,    71,    87,    88,     4,    18,    19,    20,    57,    66,
      92,    75,    92,    41,    88,    89,    79,    92,    88,    42,
       9,    94,    94,    96,    96,    96,    96,    96,    96,    30,
      42,    95,     6,    14,    29,    91,    96,    95,    90,    91,
      94,     3,    95,    42,    91,    90,    42,    42,    42,    23,
      93,    94,    93,    42,    42,    42,    93,    96,    93,    42,
      93,    93,    93,    93,    42,    94,    42,    42,    42,    42,
      93,    42,    42,    42,    42,    42
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    53,    54,    54,    55,    56,    56,    56,    56,    56,
      56,    57,    57,    57,    57,    57,    57,    58,    59,    60,
      61,    62,    62,    62,    62,    63,    63,    63,    63,    63,
      63,    63,    63,    63,    64,    65,    66,    67,    68,    68,
      68,    68,    69,    69,    69,    69,    70,    70,    70,    70,
      71,    71,    72,    72,    72,    73,    73,    74,    75,    76,
      77,    78,    79,    80,    81,    81,    81,    82,    83,    84,
      85,    85,    86,    87,    88,    89,    90,    90,    91,    91,
      92,    92,    92,    93,    93,    94,    94,    94,    94,    94,
      94,    94,    94,    94,    94,    94,    95,    96,    96,    97,
      97,    98,    99,    99,    99,   100,   100
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     2,     1,     3,     0,     2,     2,     2,     4,
       3,     1,     1,     1,     1,     1,     1,     3,     2,     3,
       2,     0,     2,     2,     2,     3,     4,     4,     4,     4,
       5,     3,     3,     3,     3,     2,     1,     3,     0,     2,
       2,     2,     4,     3,     2,     4,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     0,     2,     3,     1,     3,
       3,     2,     1,     3,     0,     2,     2,     3,     3,     2,
       0,     2,     2,     2,     4,     3,     0,     2,     1,     1,
       2,     2,     2,     0,     2,     1,     3,     3,     3,     3,
       3,     3,     3,     2,     3,     3,     1,     1,     1,     0,
       1,     4,     1,     1,     1,     0,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)]);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif






/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep)
{
  YY_USE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  switch (yykind)
    {
    case YYSYMBOL_choice_entry: /* choice_entry  */
            {
	fprintf(stderr, "%s:%d: missing end statement for this entry\n",
		((*yyvaluep).menu)->file->name, ((*yyvaluep).menu)->lineno);
	if (current_menu == ((*yyvaluep).menu))
		menu_end_menu();
}
        break;

    case YYSYMBOL_if_entry: /* if_entry  */
            {
	fprintf(stderr, "%s:%d: missing end statement for this entry\n",
		((*yyvaluep).menu)->file->name, ((*yyvaluep).menu)->lineno);
	if (current_menu == ((*yyvaluep).menu))
		menu_end_menu();
}
        break;

    case YYSYMBOL_menu_entry: /* menu_entry  */
            {
	fprintf(stderr, "%s:%d: missing end statement for this entry\n",
		((*yyvaluep).menu)->file->name, ((*yyvaluep).menu)->lineno);
	if (current_menu == ((*yyvaluep).menu))
		menu_end_menu();
}
        break;

      default:
        break;
    }
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/* Lookahead token kind.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 4: /* mainmenu_stmt: T_MAINMENU prompt T_EOL  */
{
	menu_add_prompt(P_MENU, (yyvsp[-1].string), NULL);
}
    break;

  case 9: /* stmt_list: stmt_list T_WORD error T_EOL  */
                                        { zconf_error("unknown statement \"%s\"", (yyvsp[-2].string)); }
    break;

  case 10: /* stmt_list: stmt_list error T_EOL  */
                                        { zconf_error("invalid statement"); }
    break;

  case 17: /* config_entry_start: T_CONFIG nonconst_symbol T_EOL  */
{
	(yyvsp[-1].symbol)->flags |= SYMBOL_OPTIONAL;
	menu_add_entry((yyvsp[-1].symbol));
	printd(DEBUG_PARSE, "%s:%d:config %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].symbol)->name);
}
    break;

  case 18: /* config_stmt: config_entry_start config_option_list  */
{
	printd(DEBUG_PARSE, "%s:%d:endconfig\n", zconf_curname(), zconf_lineno());
}
    break;

  case 19: /* menuconfig_entry_start: T_MENUCONFIG nonconst_symbol T_EOL  */
{
	(yyvsp[-1].symbol)->flags |= SYMBOL_OPTIONAL;
	menu_add_entry((yyvsp[-1].symbol));
	printd(DEBUG_PARSE, "%s:%d:menuconfig %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].symbol)->name);
}
    break;

  case 20: /* menuconfig_stmt: menuconfig_entry_start config_option_list  */
{
	if (current_entry->prompt)
		current_entry->prompt->type = P_MENU;
	else
		zconfprint("warning: menuconfig statement without prompt");
	printd(DEBUG_PARSE, "%s:%d:endconfig\n", zconf_curname(), zconf_lineno());
}
    break;

  case 25: /* config_option: type prompt_stmt_opt T_EOL  */
{
	menu_set_type((yyvsp[-2].type));
	printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
		zconf_curname(), zconf_lineno(),
		(yyvsp[-2].type));
}
    break;

  case 26: /* config_option: T_PROMPT prompt if_expr T_EOL  */
{
	menu_add_prompt(P_PROMPT, (yyvsp[-2].string), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:prompt\n", zconf_curname(), zconf_lineno());
}
    break;

  case 27: /* config_option: default expr if_expr T_EOL  */
{
	menu_add_expr(P_DEFAULT, (yyvsp[-2].expr), (yyvsp[-1].expr));
	if ((yyvsp[-3].type) != S_UNKNOWN)
		menu_set_type((yyvsp[-3].type));
	printd(DEBUG_PARSE, "%s:%d:default(%u)\n",
		zconf_curname(), zconf_lineno(),
		(yyvsp[-3].type));
}
    break;

  case 28: /* config_option: T_SELECT nonconst_symbol if_expr T_EOL  */
{
	menu_add_symbol(P_SELECT, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:select\n", zconf_curname(), zconf_lineno());
}
    break;

  case 29: /* config_option: T_IMPLY nonconst_symbol if_expr T_EOL  */
{
	menu_add_symbol(P_IMPLY, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:imply\n", zconf_curname(), zconf_lineno());
}
    break;

  case 30: /* config_option: T_RANGE symbol symbol if_expr T_EOL  */
{
	menu_add_expr(P_RANGE, expr_alloc_comp(E_RANGE,(yyvsp[-3].symbol), (yyvsp[-2].symbol)), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:range\n", zconf_curname(), zconf_lineno());
}
    break;

  case 31: /* config_option: T_OPTION T_MODULES T_EOL  */
{
	menu_add_option_modules();
}
    break;

  case 32: /* config_option: T_OPTION T_DEFCONFIG_LIST T_EOL  */
{
	menu_add_option_defconfig_list();
}
    break;

  case 33: /* config_option: T_OPTION T_ALLNOCONFIG_Y T_EOL  */
{
	menu_add_option_allnoconfig_y();
}
    break;

  case 34: /* choice: T_CHOICE word_opt T_EOL  */
{
	struct symbol *sym = sym_lookup((yyvsp[-1].string), SYMBOL_CHOICE);
	sym->flags |= SYMBOL_NO_WRITE;
	menu_add_entry(sym);
	menu_add_expr(P_CHOICE, NULL, NULL);
	free((yyvsp[-1].string));
	printd(DEBUG_PARSE, "%s:%d:choice\n", zconf_curname(), zconf_lineno());
}
    break;

  case 35: /* choice_entry: choice choice_option_list  */
{
	(yyval.menu) = menu_add_menu();
}
    break;

  case 36: /* choice_end: end  */
{
	if (zconf_endtoken((yyvsp[0].string), "choice")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endchoice\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 42: /* choice_option: T_PROMPT prompt if_expr T_EOL  */
{
	menu_add_prompt(P_PROMPT, (yyvsp[-2].string), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:prompt\n", zconf_curname(), zconf_lineno());
}
    break;

  case 43: /* choice_option: logic_type prompt_stmt_opt T_EOL  */
{
	menu_set_type((yyvsp[-2].type));
	printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
	       zconf_curname(), zconf_lineno(), (yyvsp[-2].type));
}
    break;

  case 44: /* choice_option: T_OPTIONAL T_EOL  */
{
	current_entry->sym->flags |= SYMBOL_OPTIONAL;
	printd(DEBUG_PARSE, "%s:%d:optional\n", zconf_curname(), zconf_lineno());
}
    break;

  case 45: /* choice_option: T_DEFAULT nonconst_symbol if_expr T_EOL  */
{
	menu_add_symbol(P_DEFAULT, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:default\n",
	       zconf_curname(), zconf_lineno());
}
    break;

  case 47: /* type: T_INT  */
                                { (yyval.type) = S_INT; }
    break;

  case 48: /* type: T_HEX  */
                                { (yyval.type) = S_HEX; }
    break;

  case 49: /* type: T_STRING  */
                                { (yyval.type) = S_STRING; }
    break;

  case 50: /* logic_type: T_BOOL  */
                                { (yyval.type) = S_BOOLEAN; }
    break;

  case 51: /* logic_type: T_TRISTATE  */
                                { (yyval.type) = S_TRISTATE; }
    break;

  case 52: /* default: T_DEFAULT  */
                                { (yyval.type) = S_UNKNOWN; }
    break;

  case 53: /* default: T_DEF_BOOL  */
                                { (yyval.type) = S_BOOLEAN; }
    break;

  case 54: /* default: T_DEF_TRISTATE  */
                                { (yyval.type) = S_TRISTATE; }
    break;

  case 57: /* if_entry: T_IF expr T_EOL  */
{
	printd(DEBUG_PARSE, "%s:%d:if\n", zconf_curname(), zconf_lineno());
	menu_add_entry(NULL);
	menu_add_dep((yyvsp[-1].expr));
	(yyval.menu) = menu_add_menu();
}
    break;

  case 58: /* if_end: end  */
{
	if (zconf_endtoken((yyvsp[0].string), "if")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endif\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 60: /* menu: T_MENU prompt T_EOL  */
{
	menu_add_entry(NULL);
	menu_add_prompt(P_MENU, (yyvsp[-1].string), NULL);
	printd(DEBUG_PARSE, "%s:%d:menu\n", zconf_curname(), zconf_lineno());
}
    break;

  case 61: /* menu_entry: menu menu_option_list  */
{
	(yyval.menu) = menu_add_menu();
}
    break;

  case 62: /* menu_end: end  */
{
	if (zconf_endtoken((yyvsp[0].string), "menu")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endmenu\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 67: /* source_stmt: T_SOURCE prompt T_EOL  */
{
	printd(DEBUG_PARSE, "%s:%d:source %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].string));
	zconf_nextfile((yyvsp[-1].string));
	free((yyvsp[-1].string));
}
    break;

  case 68: /* comment: T_COMMENT prompt T_EOL  */
{
	menu_add_entry(NULL);
	menu_add_prompt(P_COMMENT, (yyvsp[-1].string), NULL);
	printd(DEBUG_PARSE, "%s:%d:comment\n", zconf_curname(), zconf_lineno());
}
    break;

  case 72: /* help_start: T_HELP T_EOL  */
{
	printd(DEBUG_PARSE, "%s:%d:help\n", zconf_curname(), zconf_lineno());
	zconf_starthelp();
}
    break;

  case 73: /* help: help_start T_HELPTEXT  */
{
	if (current_entry->help) {
		free(current_entry->help);
		zconfprint("warning: '%s' defined with more than one help text -- only the last one will be used",
			   current_entry->sym->name ?: "<choice>");
	}

	/* Is the help text empty or all whitespace? */
	if ((yyvsp[0].string)[strspn((yyvsp[0].string), " \f\n\r\t\v")] == '\0')
		zconfprint("warning: '%s' defined with blank help text",
			   current_entry->sym->name ?: "<choice>");

	current_entry->help = (yyvsp[0].string);
}
    break;

  case 74: /* depends: T_DEPENDS T_ON expr T_EOL  */
{
	menu_add_dep((yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:depends on\n", zconf_curname(), zconf_lineno());
}
    break;

  case 75: /* visible: T_VISIBLE if_expr T_EOL  */
{
	menu_add_visibility((yyvsp[-1].expr));
}
    break;

  case 77: /* prompt_stmt_opt: prompt if_expr  */
{
	menu_add_prompt(P_PROMPT, (yyvsp[-1].string), (yyvsp[0].expr));
}
    break;

  case 80: /* end: T_ENDMENU T_EOL  */
                                { (yyval.string) = "menu"; }
    break;

  case 81: /* end: T_ENDCHOICE T_EOL  */
                                { (yyval.string) = "choice"; }
    break;

  case 82: /* end: T_ENDIF T_EOL  */
                                { (yyval.string) = "if"; }
    break;

  case 83: /* if_expr: %empty  */
                                        { (yyval.expr) = NULL; }
    break;

  case 84: /* if_expr: T_IF expr  */
                                        { (yyval.expr) = (yyvsp[0].expr); }
    break;

  case 85: /* expr: symbol  */
                                                { (yyval.expr) = expr_alloc_symbol((yyvsp[0].symbol)); }
    break;

  case 86: /* expr: symbol T_LESS symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_LTH, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 87: /* expr: symbol T_LESS_EQUAL symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_LEQ, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 88: /* expr: symbol T_GREATER symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_GTH, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 89: /* expr: symbol T_GREATER_EQUAL symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_GEQ, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 90: /* expr: symbol T_EQUAL symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_EQUAL, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 91: /* expr: symbol T_UNEQUAL symbol  */
                                                { (yyval.expr) = expr_alloc_comp(E_UNEQUAL, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 92: /* expr: T_OPEN_PAREN expr T_CLOSE_PAREN  */
                                                { (yyval.expr) = (yyvsp[-1].expr); }
    break;

  case 93: /* expr: T_NOT expr  */
                                                { (yyval.expr) = expr_alloc_one(E_NOT, (yyvsp[0].expr)); }
    break;

  case 94: /* expr: expr T_OR expr  */
                                                { (yyval.expr) = expr_alloc_two(E_OR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
    break;

  case 95: /* expr: expr T_AND expr  */
                                                { (yyval.expr) = expr_alloc_two(E_AND, (yyvsp[-2].expr), (yyvsp[0].expr)); }
    break;

  case 96: /* nonconst_symbol: T_WORD  */
                        { (yyval.symbol) = sym_lookup((yyvsp[0].string), 0); free((yyvsp[0].string)); }
    break;

  case 98: /* symbol: T_WORD_QUOTE  */
                        { (yyval.symbol) = sym_lookup((yyvsp[0].string), SYMBOL_CONST); free((yyvsp[0].string)); }
    break;

  case 99: /* word_opt: %empty  */
                                        { (yyval.string) = NULL; }
    break;

  case 101: /* assignment_stmt: T_WORD assign_op assign_val T_EOL  */
                                                        { variable_add((yyvsp[-3].string), (yyvsp[-1].string), (yyvsp[-2].flavor)); free((yyvsp[-3].string)); free((yyvsp[-1].string)); }
    break;

  case 102: /* assign_op: T_EQUAL  */
                        { (yyval.flavor) = VAR_RECURSIVE; }
    break;

  case 103: /* assign_op: T_COLON_EQUAL  */
                        { (yyval.flavor) = VAR_SIMPLE; }
    break;

  case 104: /* assign_op: T_PLUS_EQUAL  */
                        { (yyval.flavor) = VAR_APPEND; }
    break;

  case 105: /* assign_val: %empty  */
                                { (yyval.string) = xstrdup(""); }
    break;



      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      yyerror (YY_("syntax error"));
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif

  return yyresult;
}



void conf_parse(const char *name)
{
	struct symbol *sym;
	int i;

	zconf_initscan(name);

	_menu_init();

	if (getenv("ZCONF_DEBUG"))
		yydebug = 1;
	yyparse();

	/* Variables are expanded in the parse phase. We can free them here. */
	variable_all_del();

	if (yynerrs)
		exit(1);
	if (!modules_sym)
		modules_sym = sym_find( "n" );

	if (!menu_has_prompt(&rootmenu)) {
		current_entry = &rootmenu;
		menu_add_prompt(P_MENU, "Main menu", NULL);
	}

	menu_finalize(&rootmenu);
	for_all_symbols(i, sym) {
		if (sym_check_deps(sym))
			yynerrs++;
	}
	if (yynerrs)
		exit(1);
	sym_set_change_count(1);
}

static bool zconf_endtoken(const char *tokenname,
			   const char *expected_tokenname)
{
	if (strcmp(tokenname, expected_tokenname)) {
		zconf_error("unexpected '%s' within %s block",
			    tokenname, expected_tokenname);
		yynerrs++;
		return false;
	}
	if (current_menu->file != current_file) {
		zconf_error("'%s' in different file than '%s'",
			    tokenname, expected_tokenname);
		fprintf(stderr, "%s:%d: location of the '%s'\n",
			current_menu->file->name, current_menu->lineno,
			expected_tokenname);
		yynerrs++;
		return false;
	}
	return true;
}

static void zconfprint(const char *err, ...)
{
	va_list ap;

	fprintf(stderr, "%s:%d: ", zconf_curname(), zconf_lineno());
	va_start(ap, err);
	vfprintf(stderr, err, ap);
	va_end(ap);
	fprintf(stderr, "\n");
}

static void zconf_error(const char *err, ...)
{
	va_list ap;

	yynerrs++;
	fprintf(stderr, "%s:%d: ", zconf_curname(), zconf_lineno());
	va_start(ap, err);
	vfprintf(stderr, err, ap);
	va_end(ap);
	fprintf(stderr, "\n");
}

static void yyerror(const char *err)
{
	fprintf(stderr, "%s:%d: %s\n", zconf_curname(), zconf_lineno() + 1, err);
}

static void print_quoted_string(FILE *out, const char *str)
{
	const char *p;
	int len;

	putc('"', out);
	while ((p = strchr(str, '"'))) {
		len = p - str;
		if (len)
			fprintf(out, "%.*s", len, str);
		fputs("\\\"", out);
		str = p + 1;
	}
	fputs(str, out);
	putc('"', out);
}

static void print_symbol(FILE *out, struct menu *menu)
{
	struct symbol *sym = menu->sym;
	struct property *prop;

	if (sym_is_choice(sym))
		fprintf(out, "\nchoice\n");
	else
		fprintf(out, "\nconfig %s\n", sym->name);
	switch (sym->type) {
	case S_BOOLEAN:
		fputs("  bool\n", out);
		break;
	case S_TRISTATE:
		fputs("  tristate\n", out);
		break;
	case S_STRING:
		fputs("  string\n", out);
		break;
	case S_INT:
		fputs("  integer\n", out);
		break;
	case S_HEX:
		fputs("  hex\n", out);
		break;
	default:
		fputs("  ???\n", out);
		break;
	}
	for (prop = sym->prop; prop; prop = prop->next) {
		if (prop->menu != menu)
			continue;
		switch (prop->type) {
		case P_PROMPT:
			fputs("  prompt ", out);
			print_quoted_string(out, prop->text);
			if (!expr_is_yes(prop->visible.expr)) {
				fputs(" if ", out);
				expr_fprint(prop->visible.expr, out);
			}
			fputc('\n', out);
			break;
		case P_DEFAULT:
			fputs( "  default ", out);
			expr_fprint(prop->expr, out);
			if (!expr_is_yes(prop->visible.expr)) {
				fputs(" if ", out);
				expr_fprint(prop->visible.expr, out);
			}
			fputc('\n', out);
			break;
		case P_CHOICE:
			fputs("  #choice value\n", out);
			break;
		case P_SELECT:
			fputs( "  select ", out);
			expr_fprint(prop->expr, out);
			fputc('\n', out);
			break;
		case P_IMPLY:
			fputs( "  imply ", out);
			expr_fprint(prop->expr, out);
			fputc('\n', out);
			break;
		case P_RANGE:
			fputs( "  range ", out);
			expr_fprint(prop->expr, out);
			fputc('\n', out);
			break;
		case P_MENU:
			fputs( "  menu ", out);
			print_quoted_string(out, prop->text);
			fputc('\n', out);
			break;
		case P_SYMBOL:
			fputs( "  symbol ", out);
			fprintf(out, "%s\n", prop->sym->name);
			break;
		default:
			fprintf(out, "  unknown prop %d!\n", prop->type);
			break;
		}
	}
	if (menu->help) {
		int len = strlen(menu->help);
		while (menu->help[--len] == '\n')
			menu->help[len] = 0;
		fprintf(out, "  help\n%s\n", menu->help);
	}
}

void zconfdump(FILE *out)
{
	struct property *prop;
	struct symbol *sym;
	struct menu *menu;

	menu = rootmenu.list;
	while (menu) {
		if ((sym = menu->sym))
			print_symbol(out, menu);
		else if ((prop = menu->prompt)) {
			switch (prop->type) {
			case P_COMMENT:
				fputs("\ncomment ", out);
				print_quoted_string(out, prop->text);
				fputs("\n", out);
				break;
			case P_MENU:
				fputs("\nmenu ", out);
				print_quoted_string(out, prop->text);
				fputs("\n", out);
				break;
			default:
				;
			}
			if (!expr_is_yes(prop->visible.expr)) {
				fputs("  depends ", out);
				expr_fprint(prop->visible.expr, out);
				fputc('\n', out);
			}
		}

		if (menu->list)
			menu = menu->list;
		else if (menu->next)
			menu = menu->next;
		else while ((menu = menu->parent)) {
			if (menu->prompt && menu->prompt->type == P_MENU)
				fputs("\nendmenu\n", out);
			if (menu->next) {
				menu = menu->next;
				break;
			}
		}
	}
}

#include "util.c"
#include "menu.c"
