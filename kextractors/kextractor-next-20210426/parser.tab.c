/* A Bison parser, made by GNU Bison 3.5.1.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Undocumented macros, especially those whose name start with YY_,
   are private implementation details.  Do not rely on them.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.5.1"

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
#include "internal.h"

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

struct menu *current_menu, *current_entry;



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

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Use api.header.include to #include this header
   instead of duplicating it here.  */
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
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && ! defined __ICC && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                            \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
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

#if ! defined yyoverflow || YYERROR_VERBOSE

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
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


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
#define YYFINAL  6
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   184

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  50
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  47
/* YYNRULES -- Number of rules.  */
#define YYNRULES  105
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  184

#define YYUNDEFTOK  2
#define YYMAXUTOK   304


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

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
      45,    46,    47,    48,    49
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   109,   109,   109,   113,   118,   120,   121,   122,   123,
     124,   125,   126,   127,   128,   129,   132,   134,   135,   136,
     137,   142,   149,   154,   161,   170,   172,   173,   174,   177,
     185,   191,   201,   207,   213,   219,   229,   239,   244,   252,
     255,   257,   258,   259,   262,   268,   275,   281,   289,   290,
     291,   292,   295,   296,   299,   300,   301,   305,   313,   321,
     324,   329,   336,   341,   349,   352,   354,   355,   358,   367,
     374,   377,   379,   384,   390,   408,   415,   422,   424,   429,
     430,   431,   434,   435,   438,   439,   440,   441,   442,   443,
     444,   445,   446,   447,   448,   452,   454,   455,   458,   459,
     463,   466,   467,   468,   472,   473
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "T_HELPTEXT", "T_WORD", "T_WORD_QUOTE",
  "T_BOOL", "T_CHOICE", "T_CLOSE_PAREN", "T_COLON_EQUAL", "T_COMMENT",
  "T_CONFIG", "T_DEFAULT", "T_DEF_BOOL", "T_DEF_TRISTATE", "T_DEPENDS",
  "T_ENDCHOICE", "T_ENDIF", "T_ENDMENU", "T_HELP", "T_HEX", "T_IF",
  "T_IMPLY", "T_INT", "T_MAINMENU", "T_MENU", "T_MENUCONFIG", "T_MODULES",
  "T_ON", "T_OPEN_PAREN", "T_OPTIONAL", "T_PLUS_EQUAL", "T_PROMPT",
  "T_RANGE", "T_SELECT", "T_SOURCE", "T_STRING", "T_TRISTATE", "T_VISIBLE",
  "T_EOL", "T_ASSIGN_VAL", "T_OR", "T_AND", "T_EQUAL", "T_UNEQUAL",
  "T_LESS", "T_LESS_EQUAL", "T_GREATER", "T_GREATER_EQUAL", "T_NOT",
  "$accept", "input", "mainmenu_stmt", "stmt_list", "stmt_list_in_choice",
  "config_entry_start", "config_stmt", "menuconfig_entry_start",
  "menuconfig_stmt", "config_option_list", "config_option", "choice",
  "choice_entry", "choice_end", "choice_stmt", "choice_option_list",
  "choice_option", "type", "logic_type", "default", "if_entry", "if_end",
  "if_stmt", "if_stmt_in_choice", "menu", "menu_entry", "menu_end",
  "menu_stmt", "menu_option_list", "source_stmt", "comment",
  "comment_stmt", "comment_option_list", "help_start", "help", "depends",
  "visible", "prompt_stmt_opt", "end", "if_expr", "expr",
  "nonconst_symbol", "symbol", "word_opt", "assignment_stmt", "assign_op",
  "assign_val", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_int16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304
};
# endif

#define YYPACT_NINF (-65)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-4)

#define yytable_value_is_error(Yyn) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      -4,    29,    47,   -65,    17,     5,   -65,    49,     9,    14,
      51,    56,    58,     2,    60,    58,    63,   -65,   -65,   -65,
     -65,   -65,   -65,   -65,   -65,   -65,   -65,   -65,   -65,   -65,
     -65,   -65,   -65,   -65,   -65,    34,   -65,   -65,   -65,    41,
     -65,    38,    50,   -65,    52,   -65,     2,     2,    30,   -65,
     135,    55,    57,    61,   108,   108,   131,   156,    91,    20,
      91,    68,   -65,   -65,    67,   -65,   -65,   -65,    22,   -65,
     -65,     2,     2,    28,    28,    28,    28,    28,    28,   -65,
     -65,   -65,   -65,   -65,   -65,   -65,    62,    71,   -65,    58,
     -65,    72,    83,    28,    58,   -65,   -65,   -65,    94,   -65,
       2,   112,   -65,   -65,    58,    79,   114,   -65,    94,   -65,
     -65,    85,    86,    90,    93,   -65,   -65,   -65,   -65,   -65,
     -65,   -65,   -65,   113,   -65,   -65,   -65,   -65,   -65,   -65,
     -65,    96,   -65,   -65,   -65,   -65,   -65,   -65,   -65,     2,
     -65,   113,   -65,   113,    28,   113,   113,    97,    25,   -65,
     113,   -65,   113,   100,   -65,   -65,   -65,   -65,   156,     2,
     109,    37,   116,   120,   113,   121,   -65,   -65,   123,   125,
     126,   -65,   -65,    44,   -65,   -65,   -65,   -65,   130,   -65,
     -65,   -65,   -65,   -65
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       5,     0,     0,     5,     0,     0,     1,     0,     0,     0,
      98,     0,     0,     0,     0,     0,     0,    25,     9,    25,
      12,    40,    16,     7,     5,    10,    65,     5,    11,    13,
      71,     8,     6,     4,    15,     0,   102,   103,   101,   104,
      99,     0,     0,    95,     0,    97,     0,     0,     0,    96,
      84,     0,     0,     0,    22,    24,    37,     0,     0,    62,
       0,    70,    14,   105,     0,    36,    69,    21,     0,    92,
      57,     0,     0,     0,     0,     0,     0,     0,     0,    61,
      23,    68,    52,    54,    55,    56,     0,     0,    50,     0,
      49,     0,     0,     0,     0,    51,    53,    26,    77,    48,
       0,     0,    28,    27,     0,     0,     0,    41,    77,    43,
      42,     0,     0,     0,     0,    18,    39,    16,    19,    17,
      38,    59,    58,    82,    67,    66,    64,    63,    72,   100,
      91,    93,    94,    89,    90,    85,    86,    87,    88,     0,
      73,    82,    35,    82,     0,    82,    82,     0,    82,    74,
      82,    46,    82,     0,    20,    80,    81,    79,     0,     0,
       0,     0,     0,     0,    82,     0,    78,    29,     0,     0,
       0,    45,    60,    83,    76,    75,    33,    30,     0,    32,
      31,    47,    44,    34
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -65,   -65,   -65,    13,    16,   -65,   -55,   -65,   -65,   134,
     -65,   -65,   -65,   -65,   -65,   -65,   -65,   -65,   115,   -65,
     -54,    18,   -65,   -65,   -65,   -65,   -65,   -65,   -65,   -65,
     -65,   -53,   -65,   -65,   119,   -20,   -65,    76,   -38,     6,
     -46,    -7,   -64,   -65,   -65,   -65,   -65
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,    57,    17,    18,    19,    20,    54,
      97,    21,    22,   116,    23,    56,   107,    98,    99,   100,
      24,   121,    25,   118,    26,    27,   126,    28,    59,    29,
      30,    31,    61,   101,   102,   103,   125,   147,   122,   160,
      48,    49,    50,    41,    32,    39,    64
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      68,    69,   115,   117,   119,    44,    43,    45,    52,   133,
     134,   135,   136,   137,   138,    35,     7,    -3,     8,   120,
       1,     9,   127,    36,    10,   131,   132,    11,    12,   144,
     130,    46,    43,    45,     5,    86,   110,    58,    13,   124,
      60,   128,    14,    15,    33,    37,   159,     6,    34,    -2,
       8,    47,    16,     9,   148,    40,    10,    38,   123,    11,
      12,    42,    43,    71,    72,    51,    71,    72,    53,    70,
      13,    71,    72,    62,    14,    15,   175,    65,    71,    72,
     164,    63,   141,    86,    16,    71,    72,   145,   143,    66,
     139,    67,     8,   161,    79,     9,    80,   150,    10,   146,
      81,    11,    12,   115,   117,   119,   129,   112,   113,   114,
     140,   142,    13,   173,    82,   149,    14,    15,   151,   152,
      83,    84,    85,    86,   154,   155,    16,    87,    88,   156,
      89,    90,   157,   158,   159,    91,   167,    82,    72,   171,
      92,    93,    94,   104,    95,    96,    86,   162,   174,   163,
      87,   165,   166,    55,   168,   176,   169,   111,   170,   177,
     179,   105,   180,   106,   181,   182,    11,    12,    96,   183,
     178,   108,   112,   113,   114,   109,   172,    13,    73,    74,
      75,    76,    77,    78,   153
};

static const yytype_uint8 yycheck[] =
{
      46,    47,    57,    57,    57,    12,     4,     5,    15,    73,
      74,    75,    76,    77,    78,     1,     3,     0,     1,    57,
      24,     4,    60,     9,     7,    71,    72,    10,    11,    93,
       8,    29,     4,     5,     5,    15,    56,    24,    21,    59,
      27,    61,    25,    26,    39,    31,    21,     0,    39,     0,
       1,    49,    35,     4,   100,     4,     7,    43,    38,    10,
      11,     5,     4,    41,    42,     5,    41,    42,     5,    39,
      21,    41,    42,    39,    25,    26,    39,    39,    41,    42,
     144,    40,    89,    15,    35,    41,    42,    94,     5,    39,
      28,    39,     1,   139,    39,     4,    39,   104,     7,     5,
      39,    10,    11,   158,   158,   158,    39,    16,    17,    18,
      39,    39,    21,   159,     6,     3,    25,    26,    39,     5,
      12,    13,    14,    15,    39,    39,    35,    19,    20,    39,
      22,    23,    39,   117,    21,    27,    39,     6,    42,    39,
      32,    33,    34,    12,    36,    37,    15,   141,    39,   143,
      19,   145,   146,    19,   148,    39,   150,     1,   152,    39,
      39,    30,    39,    32,    39,    39,    10,    11,    37,    39,
     164,    56,    16,    17,    18,    56,   158,    21,    43,    44,
      45,    46,    47,    48,   108
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,    24,    51,    52,    53,     5,     0,    53,     1,     4,
       7,    10,    11,    21,    25,    26,    35,    55,    56,    57,
      58,    61,    62,    64,    70,    72,    74,    75,    77,    79,
      80,    81,    94,    39,    39,     1,     9,    31,    43,    95,
       4,    93,     5,     4,    91,     5,    29,    49,    90,    91,
      92,     5,    91,     5,    59,    59,    65,    54,    53,    78,
      53,    82,    39,    40,    96,    39,    39,    39,    90,    90,
      39,    41,    42,    43,    44,    45,    46,    47,    48,    39,
      39,    39,     6,    12,    13,    14,    15,    19,    20,    22,
      23,    27,    32,    33,    34,    36,    37,    60,    67,    68,
      69,    83,    84,    85,    12,    30,    32,    66,    68,    84,
      85,     1,    16,    17,    18,    56,    63,    70,    73,    81,
      88,    71,    88,    38,    85,    86,    76,    88,    85,    39,
       8,    90,    90,    92,    92,    92,    92,    92,    92,    28,
      39,    91,    39,     5,    92,    91,     5,    87,    90,     3,
      91,    39,     5,    87,    39,    39,    39,    39,    54,    21,
      89,    90,    89,    89,    92,    89,    89,    39,    89,    89,
      89,    39,    71,    90,    39,    39,    39,    39,    89,    39,
      39,    39,    39,    39
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_int8 yyr1[] =
{
       0,    50,    51,    51,    52,    53,    53,    53,    53,    53,
      53,    53,    53,    53,    53,    53,    54,    54,    54,    54,
      54,    55,    56,    57,    58,    59,    59,    59,    59,    60,
      60,    60,    60,    60,    60,    60,    61,    62,    63,    64,
      65,    65,    65,    65,    66,    66,    66,    66,    67,    67,
      67,    67,    68,    68,    69,    69,    69,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    78,    78,    79,    80,
      81,    82,    82,    83,    84,    85,    86,    87,    87,    88,
      88,    88,    89,    89,    90,    90,    90,    90,    90,    90,
      90,    90,    90,    90,    90,    91,    92,    92,    93,    93,
      94,    95,    95,    95,    96,    96
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     2,     1,     3,     0,     2,     2,     2,     2,
       2,     2,     2,     2,     4,     3,     0,     2,     2,     2,
       3,     3,     2,     3,     2,     0,     2,     2,     2,     3,
       4,     4,     4,     4,     5,     2,     3,     2,     1,     3,
       0,     2,     2,     2,     4,     3,     2,     4,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     3,
       3,     3,     2,     1,     3,     0,     2,     2,     3,     3,
       2,     0,     2,     2,     2,     4,     3,     0,     2,     2,
       2,     2,     0,     2,     1,     3,     3,     3,     3,     3,
       3,     3,     2,     3,     3,     1,     1,     1,     0,     1,
       4,     1,     1,     1,     0,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


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

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



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

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YYUSE (yyoutput);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyo, yytoknum[yytype], *yyvaluep);
# endif
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyo, yytype, yyvaluep);
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
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, int yyrule)
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
                       yystos[+yyssp[yyi + 1 - yynrhs]],
                       &yyvsp[(yyi + 1) - (yynrhs)]
                                              );
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
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
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


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
#  else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                yy_state_t *yyssp, int yytoken)
{
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Actual size of YYARG. */
  int yycount = 0;
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[+*yyssp];
      YYPTRDIFF_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
      yysize = yysize0;
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYPTRDIFF_T yysize1
                    = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
                    yysize = yysize1;
                  else
                    return 2;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    /* Don't count the "%s"s in the final size, but reserve room for
       the terminator.  */
    YYPTRDIFF_T yysize1 = yysize + (yystrlen (yyformat) - 2 * yycount) + 1;
    if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
      yysize = yysize1;
    else
      return 2;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  switch (yytype)
    {
    case 62: /* choice_entry  */
            {
	fprintf(stderr, "%s:%d: missing end statement for this entry\n",
		((*yyvaluep).menu)->file->name, ((*yyvaluep).menu)->lineno);
	if (current_menu == ((*yyvaluep).menu))
		menu_end_menu();
}
        break;

    case 70: /* if_entry  */
            {
	fprintf(stderr, "%s:%d: missing end statement for this entry\n",
		((*yyvaluep).menu)->file->name, ((*yyvaluep).menu)->lineno);
	if (current_menu == ((*yyvaluep).menu))
		menu_end_menu();
}
        break;

    case 75: /* menu_entry  */
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




/* The lookahead symbol.  */
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
    yy_state_fast_t yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss;
    yy_state_t *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYPTRDIFF_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
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

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    goto yyexhaustedlab;
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
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
# undef YYSTACK_RELOCATE
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

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
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
  case 4:
{
	menu_add_prompt(P_MENU, (yyvsp[-1].string), NULL);
}
    break;

  case 14:
                                        { zconf_error("unknown statement \"%s\"", (yyvsp[-2].string)); }
    break;

  case 15:
                                        { zconf_error("invalid statement"); }
    break;

  case 20:
                                                { zconf_error("invalid statement"); }
    break;

  case 21:
{
	(yyvsp[-1].symbol)->flags |= SYMBOL_OPTIONAL;
	menu_add_entry((yyvsp[-1].symbol));
	printd(DEBUG_PARSE, "%s:%d:config %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].symbol)->name);
}
    break;

  case 22:
{
	printd(DEBUG_PARSE, "%s:%d:endconfig\n", zconf_curname(), zconf_lineno());
}
    break;

  case 23:
{
	(yyvsp[-1].symbol)->flags |= SYMBOL_OPTIONAL;
	menu_add_entry((yyvsp[-1].symbol));
	printd(DEBUG_PARSE, "%s:%d:menuconfig %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].symbol)->name);
}
    break;

  case 24:
{
	if (current_entry->prompt)
		current_entry->prompt->type = P_MENU;
	else
		zconfprint("warning: menuconfig statement without prompt");
	printd(DEBUG_PARSE, "%s:%d:endconfig\n", zconf_curname(), zconf_lineno());
}
    break;

  case 29:
{
	menu_set_type((yyvsp[-2].type));
	printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
		zconf_curname(), zconf_lineno(),
		(yyvsp[-2].type));
}
    break;

  case 30:
{
	menu_add_prompt(P_PROMPT, (yyvsp[-2].string), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:prompt\n", zconf_curname(), zconf_lineno());
}
    break;

  case 31:
{
	menu_add_expr(P_DEFAULT, (yyvsp[-2].expr), (yyvsp[-1].expr));
	if ((yyvsp[-3].type) != S_UNKNOWN)
		menu_set_type((yyvsp[-3].type));
	printd(DEBUG_PARSE, "%s:%d:default(%u)\n",
		zconf_curname(), zconf_lineno(),
		(yyvsp[-3].type));
}
    break;

  case 32:
{
	menu_add_symbol(P_SELECT, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:select\n", zconf_curname(), zconf_lineno());
}
    break;

  case 33:
{
	menu_add_symbol(P_IMPLY, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:imply\n", zconf_curname(), zconf_lineno());
}
    break;

  case 34:
{
	menu_add_expr(P_RANGE, expr_alloc_comp(E_RANGE,(yyvsp[-3].symbol), (yyvsp[-2].symbol)), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:range\n", zconf_curname(), zconf_lineno());
}
    break;

  case 35:
{
	if (modules_sym)
		zconf_error("symbol '%s' redefines option 'modules' already defined by symbol '%s'",
			    current_entry->sym->name, modules_sym->name);
	modules_sym = current_entry->sym;
}
    break;

  case 36:
{
	struct symbol *sym = sym_lookup((yyvsp[-1].string), SYMBOL_CHOICE);
	sym->flags |= SYMBOL_NO_WRITE;
	menu_add_entry(sym);
	menu_add_expr(P_CHOICE, NULL, NULL);
	free((yyvsp[-1].string));
	printd(DEBUG_PARSE, "%s:%d:choice\n", zconf_curname(), zconf_lineno());
}
    break;

  case 37:
{
	(yyval.menu) = menu_add_menu();
}
    break;

  case 38:
{
	if (zconf_endtoken((yyvsp[0].string), "choice")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endchoice\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 44:
{
	menu_add_prompt(P_PROMPT, (yyvsp[-2].string), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:prompt\n", zconf_curname(), zconf_lineno());
}
    break;

  case 45:
{
	menu_set_type((yyvsp[-2].type));
	printd(DEBUG_PARSE, "%s:%d:type(%u)\n",
	       zconf_curname(), zconf_lineno(), (yyvsp[-2].type));
}
    break;

  case 46:
{
	current_entry->sym->flags |= SYMBOL_OPTIONAL;
	printd(DEBUG_PARSE, "%s:%d:optional\n", zconf_curname(), zconf_lineno());
}
    break;

  case 47:
{
	menu_add_symbol(P_DEFAULT, (yyvsp[-2].symbol), (yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:default\n",
	       zconf_curname(), zconf_lineno());
}
    break;

  case 49:
                                { (yyval.type) = S_INT; }
    break;

  case 50:
                                { (yyval.type) = S_HEX; }
    break;

  case 51:
                                { (yyval.type) = S_STRING; }
    break;

  case 52:
                                { (yyval.type) = S_BOOLEAN; }
    break;

  case 53:
                                { (yyval.type) = S_TRISTATE; }
    break;

  case 54:
                                { (yyval.type) = S_UNKNOWN; }
    break;

  case 55:
                                { (yyval.type) = S_BOOLEAN; }
    break;

  case 56:
                                { (yyval.type) = S_TRISTATE; }
    break;

  case 57:
{
	printd(DEBUG_PARSE, "%s:%d:if\n", zconf_curname(), zconf_lineno());
	menu_add_entry(NULL);
	menu_add_dep((yyvsp[-1].expr));
	(yyval.menu) = menu_add_menu();
}
    break;

  case 58:
{
	if (zconf_endtoken((yyvsp[0].string), "if")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endif\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 61:
{
	menu_add_entry(NULL);
	menu_add_prompt(P_MENU, (yyvsp[-1].string), NULL);
	printd(DEBUG_PARSE, "%s:%d:menu\n", zconf_curname(), zconf_lineno());
}
    break;

  case 62:
{
	(yyval.menu) = menu_add_menu();
}
    break;

  case 63:
{
	if (zconf_endtoken((yyvsp[0].string), "menu")) {
		menu_end_menu();
		printd(DEBUG_PARSE, "%s:%d:endmenu\n", zconf_curname(), zconf_lineno());
	}
}
    break;

  case 68:
{
	printd(DEBUG_PARSE, "%s:%d:source %s\n", zconf_curname(), zconf_lineno(), (yyvsp[-1].string));
	zconf_nextfile((yyvsp[-1].string));
	free((yyvsp[-1].string));
}
    break;

  case 69:
{
	menu_add_entry(NULL);
	menu_add_prompt(P_COMMENT, (yyvsp[-1].string), NULL);
	printd(DEBUG_PARSE, "%s:%d:comment\n", zconf_curname(), zconf_lineno());
}
    break;

  case 73:
{
	printd(DEBUG_PARSE, "%s:%d:help\n", zconf_curname(), zconf_lineno());
	zconf_starthelp();
}
    break;

  case 74:
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

  case 75:
{
	menu_add_dep((yyvsp[-1].expr));
	printd(DEBUG_PARSE, "%s:%d:depends on\n", zconf_curname(), zconf_lineno());
}
    break;

  case 76:
{
	menu_add_visibility((yyvsp[-1].expr));
}
    break;

  case 78:
{
	menu_add_prompt(P_PROMPT, (yyvsp[-1].string), (yyvsp[0].expr));
}
    break;

  case 79:
                                { (yyval.string) = "menu"; }
    break;

  case 80:
                                { (yyval.string) = "choice"; }
    break;

  case 81:
                                { (yyval.string) = "if"; }
    break;

  case 82:
                                        { (yyval.expr) = NULL; }
    break;

  case 83:
                                        { (yyval.expr) = (yyvsp[0].expr); }
    break;

  case 84:
                                                { (yyval.expr) = expr_alloc_symbol((yyvsp[0].symbol)); }
    break;

  case 85:
                                                { (yyval.expr) = expr_alloc_comp(E_LTH, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 86:
                                                { (yyval.expr) = expr_alloc_comp(E_LEQ, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 87:
                                                { (yyval.expr) = expr_alloc_comp(E_GTH, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 88:
                                                { (yyval.expr) = expr_alloc_comp(E_GEQ, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 89:
                                                { (yyval.expr) = expr_alloc_comp(E_EQUAL, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 90:
                                                { (yyval.expr) = expr_alloc_comp(E_UNEQUAL, (yyvsp[-2].symbol), (yyvsp[0].symbol)); }
    break;

  case 91:
                                                { (yyval.expr) = (yyvsp[-1].expr); }
    break;

  case 92:
                                                { (yyval.expr) = expr_alloc_one(E_NOT, (yyvsp[0].expr)); }
    break;

  case 93:
                                                { (yyval.expr) = expr_alloc_two(E_OR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
    break;

  case 94:
                                                { (yyval.expr) = expr_alloc_two(E_AND, (yyvsp[-2].expr), (yyvsp[0].expr)); }
    break;

  case 95:
                        { (yyval.symbol) = sym_lookup((yyvsp[0].string), 0); free((yyvsp[0].string)); }
    break;

  case 97:
                        { (yyval.symbol) = sym_lookup((yyvsp[0].string), SYMBOL_CONST); free((yyvsp[0].string)); }
    break;

  case 98:
                                        { (yyval.string) = NULL; }
    break;

  case 100:
                                                        { variable_add((yyvsp[-3].string), (yyvsp[-1].string), (yyvsp[-2].flavor)); free((yyvsp[-3].string)); free((yyvsp[-1].string)); }
    break;

  case 101:
                        { (yyval.flavor) = VAR_RECURSIVE; }
    break;

  case 102:
                        { (yyval.flavor) = VAR_SIMPLE; }
    break;

  case 103:
                        { (yyval.flavor) = VAR_APPEND; }
    break;

  case 104:
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
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

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
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *, YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
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

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
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
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;


#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif


/*-----------------------------------------------------.
| yyreturn -- parsing is finished, return the result.  |
`-----------------------------------------------------*/
yyreturn:
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
                  yystos[+*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
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
	conf_set_changed(true);
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
			fprintf(out, "%s\n", prop->menu->sym->name);
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
