/**
 * This is an extension to Kconfig code to print unmet dependency warnings
 * in an explicit format amenable to bug verification by kismet.
 * 
 * The code was adapted from the Kconfig code of newer Linux kernel
 * versions. Function names are prefixed with "kismet_" to avoid potential
 * name collisions.
 * */

#ifndef KISMET_UDD_PRINTER_EXTENSION_H
#define KISMET_UDD_PRINTER_EXTENSION_H

#include <string.h>

#include "lkc.h"

void expr_gstr_print(struct expr*, struct gstr*); // expr.c
tristate expr_calc_value(struct expr*); // expr.c

/*
 * Transform the top level "||" tokens into newlines and prepend each
 * line with a minus. This makes expressions much easier to read.
 * Suitable for reverse dependency expressions.
 */
static void kismet_expr_print_revdep(struct expr *e,
			      void (*fn)(void *, struct symbol *, const char *),
			      void *data, tristate pr_type, const char **title)
{
	if (e->type == E_OR) {
		kismet_expr_print_revdep(e->left.expr, fn, data, pr_type, title);
		kismet_expr_print_revdep(e->right.expr, fn, data, pr_type, title);
	} else if (expr_calc_value(e) == pr_type) {
		if (*title) {
			fn(data, NULL, *title);
			*title = NULL;
		}

		fn(data, NULL, "  - ");
		expr_print(e, fn, data, E_NONE);
		fn(data, NULL, "\n");
	}
}

static void kismet_expr_print_gstr_helper(void *data, struct symbol *sym, const char *str)
{
	struct gstr *gs = (struct gstr*)data;
	const char *sym_str = NULL;

	if (sym)
		sym_str = sym_get_string_value(sym);

	if (gs->max_width) {
		unsigned extra_length = strlen(str);
		const char *last_cr = strrchr(gs->s, '\n');
		unsigned last_line_length;

		if (sym_str)
			extra_length += 4 + strlen(sym_str);

		if (!last_cr)
			last_cr = gs->s;

		last_line_length = strlen(gs->s) - (last_cr - gs->s);

		if ((last_line_length + extra_length) > gs->max_width)
			str_append(gs, "\\\n");
	}

	str_append(gs, str);
	if (sym && sym->type != S_UNKNOWN)
		str_printf(gs, " [=%s]", sym_str);
}

static void kismet_expr_gstr_print_revdep(struct expr *e, struct gstr *gs,
			    tristate pr_type, const char *title)
{
	kismet_expr_print_revdep(e, kismet_expr_print_gstr_helper, gs, pr_type, &title);
}


static void kismet_sym_warn_unmet_dep(struct symbol *sym)
{
	struct gstr gs = str_new();

	str_printf(&gs,
		   "\nWARNING: unmet direct dependencies detected for %s\n",
		   sym->name);
	str_printf(&gs,
		   "  Depends on [%c]: ",
		   sym->dir_dep.tri == mod ? 'm' : 'n');
	expr_gstr_print(sym->dir_dep.expr, &gs);
	str_printf(&gs, "\n");

	kismet_expr_gstr_print_revdep(sym->rev_dep.expr, &gs, yes,
			       "  Selected by [y]:\n");
	kismet_expr_gstr_print_revdep(sym->rev_dep.expr, &gs, mod,
			       "  Selected by [m]:\n");

	fputs(str_get(&gs), stderr);
}

#endif // KISMET_UDD_PRINTER_EXTENSION_H
