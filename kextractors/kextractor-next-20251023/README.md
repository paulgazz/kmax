In `expr.h`, `struct symbol` is given two more fields:

    bool searched;
    bool depends;

Copied `scripts/include` to this folder.  Updated Makefile to add this folder as an include `-I include`.

Updated `expr.cexpr_compare_type` in kextractor.c since E_LIST is no longer a data type.

Added include for `"internal.h"` to kextractor.c which contains `for_all_symbols`, etc.

Changed `sym_escape_string_value` to `escape_string_value`.

Copied `escape_string_value` into `kextractor.c`.

Added include for `<xalloc.h>` to `kextract.c`.

Added `for_all_symbols` from `internal.h` to `kextract.c`.

Changed `expr_list_for_each_sym` to `menu_for_each_sub_entry` for change in the data structure for choice.
