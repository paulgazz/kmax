# Kconfig Semantics

## Default Booleans

Some variables are not visible to the user (no `prompt`), but have a
default value.  These should be forced to be true (given the default
conditions).

This is distinct from non-visible Booleans, which have no prompt, but
also have no default.  These are essentially internal state variables
and can be treated the same as visible Booleans.


## Boolean choices

This requires mutual exclusion.

This is different from tristate choices, where multiple module
selections are permitted.

## Non-Boolean values

Non-Boolean values should always be set to something, as it appears
Kconfig expects this.
