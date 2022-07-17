# unmet direct dependency warnings parser
import os, re
from shutil import which, copyfile
from kmax.vcommon import run

def __get_installed_module_path() -> str:
    import sys
    return os.path.dirname(sys.modules['kmax'].__file__)

def __get_resource_path(r_relpath) -> str:
    mpath = __get_installed_module_path()
    return os.path.join(mpath, r_relpath)

def patch_kconfig_udd_printer_extension(linux_ksrc: str) -> bool:
    """Patch Kconfig code to print explicit unmet direct dependency bug
    warnings.
    """
    assert which("patch")
    
    # Apply the patch.
    pfile = __get_resource_path("resources/kismet_verification_patch.diff")
    assert os.path.isfile(pfile)
    target_file = os.path.join(linux_ksrc, "scripts/kconfig/symbol.c")
    assert os.path.isfile(target_file)
    patch_cmd = "patch -p1 %s < %s" % (target_file, pfile)
    _, _, patch_retcode, _ = run(patch_cmd, shell=True)

    # Copy the extension header file.
    src = __get_resource_path("resources/kismet_udd_printer_extension.h")
    assert os.path.isfile(src)
    dst_extfile = os.path.join(linux_ksrc, "scripts/kconfig/kismet_udd_printer_extension.h")
    copyfile(src, dst_extfile)
    assert os.path.isfile(dst_extfile)

    return patch_retcode == 0 and os.path.isfile(dst_extfile)

def reverse_patch_kconfig_udd_printer_extension(linux_ksrc: str) -> bool:
    """Reverse the patch to the Kconfig code that prints explicit unmet
    direct dependency bug warnings.
    """
    assert which("patch")
    
    # Reverse the patch.
    pfile = __get_resource_path("resources/kismet_verification_patch.diff")
    assert os.path.isfile(pfile)
    target_file = os.path.join(linux_ksrc, "scripts/kconfig/symbol.c")
    assert os.path.isfile(target_file)
    patch_cmd = "patch -R -p1 %s < %s" % (target_file, pfile)
    _, _, patch_retcode, _ = run(patch_cmd, shell=True)

    # Remove the extension header file.
    extfile = os.path.join(linux_ksrc, "scripts/kconfig/kismet_udd_printer_extension.h")
    if os.path.isfile(extfile):
        os.remove(extfile)

    return patch_retcode == 0 and not os.path.exists(extfile)

def does_kconfig_print_uddwarning_in_explicit_format(linux_ksrc) -> bool:
    """Returns whether Kconfig has code for printing unmet direct
    dependency warnings in an explicit format that is amenable to use in
    verifying bugs with test cases.

    The explicit format starts with:
        "WARNING: unmet direct dependencies detected for"
    """
    assert which("grep")
    kconfig_scripts_path = os.path.join(linux_ksrc, "scripts/kconfig/")
    cmd = "grep -rI \"WARNING: unmet direct dependencies detected for\""
    _, _, retcode, _ = run(cmd, cwd = kconfig_scripts_path, shell = True)
    return retcode == 0

# given the content of the make output possibly including multiple warnings
# parses the content and returns {selected: {selecters} }
def parse_warnings(make_output):
    selected_prefix = r"WARNING: unmet direct dependencies detected for "
    selected_suffix = r"\n"
    selected_re = selected_prefix + "(.*?)" + selected_suffix

    warning_start_indices = [m.start() for m in re.finditer(selected_re, make_output)] + [len(make_output)]

    warning_str_ranges = []
    for i in range(len(warning_start_indices) - 1):
        warning_str_ranges.append( (warning_start_indices[i], warning_start_indices[i+1]) )

    res = [ process_warning(make_output[s:e]) for s,e in warning_str_ranges ]

    return dict( (selected, selecters) for selected, _, selecters in res )

# processes the first warning encountered. used as helper to parse_warnings()
def process_warning(warning_str):
    # get the selected
    selected_prefix = r"WARNING: unmet direct dependencies detected for "
    selected_suffix = r"\n"
    selected_re = selected_prefix + "(.*?)" + selected_suffix
    selected = re.search(selected_re, warning_str).group(1).strip()

    # get unsatisfied 'depends on'. whole path.
    dependson_prefix = r"Depends on \[.*\]:"
    dependson_suffix = r"\n"
    dependson_re = dependson_prefix + "(.*?)" + dependson_suffix
    dependson = re.search(dependson_re, warning_str).group(1).strip()

    # get the selecter (just the first one, not the whole path. not the y/m info but just the symbol name)
    # There might be multiple selecters
    selecter_prefix = r"- "
    selecter_suffix = r" \["
    selecter_re = selecter_prefix + "(.*?)" + selecter_suffix
    selecters = set([m.group(1).strip() for m in re.finditer(selecter_re, warning_str)])

    return selected, dependson, selecters
