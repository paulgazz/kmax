# unmet direct dependency warnings parser
import re

def parse_warnings(make_output: str) -> dict:
    """Parse and return the unmet direct dependency warnings from make
    output (make olddefconfig).

    Returns a dict that maps selectees to list of selectors.

    The unmet direct dependency warning message format was changed with
    the Linux kernel commit f8f69dc0b4e0. This method can parse for both
    formats. However, the method asserts that a single format is used in
    a given make output.
    """
    new_format_ret = parse_warnings_newformat(make_output)
    old_format_ret = parse_warnings_oldformat(make_output)

    # Can't have warnings in both formats in a make output.
    assert not (len(new_format_ret) > 0 and len(old_format_ret) > 0)

    if new_format_ret:
        return new_format_ret
    elif old_format_ret:
        return old_format_ret
    else:
        return {} #< no unmet dependency warnings.


###########################################################################
# NEW FORMAT PARSER (after the linux kernel commit f8f69dc0b4e0) ##########
###########################################################################

# given the content of the make output possibly including multiple warnings
# parses the content and returns {selected: {selecters} }
def parse_warnings_newformat(make_output):
    """Format: after the Linux kernel commit f8f69dc0b4e0
    """
    selected_prefix = r"WARNING: unmet direct dependencies detected for "
    selected_suffix = r"\n"
    selected_re = selected_prefix + "(.*?)" + selected_suffix

    warning_start_indices = [m.start() for m in re.finditer(selected_re, make_output)] + [len(make_output)]

    warning_str_ranges = []
    for i in range(len(warning_start_indices) - 1):
        warning_str_ranges.append( (warning_start_indices[i], warning_start_indices[i+1]) )

    res = [ process_warning_newformat(make_output[s:e]) for s,e in warning_str_ranges ]

    return dict( (selected, selecters) for selected, _, selecters in res )

# processes the first warning encountered. used as helper to parse_warnings()
def process_warning_newformat(warning_str):
    """Format: after the Linux kernel commit f8f69dc0b4e0
    """
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

###########################################################################
# OLD FORMAT PARSER (before the linux kernel commit f8f69dc0b4e0) ########
###########################################################################

def get_all_terms_of_bool_expr(expr):
  """Given a string boolean expression, return all the terms in the order
  they appear. in the expression.

  Expected format: starts with "(" and ends with ")"

  Example input/output:
  "(A && B)" returns ["A", "B"]
  "(A)" returns "A"
  """
  # starts with "(", ends with ")", non-empty content
  assert expr
  assert len(expr) > 2
  assert expr[0] == "("
  assert expr[-1] == ")"

  r = "[\( ]([a-zA-Z0-9_]*)[ \)]"
  match_results = re.findall(r, expr)
  assert match_results
  return match_results

def process_warning_oldformat(warning_str):
  """Format: before the Linux kernel commit f8f69dc0b4e0
  
  Given a single line of unmet direct dependency warning in old format,
  parse and return the tuple of selectee, dependson, and the list of
  selectors.
  
  WARNING: In the old format, there is no way of distinguishing
  the selector from the complete expression that made select possible.
  For example, it also includes selector's dependencies, or other selectors
  for the same selectee. Therefore, the method returns all the terms in
  the selector's expression as the list of selectors. Be careful that it
  might include the options that do not actually select the selectee.
  However, as long as an option that selects the selectee is in the list
  of selectors, it means the selector is enabled and caused the unmet
  dependency.
  """
  r = r"^warning: (.*?) selects (.*?) which has unmet direct dependencies (.*?)$"
  s = re.search(r, warning_str)
  selector_expr = s.group(1).strip()
  selectors = get_all_terms_of_bool_expr(selector_expr)
  selectee = s.group(2).strip()
  dependson = s.group(3).strip()
  return selectee, dependson, selectors

def parse_warnings_oldformat(make_output: str) -> dict:
  """Format: before the Linux kernel commit f8f69dc0b4e0
  
  Given make's output, parse and return all unmet dependency warnings
  in old format.  Output dict maps selectees to list of selectors.
  
  Format is to have a complete warning in a single line:
  ^warning: .* selects .* which has unmet direct dependencies .*$

  Example:
  "(A1 && B1 && C1) selects D1 which has unmet direct dependencies (E1 && F1)"

  """
  ret = {}

  def check_line(l):
    """Given a single line, check if unmet warning exists"""
    r = r"^warning: .* selects .* which has unmet direct dependencies .*$"
    ret = re.findall(r, l)
    return len(ret) > 0
  
  # Iterate over each line and check.
  for l in make_output.split('\n'):
    l = l.strip()
    if check_line(l.strip()):
      # There is a udd warning: add it to the results
      selectee, _, selectors = process_warning_oldformat(l)
      ret[selectee] = ret.get(selectee, [])
      for s in selectors:
        ret[selectee].append(s)

  return ret

###########################################################################
# TESTS ###################################################################
###########################################################################

def test_parse_warnings_oldformat():
  print("running test_parse_warnings_oldformat()")
  multiple_warnings_str = \
    """warning: (A1 && B1 && C1) selects D1 which has unmet direct dependencies (E1 && F1)\n
       warning: (A2) selects B2 which has unmet direct dependencies (C2 && D2)\n
       warning: (A3 && B3) selects C3 which has unmet direct dependencies (D3)\n
       warning: (M4) selects N4 which has unmet direct dependencies (A4)\n
       warning: (M4) selects A5 which has unmet direct dependencies (B5)\n
       warning: (M5) selects N4 which has unmet direct dependencies (A6)"""

  ret = parse_warnings_oldformat(multiple_warnings_str)
  # SELECTOR -> SELECTEE
  # A1 -> D1
  # A2 -> B2
  # A3 -> C3
  # M4 -> N4
  # M4 -> A5
  # M5 -> N4

  # Check unique selectors
  unique_selectees = ["D1", "B2", "C3", "N4", "A5"]
  assert sorted(list(ret.keys())) == sorted(unique_selectees)

  # Check selectors lists
  assert sorted(ret["D1"]) == sorted(["A1", "B1", "C1"])
  assert sorted(ret["B2"]) == sorted(["A2"])
  assert sorted(ret["C3"]) == sorted(["A3", "B3"])
  assert sorted(ret["N4"]) == sorted(["M4", "M5"])
  assert sorted(ret["A5"]) == sorted(["M4"])

def test_process_warning_oldformat():
  print("running test_process_warning_oldformat()")
  s1 = "warning: (DRM_RADEON && DRM_AMDGPU && DRM_NOUVEAU && DRM_I915 && DRM_GMA500 && DRM_SHMOBILE && DRM_TILCDC && DRM_FSL_DCU && DRM_TINYDRM && DRM_PARADE_PS8622 && FB_BACKLIGHT && FB_ARMCLCD && FB_MX3 && USB_APPLEDISPLAY && FB_OLPC_DCON && ACPI_CMPC && SAMSUNG_Q10) selects BACKLIGHT_CLASS_DEVICE which has unmet direct dependencies (HAS_IOMEM && BACKLIGHT_LCD_SUPPORT)"
  selectee1, dependson1, selector1 = process_warning_oldformat(s1)
  assert selectee1 == "BACKLIGHT_CLASS_DEVICE"
  assert dependson1 == "(HAS_IOMEM && BACKLIGHT_LCD_SUPPORT)"
  assert selector1 == ["DRM_RADEON", "DRM_AMDGPU", "DRM_NOUVEAU", "DRM_I915", "DRM_GMA500", "DRM_SHMOBILE", "DRM_TILCDC", "DRM_FSL_DCU", "DRM_TINYDRM", "DRM_PARADE_PS8622", "FB_BACKLIGHT", "FB_ARMCLCD", "FB_MX3", "USB_APPLEDISPLAY", "FB_OLPC_DCON", "ACPI_CMPC", "SAMSUNG_Q10"]

  s2 = "warning: (STM32_DFSDM_ADC) selects IIO_BUFFER_HW_CONSUMER which has unmet direct dependencies (IIO && IIO_BUFFER)"
  selectee2, dependson2, selector2 = process_warning_oldformat(s2)
  assert selectee2 == "IIO_BUFFER_HW_CONSUMER"
  assert dependson2 == "(IIO && IIO_BUFFER)"
  assert selector2 == ["STM32_DFSDM_ADC"]

def test_get_all_terms_of_bool_expr():
  print("running test_get_all_terms_of_bool_expr()")
  assert ["HAS_IOMEM", "BACKLIGHT_LCD_SUPPORT"] == get_all_terms_of_bool_expr("(HAS_IOMEM && BACKLIGHT_LCD_SUPPORT)")
  assert ["HAS_IOMEM"] == get_all_terms_of_bool_expr("(HAS_IOMEM)")
