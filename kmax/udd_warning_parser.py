# unmet direct dependency warnings parser
import os, re, pprint, textwrap, argparse

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