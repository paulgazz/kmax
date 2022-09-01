import sys
import json
from typing import List, Tuple, Dict


# encodes the results as a json structure, and writes it to the given file path, as well as stdout.
def write_inclusion_results(results: Dict[str, List[Tuple[int, int]]], output_path: str) -> None:
    results_as_json = json.dumps(results)
    with open(output_path, 'w') as out:
        json.dump(results_as_json, out)
    sys.stdout.write("Storing results to " + output_path + ': ' + results_as_json)


# takes a string, and returns a list of (token, line #)
def get_tokens(s):
    buf = ""
    token_list = []
    line_num = 1
    prev_char = ''
    for c in s:
        # append the existing buffered token when we reach a space or tab
        if c == ' ' or c == '\t':
            if buf != "":
                token_list.append((buf, line_num))
                buf = ""
        else:
            # append the existing token if we reach a newline character, and increment the line number counter.
            if c == '\n':
                if buf != "":
                    token_list.append((buf, line_num))
                    buf = ""
                line_num += 1 # TODO: make this function return a list of tokens with their line numbers.
            # logic for special characters (comments, strings, and preprocessor directives)
            # appends the existing buffered token, then appends the special character(s) as new tokens.
            elif c == '#' or c == '\'' or c == '"' or c == '\\' or (c == '/' and prev_char == '/') or (prev_char == '/' and c == '*') or (prev_char == '*' and c == '/'):
                if buf != '/' and buf != '*' and buf != "":
                    token_list.append((buf, line_num))
                    buf = ""
                buf += c
                token_list.append((buf, line_num))
                buf = ""
            # the next character could be /, so we want to start a new token just for this.
            elif c == '*' or c == '/':
                if buf != "":
                    token_list.append((buf, line_num))
                    buf = ""
                buf += c
            # if the current character is not special in any way, then we just add it to the buffer.
            else:
                buf += c
        # keep track of the previous character, so we can determine when we have /*, */, or //
        prev_char = c

    # ensure that we catch the final string
    if buf != "":
        token_list.append((buf, line_num))
    return token_list


# determines what kind of code each token is (c, comment, or preprocessor).
# returns a map between line number and a list of (token mapped to type of code)
def analyze_c_tokens(tokens_w_line_nums):
    analyzed_tokens = {}

    in_quotes = False
    in_single_line_comment = False
    in_preprocessor = False
    prev_line_num = 0
    in_comment = False
    continued_preprocessor = False
    for token, line_num in tokens_w_line_nums:
        if len(token) < 1:
            continue
        if line_num == prev_line_num:
            pass
        else:
            if not continued_preprocessor:
                in_preprocessor = False
            if in_single_line_comment:
                in_comment = False
                in_single_line_comment = False
            analyzed_tokens[line_num] = []

        # preprocessor check
        if (not in_comment) and (not in_quotes) and token[0] == '#':
            in_preprocessor = True

        # NOTE: this gets tricky.
        # 1. if we start quotes while already in a comment or preprocessor, then it's still a comment.
        # 2. if we start a comment or preprocessor while already in quotes, then it's still quotes.

        # invert the quote status whenever we reach a new quote
        if (not in_preprocessor) and (not in_comment) and ("\"" in token):
            in_quotes = not in_quotes

        if (not in_quotes) and (not in_comment) and ("//" in token):
            in_single_line_comment = True
            in_comment = True

        if (not in_quotes) and (not in_comment) and ("/*" in token):
            in_comment = True

        # add the token with code type
        if in_comment:
            analyzed_tokens[line_num].append({token: "comment"})
        elif in_preprocessor:
            analyzed_tokens[line_num].append({token: "preprocessor"})
        else:
            analyzed_tokens[line_num].append({token: "c"})

        if in_comment and ("*/" in token):
            in_comment = False

        if token == '\\':
            continued_preprocessor = True
        else:
            continued_preprocessor = False

        prev_line_num = line_num
    return analyzed_tokens


# takes two dictionaries of lines to be checked for compilation, and returns a dictionary containing the the trivial lines.
def get_eval_lines(patch_conditions: str) -> Dict[str, List[int]]:
    with open(patch_conditions, 'r') as f:
        lines_json = json.loads(f.read())
        # debugging
        #print("INPUT LINES JSON:", lines_json)
    
    if len(lines_json) == 0:
        return {}

    eval_lines = {}
    c_file_line_map = lines_json.get("sourcefile_loc", [])

    # parse the json structure for c source file lines
    for comp_unit, lines in c_file_line_map.items():
        eval_lines[comp_unit] = lines

    # not every patch will modify a header, so unlike C source files, we need to check if there are headers.
    if "headerfile_loc" in lines_json:
        h_file_line_map = lines_json["headerfile_loc"]
        # parse the json structure for header lines
        for header, lines in h_file_line_map.items():
            eval_lines[header] = lines


    return eval_lines
