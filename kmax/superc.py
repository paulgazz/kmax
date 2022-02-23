from common import BasicLogger
from vcommon import run, write_content_to_file, check_if_compiles
from kmax.arch import Arch
import os
import pathlib
from shutil import which
from kmax.klocalizer import Klocalizer
import subprocess
#
# Static analysis of C source files without SuperC
#
class SyntaxAnalysis:
    # taken from plocalizer/scripts/create_validation_conditions.py
    # TODO: merge this ConditionalBlock implementation with Klocalizer.ConditionalBlock
    class ConditionalBlock:
      """For capturing the start/end of preprocessor conditional blocks."""
      def __init__(self):
        self.start_line = -1
        self.end_line   = -1
        self.sub_block_groups = []
      
      def getdict(self):
        """Get a dictionary representation of the conditional block.
        
        May be used for debugging purposes."""
        r = {}
        r["StartLine"] = self.start_line
        r["EndLine"] = self.end_line
        r["Sub"] = []
        for s in self.sub_block_groups:
          r["Sub"].append([k.getdict() for k in s])
        return r

      def retrieve_deepest_block(self, line : int): # -> ConditionalBlock
        """Retrieve the end line of the deepest encapsulating conditional block
        for the given line.

        If there is no such block (line is out of range of the conditional
        blocks), return None.

        This should always return valid values when called with a valid line
        number on a conditional block tree with a dummy root for covering the
        overall file.
        """
        # TODO: Search for multiple lines can be optimized by doing a
        # traversal for all lines.
        assert line >= 0

        # For the given line, retrieve the end-of-block line that it belongs to.
        if self.start_line <= line < self.end_line:
          # Search within the sub blocks
          ret_from_sub_blocks = []
          for s in self.sub_block_groups:
            for k in s:
              r = k.retrieve_deepest_block(line)
              if r is not None:
                ret_from_sub_blocks.append(r)
          # It may belong to at most one sub block
          assert len(ret_from_sub_blocks) <= 1

          if ret_from_sub_blocks:
            # Belongs to a sub block
            return ret_from_sub_blocks[0]
          else:
            # Belongs to self, not in any nested sub block
            return self
        else:
          return None

    # taken from plocalizer/scripts/eval_common.py
    @staticmethod
    def get_tokens(s):
        """
        TODO: document
        takes a string, and returns a list of (token, line #)
        """
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

    @staticmethod
    def analyze_c_tokens(tokens_w_line_nums):
        """
        TODO: document
        determines what kind of code each token is (c, comment, or preprocessor).
        returns a map between line number and a list of (token mapped to type of code)
        """
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

    # taken from plocalizer/scripts/create_validation_conditions.py
    @staticmethod
    def get_conditional_blocks(src_content, line_count):
        """Output conditional block is the dummy root with special start/end
        values, which covers any conditional blocks in the file.
        """
        assert src_content

        # Analyze the tokens to get preprocessor tokens
        tokens = SyntaxAnalysis.get_tokens(src_content)
        categorized_tokens = SyntaxAnalysis.analyze_c_tokens(tokens)

        # Root is the one that is not due to any preprocessor directives, but the
        # encapsulating block with condition 1. 
        root_conditional_block = SyntaxAnalysis.ConditionalBlock()
        root_conditional_block.start_line = 0 #< Special value
        root_conditional_block.end_line = line_count + 1 #< Special value
        stack = [root_conditional_block]

        # Conditional blocks have a stack-like structure. The above stack helps
        # us to keep track of the current context. For example, if a opening for
        # a conditional block is seen, it is nested under the block at the
        # top the stack.

        for linenum in categorized_tokens:
          for i, token_to_type in enumerate(categorized_tokens[linenum]):
            # Get the token and its type
            assert len(token_to_type) == 1 #< One token mapped to its type.
            token = list(token_to_type.keys())[0]
            token_type = token_to_type[token]

            # Check if it is a conditional preprocessor directive
            if token == '#' and token_type == 'preprocessor':
              # Beginning of a new preprocessor directive, read the next token
              # to see if it is a conditional preprocessor directive.
              # Assumption: preprocessor directives like #if are not broken into
              # two lines right after the # sign (# \ if).
              next_token_to_type = categorized_tokens[linenum][i + 1]
              assert len(next_token_to_type) == 1
              next_token = list(next_token_to_type.keys())[0]
              next_token_type = next_token_to_type[next_token]
              assert next_token_type == "preprocessor"
              if next_token not in ['if', 'ifdef', 'ifndef', 'elif', 'else', 'endif']:
                # Not a conditional preprocessor directive
                continue
              
              if next_token in ['if', 'ifdef', 'ifndef']:
                # Open a new conditional block
                new_cb = SyntaxAnalysis.ConditionalBlock()
                new_cb.start_line = linenum
                stack[-1].sub_block_groups.append([new_cb])
                stack.append(new_cb)
              elif next_token in ['elif', 'else']:
                # Close the currently open conditional block.
                last_cb = stack[-1]
                last_cb.end_line = linenum
                stack.pop()

                # Open a new one in the same block group as the closed one.
                new_cb = SyntaxAnalysis.ConditionalBlock()
                new_cb.start_line = linenum
                parent_cb = stack[-1]
                parent_cb.sub_block_groups[-1].append(new_cb)
                stack.append(new_cb)
              elif next_token == 'endif':
                # Close the currently open conditional block.
                last_cb = stack[-1]
                last_cb.end_line = linenum
                stack.pop()
              else:
                assert False

        # There must remain only one element, which is the dummy root
        assert len(stack) == 1
        return stack[0]
    
    @staticmethod
    def get_conditional_blocks_of_file(srcfile_path: str) -> ConditionalBlock:
      """Returns a ConditionalBlock instance with the dummy root. Anything
      inside the root node is unconditional.  Children nodes depict blocks
      under conditional preprocessor directives, but the actual conditions
      are not set since this is only a syntax analysis.
      """
      assert os.path.isfile(srcfile_path)

      # Read the source file.
      with open(srcfile_path, 'r') as f:
        content = f.read()
      # Read the line count
      # Old method was to count the '\n' in source content but this failed
      # for a file (commit 88f8575bca5f, drivers/gpu/drm/amd/amdgpu/gfx_v9_4_2.c)
      # probably because there was no newline at the end of the file. Use
      # the file system to count the lines as below, which is safer.
      with open(srcfile_path, 'r') as f:
        line_count = len(f.readlines())

      # Get the conditional blocks (start-end lines).
      # Root has the special start/end values: 0 and line_count+1
      cb = SyntaxAnalysis.get_conditional_blocks(content, line_count)

      return cb
