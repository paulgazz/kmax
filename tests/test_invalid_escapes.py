"""Compile the four real sources with SyntaxWarning treated as an error.

The module under test is not imported here. A child interpreter compiles
the on-disk bytes, so collection stays green when a source still warns.
Runtime string values are taken from the abstract syntax tree, not from
source spelling.
"""

import ast
import os
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(__file__).resolve().parents[1]
PYTHON = os.environ.get("KMAX_REGRESSION_PYTHON", sys.executable)
SOURCES = (
    "pymake/data.py",
    "pymake/parser.py",
    "pymake/process.py",
    "kmax/vcommon.py",
)


def _child_env():
    env = os.environ.copy()
    env["PYTHONPATH"] = str(WORKTREE)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    cache = env.get("PYTHONPYCACHEPREFIX")
    if cache:
        Path(cache).mkdir(parents=True, exist_ok=True)
    return env


def compile_sources():
    code = (
        "import pathlib, sys, warnings\n"
        "warnings.simplefilter('error', SyntaxWarning)\n"
        "for rel in sys.argv[1:]:\n"
        "    pathlib.Path(rel).read_text(encoding='utf-8')\n"
        "    src = pathlib.Path(rel).read_bytes()\n"
        "    compile(src, rel, 'exec')\n"
        "    print('OK', rel)\n"
    )
    return subprocess.run(
        [PYTHON, "-B", "-c", code, *SOURCES],
        cwd=str(WORKTREE),
        env=_child_env(),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def test_four_sources_compile_with_syntax_warning_as_error():
    completed = compile_sources()
    assert completed.returncode == 0, completed.stderr + completed.stdout
    for rel in SOURCES:
        assert f"OK {rel}" in completed.stdout


def string_constants(source_text):
    tree = ast.parse(source_text)
    values = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            values.append((node.lineno, node.col_offset, node.value))
    values.sort()
    return values


def test_string_constants_match_baseline_blobs():
    """Compare parsed string values against the blobs passed in by the runner.

    The blobs are the baseline file bytes. This test does not look at raw
    prefixes or backslash spelling.
    """
    blobs = os.environ.get("KMAX_BASELINE_BLOBS")
    if not blobs:
        return
    root = Path(blobs)
    for rel in SOURCES:
        current = (WORKTREE / rel).read_text(encoding="utf-8")
        baseline = (root / rel).read_text(encoding="utf-8")
        assert string_constants(current) == string_constants(baseline), rel


def test_parsedepfile_splits_variable_reference(tmp_path):
    dep = tmp_path / "sample.d"
    dep.write_text("obj/$(BAR)_out.o: src/$(BAR).c helper.h\n", encoding="utf-8")
    code = (
        "import sys\n"
        "from pymake.parser import parsedepfile\n"
        "stmts = parsedepfile(sys.argv[1])\n"
        "rule = stmts[0]\n"
        "target = rule.targetexp\n"
        "deps = rule.depexp\n"
        "print('TCOUNT', len(target))\n"
        "print('DCOUNT', len(deps))\n"
        "for part in target:\n"
        "    piece = part[0]\n"
        "    print('T', type(piece).__name__, getattr(piece, 's', piece if isinstance(piece, str) else ''))\n"
        "for part in deps:\n"
        "    piece = part[0]\n"
        "    print('D', type(piece).__name__, getattr(piece, 's', piece if isinstance(piece, str) else ''))\n"
    )
    completed = subprocess.run(
        [PYTHON, "-B", "-c", code, str(dep)],
        cwd=str(WORKTREE),
        env=_child_env(),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr
    stdout = completed.stdout
    assert "TCOUNT 3" in stdout
    assert "DCOUNT 3" in stdout
    assert "T StringExpansion " not in stdout
    assert "T str obj/" in stdout
    assert "T VariableRef " in stdout
    assert "T str _out.o" in stdout
    assert "D str  src/" in stdout
    assert "D VariableRef " in stdout
    assert "D str .c helper.h" in stdout


def test_skipws_and_define_and_command_split_keep_runtime_meaning():
    code = (
        "from pymake.parser import Data, _redefines, _skipws\n"
        "from pymake.parserdata import Location\n"
        "from pymake.process import clinetoargv\n"
        "loc = Location('<mem>', 1, 0)\n"
        "ws = Data('  \\tkeep', 0, 7, loc)\n"
        "print('SKIP', ws.skipwhitespace(0))\n"
        "blank = Data(' \\t', 0, 2, loc)\n"
        "print('BLANK', blank.skipwhitespace(0))\n"
        "print('DEFINE', int(_redefines.match('  define FOO', 0) is not None))\n"
        "print('ENDEF', int(_redefines.match('\\tendef', 0) is not None))\n"
        "print('OTHER', int(_redefines.match('  include', 0) is None))\n"
        "args, bad = clinetoargv('echo $(NAME)', '/tmp')\n"
        "print('ARGV', args)\n"
        "print('BAD', bad)\n"
        "plain, plain_bad = clinetoargv('echo hello', '/tmp')\n"
        "print('PLAIN', plain)\n"
        "print('PLAINBAD', plain_bad)\n"
    )
    completed = subprocess.run(
        [PYTHON, "-B", "-c", code],
        cwd=str(WORKTREE),
        env=_child_env(),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr
    stdout = completed.stdout
    assert "SKIP 3" in stdout
    assert "BLANK 2" in stdout
    assert "DEFINE 1" in stdout
    assert "ENDEF 1" in stdout
    assert "OTHER 1" in stdout
    assert "ARGV None" in stdout
    assert "BAD $" in stdout
    assert "PLAIN ['echo', 'hello']" in stdout
    assert "PLAINBAD None" in stdout


def test_vcommon_command_text_is_data_only():
    code = (
        "import ast\n"
        "import pathlib\n"
        "tree = ast.parse(pathlib.Path('kmax/vcommon.py').read_text(encoding='utf-8'))\n"
        "found = []\n"
        "for node in ast.walk(tree):\n"
        "    if isinstance(node, ast.Assign):\n"
        "        for target in node.targets:\n"
        "            if isinstance(target, ast.Name) and target.id == 'cmd':\n"
        "                found.append(node.value.value)\n"
        "assert len(found) == 1\n"
        "cmd = found[0]\n"
        "assert 'find . -type f -regex' in cmd\n"
        "assert 'Makefile' in cmd and 'Kconfig' in cmd and 'Kbuild' in cmd\n"
        "assert cmd.count(chr(92)) == 5\n"
        "print('CMD_OK', len(cmd))\n"
    )
    completed = subprocess.run(
        [PYTHON, "-B", "-c", code],
        cwd=str(WORKTREE),
        env=_child_env(),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr
    assert "CMD_OK" in completed.stdout
