"""Check glob detection in fresh interpreters with strict warning handling."""

import os
import subprocess
import sys
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class TestPymakeGlob(unittest.TestCase):
    def run_child(self, code):
        env = os.environ.copy()
        env["PYTHONPATH"] = str(ROOT)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        result = subprocess.run(
            [sys.executable, "-B", "-W", "error::FutureWarning", "-c",
             textwrap.dedent(code)],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=30,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_globrelative_import(self):
        self.run_child(r"""
            from pathlib import Path
            from pymake import globrelative
            assert Path(globrelative.__file__) == Path.cwd() / "pymake/globrelative.py"
        """)

    def test_kmax_import(self):
        self.run_child(r"""
            from pathlib import Path
            import kmax.alg
            from pymake import data
            assert Path(kmax.alg.__file__) == Path.cwd() / "kmax/alg.py"
            assert Path(data.__file__) == Path.cwd() / "pymake/data.py"
        """)

    def test_glob_character_membership_and_match_anchor(self):
        self.run_child(r"""
            from pymake import data, globrelative
            characters = [chr(code) for code in range(128)] + ["\u4e2d", "\u00e9", "\U0001f600"]
            for character in characters:
                expected = character in "[*?"
                for value in (character, "prefix" + character + "suffix"):
                    assert globrelative.hasglob(value) is expected, repr(value)
                    assert bool(data.Makefile._globcheck.search(value)) is expected, repr(value)
                assert bool(data.Makefile._globcheck.match(character)) is expected
                assert data.Makefile._globcheck.match("prefix" + character) is None
            assert globrelative.hasglob("") is False
            assert data.Makefile._globcheck.search("") is None
        """)

    def test_real_globs_and_makefile_target(self):
        self.run_child(r"""
            import os
            from pathlib import Path
            import tempfile
            from pymake import data, globrelative
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "inc").mkdir()
                (root / "a.c").write_text("", encoding="utf-8")
                (root / "b.o").write_text("", encoding="utf-8")
                (root / ".hidden").write_text("", encoding="utf-8")
                (root / "inc/one.mk").write_text("FIRST := yes\n", encoding="utf-8")
                (root / "inc/two.mk").write_text("SECOND := yes\n", encoding="utf-8")
                (root / "live.link").symlink_to("a.c")
                (root / "gone.link").symlink_to("absent.c")
                assert globrelative.glob(directory, "*.c") == ["a.c"]
                assert globrelative.glob(directory, "[ab].*") == ["a.c", "b.o"]
                assert globrelative.glob(directory, "?.o") == ["b.o"]
                assert globrelative.glob(directory, "*.link") == ["live.link"]
                assert globrelative.glob(directory, ".*") == [".", "..", ".hidden"]
                assert globrelative.glob(directory, "inc/*.mk") == ["inc/one.mk", "inc/two.mk"]
                assert globrelative.glob(directory, "a.c") == ["a.c"]
                assert globrelative.glob(directory, "missing") == []
                makefile = data.Makefile(workdir=os.fspath(root))
                assert makefile.gettarget("a.c").target == "a.c"
        """)


if __name__ == "__main__":
    unittest.main()
