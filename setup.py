import os
from setuptools import setup, Extension

# Utility function to read the README file.
# Used for the long_description.  It's nice, because now 1) we have a top level
# README file and 2) it's easier to type in the README file than to put a raw
# string in below ...
def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

about = {}
exec(read(os.path.join("kmaxtools", "about.py")), about)

kextractor = Extension('kextractor', [ 'kextractor/kextractor_extension.c', 'kextractor/kextractor.c', 'kextractor/confdata.c', 'kextractor/expr.c', 'kextractor/preprocess.c', 'kextractor/lexer.lex.c', 'kextractor/parser.tab.c', 'kextractor/symbol.c', 'kextractor/util.c'], include_dirs=['kextractor/'])

setup(
    name = about['__title__'],
    version = about['__version__'],
    author = "Paul Gazzillo",
    author_email = "paul@pgazz.com",
    description = ("Tools for working with symbolic  constraints from Kbuild Makefile."),
    long_description_content_type = 'text/markdown',
    long_description = read('README.md'),
    license = "GPLv2+",
    keywords = "makefile kconfig kbuild configurations kmax kclause klocalizer",
    url = "https://github.com/paulgazz/kmax",
    packages=['kmaxtools', 'pymake'],
    ext_modules = [ kextractor ],
    classifiers=[
        "Development Status :: 4 - Beta",
        "Topic :: Utilities",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
    ],
    scripts=['kmaxtools/kmax', 'kmaxtools/kmaxall', 'kmaxtools/kclause', 'kmaxtools/klocalizer', 'kmaxtools/kextract'],
    install_requires=[
        'enum34',
        'regex',
        'z3-solver',
        'dd',
        'networkx==2.2', # for dd to work on python2
    ],
)
