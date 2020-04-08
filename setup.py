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

kconfig_extractor_v1 = Extension('kconfig_extractor_v1', [ 'kconfig_extractor/kconfig_extractor_v1/kconfig_extractor_extension.c', 'kconfig_extractor/kconfig_extractor_v1/confdata.c', 'kconfig_extractor/kconfig_extractor_v1/expr.c', 'kconfig_extractor/kconfig_extractor_v1/symbol.c'], include_dirs=['kconfig_extractor/kconfig_extractor_v1/'])
kconfig_extractor_v2 = Extension('kconfig_extractor_v2', [ 'kconfig_extractor/kconfig_extractor_v2/kconfig_extractor_extension.c', 'kconfig_extractor/kconfig_extractor_v2/confdata.c', 'kconfig_extractor/kconfig_extractor_v2/expr.c', 'kconfig_extractor/kconfig_extractor_v2/preprocess.c', 'kconfig_extractor/kconfig_extractor_v2/symbol.c', 'kconfig_extractor/kconfig_extractor_v2/lexer.lex.c', 'kconfig_extractor/kconfig_extractor_v2/parser.tab.c', 'kconfig_extractor/kconfig_extractor_v2/kconfig_extractor.c'], include_dirs=['kconfig_extractor/kconfig_extractor_v2/'])

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
    ext_modules = [kconfig_extractor_v1, kconfig_extractor_v2],
    classifiers=[
        "Development Status :: 4 - Beta",
        "Topic :: Utilities",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
    ],
    scripts=['kmaxtools/kmax', 'kmaxtools/kmaxall', 'kmaxtools/kclause', 'kmaxtools/klocalizer', 'kmaxtools/kextractor'],
    install_requires=[
        'enum34',
        'regex',
        'z3-solver',
        'dd',
        'networkx==2.2', # for dd to work on python2
    ],
)
