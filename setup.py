import os
from setuptools import setup, Extension

# Utility function to read the README file.
# Used for the long_description.  It's nice, because now 1) we have a top level
# README file and 2) it's easier to type in the README file than to put a raw
# string in below ...
def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

about = {}
exec(read(os.path.join("kmax", "about.py")), about)

kextractor_next_20251023 = Extension('kextractor_next_20251023', [ 'kextractors/kextractor-next-20251023/kextractor_extension.c', 'kextractors/kextractor-next-20251023/kextractor.c', 'kextractors/kextractor-next-20251023/confdata.c', 'kextractors/kextractor-next-20251023/expr.c', 'kextractors/kextractor-next-20251023/preprocess.c', 'kextractors/kextractor-next-20251023/lexer.lex.c', 'kextractors/kextractor-next-20251023/menu.c', 'kextractors/kextractor-next-20251023/parser.tab.c', 'kextractors/kextractor-next-20251023/symbol.c', 'kextractors/kextractor-next-20251023/util.c'], include_dirs=['kextractors/kextractor-next-20251023/', 'kextractors/kextractor-next-20251023/include/'])

kextractor_next_20210426 = Extension('kextractor_next_20210426', [ 'kextractors/kextractor-next-20210426/kextractor_extension.c', 'kextractors/kextractor-next-20210426/kextractor.c', 'kextractors/kextractor-next-20210426/confdata.c', 'kextractors/kextractor-next-20210426/expr.c', 'kextractors/kextractor-next-20210426/preprocess.c', 'kextractors/kextractor-next-20210426/lexer.lex.c', 'kextractors/kextractor-next-20210426/menu.c', 'kextractors/kextractor-next-20210426/parser.tab.c', 'kextractors/kextractor-next-20210426/symbol.c', 'kextractors/kextractor-next-20210426/util.c'], include_dirs=['kextractors/kextractor-next-20210426/'])

kextractor_next_20200430 = Extension('kextractor_next_20200430', [ 'kextractors/kextractor-next-20200430/kextractor_extension.c', 'kextractors/kextractor-next-20200430/kextractor.c', 'kextractors/kextractor-next-20200430/confdata.c', 'kextractors/kextractor-next-20200430/expr.c', 'kextractors/kextractor-next-20200430/preprocess.c', 'kextractors/kextractor-next-20200430/lexer.lex.c', 'kextractors/kextractor-next-20200430/parser.tab.c', 'kextractors/kextractor-next-20200430/symbol.c', 'kextractors/kextractor-next-20200430/util.c'], include_dirs=['kextractors/kextractor-next-20200430/'])

kextractor_3_19 = Extension('kextractor_3_19', [ 'kextractors/kextractor-3.19/kextractor_extension.c', 'kextractors/kextractor-3.19/kextractor.c', 'kextractors/kextractor-3.19/bconf.tab.c', 'kextractors/kextractor-3.19/zconf.tab.c'], include_dirs=['kextractors/kextractor-3.19/'])

kextractor_4_12_8 = Extension('kextractor_4_12_8', [ 'kextractors/kextractor-4.12.8/kextractor_extension.c', 'kextractors/kextractor-4.12.8/kextractor.c', 'kextractors/kextractor-4.12.8/bconf.tab.c', 'kextractors/kextractor-4.12.8/zconf.tab.c'], include_dirs=['kextractors/kextractor-4.12.8/'])

kextractor_4_18 = Extension('kextractor_4_18', [ 'kextractors/kextractor-4.18/kextractor_extension.c', 'kextractors/kextractor-4.18/kextractor.c', 'kextractors/kextractor-4.18/zconf.tab.c'], include_dirs=['kextractors/kextractor-4.18/'])

kextractor_3_2 = Extension('kextractor_3_2', [ 'kextractors/kextractor-3.2/kextractor_extension.c', 'kextractors/kextractor-3.2/kextractor.c', 'kextractors/kextractor-3.2/bconf.tab.c', 'kextractors/kextractor-3.2/zconf.tab.c'], include_dirs=['kextractors/kextractor-3.2/'])

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
    packages=['kmax', 'pymake'],
    ext_modules = [ kextractor_next_20251023, kextractor_next_20210426, kextractor_next_20200430, kextractor_3_19, kextractor_4_12_8, kextractor_4_18, kextractor_3_2, ],
    classifiers=[
        "Development Status :: 4 - Beta",
        "Topic :: Utilities",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
    ],
    scripts=['kmax/kmax', 'kmax/kmaxall', 'kmax/kclause', 'kmax/klocalizer', 'kmax/kextract', 'kmax/kextractlinux', 'kmax/kreader', 'kmax/kismet', 'kmax/koverage'],
    install_requires=[
        'enum34',
        'regex',
        'z3-solver',
        'dd==0.5.7', # dd requires networkx >= 2.4 starting from 0.6.0
        'networkx==2.2', # for dd to work on python2
        'requests',
        'whatthepatch',
        'packaging',
        'tqdm',
    ],
    include_package_data=True,
)
