import os
from setuptools import setup

# Utility function to read the README file.
# Used for the long_description.  It's nice, because now 1) we have a top level
# README file and 2) it's easier to type in the README file than to put a raw
# string in below ...
def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

setup(
    name = "kmax",
    version = "2.0rc3",
    author = "Paul Gazzillo",
    author_email = "paul@pgazz.com",
    description = ("Collecting symbolic configurations from Kbuild Makefiles"),
    license = "GPLv2+",
    keywords = "makefile kbuild kmax configurations",
    url = "https://github.com/paulgazz/kmax",
    packages=['kmax', 'pymake', 'tests'],
    long_description=read('README.md'),
    classifiers=[
        "Development Status :: 4 - Beta",
        "Topic :: Utilities",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
    ],
    scripts=['kmax/kmaxdriver.py', 'kmax/kbuildplus.py'],
    install_requires=[
        'enum34',
        'regex',
        'z3-solver',
    ],
)