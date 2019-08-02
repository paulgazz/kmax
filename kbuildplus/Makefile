# Kmax
# Copyright (C) 2012-2015 Paul Gazzillo
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

TMPDIR := /tmp
PYMAKE := http://hg.mozilla.org/users/bsmedberg_mozilla.com/pymake/archive/default.tar.bz2

all: pymake/

pymake/:
ifeq ($(shell which wget > /dev/null; echo $$?), 0)
	wget -P $(TMPDIR) $(PYMAKE)
else
ifeq ($(shell which curl > /dev/null; echo $$?), 0)
	curl $(PYMAKE) > $(TMPDIR)/default.tar.bz2
else
	@echo "No download tool found.  Need wget or curl."
	@false
endif
endif
	tar -jxvf $(TMPDIR)/default.tar.bz2 -C $(TMPDIR)
	mv $(TMPDIR)/pymake-default/pymake .
	$(RM) $(TMPDIR)/default.tar.bz2
	$(RM) -R $(TMPDIR)/pymake-default

clobber:
	$(RM) -R pymake/
