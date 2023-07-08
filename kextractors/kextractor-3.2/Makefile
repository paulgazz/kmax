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

CPROGS := kextractor
# GENERATED := zconf.hash.c zconf.tab.c zconf.lex.c
GENERATED := zconf.tab.c zconf.lex.c

.PHONY: all clean configure clobber check-dep

all: $(GENERATED) $(CPROGS)

zconf.tab.o: zconf.tab.c zconf.hash.c zconf.lex.c util.c confdata.c expr.c symbol.c menu.c lkc.h

bconf.tab.o: bconf.tab.c bconf.lex.c

kextractor: kextractor.o zconf.tab.o bconf.tab.o
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

zconf.hash.c: zconf.gperf
	gperf -t --output-file $@ -a -C -E -g -k '1,3,$$' -p -t $<

%.tab.c: %.y
	bison -l -b $* -p $* -t $<

%.lex.c: %.l
	flex -o $@ $<

clean:
	$(RM) $(CPROGS) *.o

clobber:
	$(RM) $(GENERATED)
