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
SRC = confdata.c expr.c preprocess.c symbol.c lexer.lex.c parser.tab.c kextractor.c util.c menu.c
OBJ = $(SRC:%.c=%.o)

.PHONY: all clean configure clobber check-dep

all: $(OBJ) $(GENERATED) $(CPROGS)

parser.tab.o: parser.tab.c lexer.lex.c util.c confdata.c expr.c symbol.c menu.c lkc.h

kextractor: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

parser.tab.c: parser.y
	bison -o parser.tab.c --defines=parser.tab.h -t -l parser.y

lexer.lex.c: lexer.l
	flex -o lexer.lex.c -L lexer.l

clean:
	$(RM) $(CPROGS) *.o

clobber:
	$(RM) $(GENERATED)
