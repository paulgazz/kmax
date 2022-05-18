CPROGS := kextractor 
GENERATED := zconf.tab.c zconf.lex.c

.PHONY: all clean configure clobber check-dep

all: $(GENERATED) $(CPROGS)

zconf.tab.o: zconf.tab.c zconf.lex.c util.c confdata.c expr.c symbol.c menu.c lkc.h

kextractor: kextractor.o zconf.tab.o
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.tab.c: %.y
	bison -l -b $* -p $* -t $<

%.lex.c: %.l
	flex -o $@ $<

clean:
	$(RM) $(CPROGS) *.o

clobber:
	$(RM) $(GENERATED)
