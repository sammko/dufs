CFLAGS=-W -Wall -Wextra -Werror -Wno-unused-parameter -pedantic -g

all: wrapper test

clean:
	rm -f *.o wrapper test

wrapper: util.o dufs.h filesystem.o wrapper.o
	$(CC) $(CFLAGS) $^ -o $@

test: util.o dufs.h filesystem.o test.o
	$(CC) $(CFLAGS) $^ -o $@

