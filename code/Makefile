CC     ?= gcc
CFLAGS ?= -O3 -Wall

all: exhaust exhaust2 verify_small

exhaust: exhaust_new.c
	$(CC) $(CFLAGS) -o $@ $<

exhaust2: exhaust2.c
	$(CC) $(CFLAGS) -o $@ $<

verify_small: verify_small.c
	$(CC) $(CFLAGS) -o $@ $<

# quick smoke test: exhaustive enumeration for n <= 5 and verification n <= 8
check: all
	./exhaust 4
	./exhaust 5
	./verify_small 8 1 8 exact
	python3 check_all.py --quick
	python3 -m unittest test_verify_h4_exit.py

clean:
	rm -f exhaust exhaust2 verify_small

.PHONY: all check clean
