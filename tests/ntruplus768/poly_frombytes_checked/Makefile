CC ?= cc
JASMINC ?= jasminc
PYTHON ?= python3
OUTDIR ?= /tmp/ntruplus768-poly-frombytes-checked-test
CFLAGS := -std=c11 -O2 -g -Wall -Wextra -Wpedantic -Werror -ffunction-sections -fdata-sections
SANFLAGS := -O1 -fno-omit-frame-pointer -fsanitize=undefined -fno-sanitize-recover=undefined
LDFLAGS := -Wl,--gc-sections -Wl,-z,noexecstack
SOURCE := ../../../ntruplus/jasmin/768/ref/poly_frombytes.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes
DRIVER := poly_frombytes_checked_diff.c
REFERENCE := reference/poly.c

.PHONY: all check selfcheck assembly build-normal build-ubsan run ubsan
all: selfcheck run ubsan

check:
	$(PYTHON) check_poly_frombytes_checked.py

selfcheck:
	$(PYTHON) check_poly_frombytes_checked.py --self-check

assembly:
	mkdir -p "$(OUTDIR)"
	$(JASMINC) -arch x86-64 -call-conv linux -system linux -slice $(SLICE) -o "$(OUTDIR)/poly_frombytes.s" "$(SOURCE)"

build-normal: assembly
	$(CC) $(CFLAGS) -Ireference $(DRIVER) $(REFERENCE) "$(OUTDIR)/poly_frombytes.s" $(LDFLAGS) -o "$(OUTDIR)/checked-normal"

build-ubsan: assembly
	$(CC) $(CFLAGS) $(SANFLAGS) -Ireference $(DRIVER) $(REFERENCE) "$(OUTDIR)/poly_frombytes.s" $(LDFLAGS) -o "$(OUTDIR)/checked-ubsan"

run: check build-normal
	"$(OUTDIR)/checked-normal"

ubsan: check build-ubsan
	UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 "$(OUTDIR)/checked-ubsan"
