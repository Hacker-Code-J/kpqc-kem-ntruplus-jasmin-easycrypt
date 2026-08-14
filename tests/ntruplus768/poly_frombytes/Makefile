# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
CHECKER := check_poly_frombytes.py
C_SOURCE := ../../../NTRU+/NTRU+768/poly.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-poly-frombytes-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --kem-source "$(KEM_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) poly_frombytes_diff.c "$(C_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/poly_frombytes_diff"
	"$(OUTDIR)/poly_frombytes_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) poly_frombytes_diff.c "$(C_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/poly_frombytes_diff_ubsan"
	"$(OUTDIR)/poly_frombytes_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
