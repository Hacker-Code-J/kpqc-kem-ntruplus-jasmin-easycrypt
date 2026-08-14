# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMIN_SOURCE := $(JASMIN_DIR)/poly_tobytes.jazz
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_poly_tobytes.py
DIFF := poly_tobytes_diff.c
JASMINC ?= /usr/local/bin/jasminc
JASMINCT ?= /usr/local/bin/jasmin-ct
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-poly-tobytes-test.XXXXXX))

.PHONY: check selfcheck asm safety ct sct run ubsan clean

check:
	$(PYTHON) $(CHECKER) --poly-source "$(POLY_SOURCE)" --kem-source "$(KEM_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --poly-source "$(POLY_SOURCE)" --kem-source "$(KEM_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

asm:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/poly_tobytes.s" "$(JASMIN_SOURCE)"
	@printf 'assembly: %s\n' "$(OUTDIR)/poly_tobytes.s"

safety:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -checksafety -slice $(SLICE) -o "$(OUTDIR)/poly_tobytes-safety.s" "$(JASMIN_SOURCE)"

ct:
	$(JASMINCT) --slice=$(SLICE) "$(JASMIN_SOURCE)"

sct:
	$(JASMINCT) --slice=$(SLICE) --sct "$(JASMIN_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/poly_tobytes.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/poly_tobytes.s" -o "$(OUTDIR)/poly_tobytes.o"
	$(CC) $(CFLAGS) "$(DIFF)" "$(POLY_SOURCE)" "$(OUTDIR)/poly_tobytes.o" $(LDFLAGS) -o "$(OUTDIR)/poly_tobytes_diff"
	"$(OUTDIR)/poly_tobytes_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/poly_tobytes.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/poly_tobytes.s" -o "$(OUTDIR)/poly_tobytes.o"
	$(CC) $(CFLAGS) $(SANFLAGS) "$(DIFF)" "$(POLY_SOURCE)" "$(OUTDIR)/poly_tobytes.o" $(LDFLAGS) -o "$(OUTDIR)/poly_tobytes_diff_ubsan"
	"$(OUTDIR)/poly_tobytes_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
