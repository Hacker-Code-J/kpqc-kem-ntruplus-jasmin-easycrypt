# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
INVNTT_RADIX2_8_SOURCE := $(JASMIN_DIR)/invntt_radix2_8.jazz
INVNTT_RADIX2_4_SOURCE := $(JASMIN_DIR)/invntt_radix2_4.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_invntt_radix2_8.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
INVNTT_RADIX2_8_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8
INVNTT_RADIX2_4_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-invntt-radix2-8-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(INVNTT_RADIX2_8_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(INVNTT_RADIX2_8_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_8_SLICE) -o "$(OUTDIR)/invntt_radix2_8.s" "$(INVNTT_RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_4_SLICE) -o "$(OUTDIR)/invntt_radix2_4.s" "$(INVNTT_RADIX2_4_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_8.s" -o "$(OUTDIR)/invntt_radix2_8.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_4.s" -o "$(OUTDIR)/invntt_radix2_4.o"
	$(CC) $(CFLAGS) invntt_radix2_8_diff.c "$(OUTDIR)/invntt_radix2_8.o" \
		"$(OUTDIR)/invntt_radix2_4.o" $(LDFLAGS) -o "$(OUTDIR)/invntt_radix2_8_diff"
	"$(OUTDIR)/invntt_radix2_8_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_8_SLICE) -o "$(OUTDIR)/invntt_radix2_8.s" "$(INVNTT_RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_4_SLICE) -o "$(OUTDIR)/invntt_radix2_4.s" "$(INVNTT_RADIX2_4_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_8.s" -o "$(OUTDIR)/invntt_radix2_8.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_4.s" -o "$(OUTDIR)/invntt_radix2_4.o"
	$(CC) $(CFLAGS) $(SANFLAGS) invntt_radix2_8_diff.c "$(OUTDIR)/invntt_radix2_8.o" \
		"$(OUTDIR)/invntt_radix2_4.o" $(LDFLAGS) -o "$(OUTDIR)/invntt_radix2_8_diff_ubsan"
	"$(OUTDIR)/invntt_radix2_8_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
