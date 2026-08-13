# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
INVNTT_RADIX2_64_SOURCE := $(JASMIN_DIR)/invntt_radix2_64.jazz
INVNTT_RADIX2_32_SOURCE := $(JASMIN_DIR)/invntt_radix2_32.jazz
INVNTT_RADIX2_16_SOURCE := $(JASMIN_DIR)/invntt_radix2_16.jazz
INVNTT_RADIX2_8_SOURCE := $(JASMIN_DIR)/invntt_radix2_8.jazz
INVNTT_RADIX2_4_SOURCE := $(JASMIN_DIR)/invntt_radix2_4.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_invntt_radix2_64.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
INVNTT_RADIX2_64_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64
INVNTT_RADIX2_32_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32
INVNTT_RADIX2_16_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16
INVNTT_RADIX2_8_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8
INVNTT_RADIX2_4_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-invntt-radix2-64-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(INVNTT_RADIX2_64_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(INVNTT_RADIX2_64_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_64_SLICE) -o "$(OUTDIR)/invntt_radix2_64.s" "$(INVNTT_RADIX2_64_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_32_SLICE) -o "$(OUTDIR)/invntt_radix2_32.s" "$(INVNTT_RADIX2_32_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_16_SLICE) -o "$(OUTDIR)/invntt_radix2_16.s" "$(INVNTT_RADIX2_16_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_8_SLICE) -o "$(OUTDIR)/invntt_radix2_8.s" "$(INVNTT_RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_4_SLICE) -o "$(OUTDIR)/invntt_radix2_4.s" "$(INVNTT_RADIX2_4_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_64.s" -o "$(OUTDIR)/invntt_radix2_64.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_32.s" -o "$(OUTDIR)/invntt_radix2_32.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_16.s" -o "$(OUTDIR)/invntt_radix2_16.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_8.s" -o "$(OUTDIR)/invntt_radix2_8.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt_radix2_4.s" -o "$(OUTDIR)/invntt_radix2_4.o"
	$(CC) $(CFLAGS) invntt_radix2_64_diff.c "$(OUTDIR)/invntt_radix2_64.o" \
		"$(OUTDIR)/invntt_radix2_32.o" "$(OUTDIR)/invntt_radix2_16.o" \
		"$(OUTDIR)/invntt_radix2_8.o" "$(OUTDIR)/invntt_radix2_4.o" \
		$(LDFLAGS) -o "$(OUTDIR)/invntt_radix2_64_diff"
	"$(OUTDIR)/invntt_radix2_64_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_64_SLICE) -o "$(OUTDIR)/invntt_radix2_64.s" "$(INVNTT_RADIX2_64_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_32_SLICE) -o "$(OUTDIR)/invntt_radix2_32.s" "$(INVNTT_RADIX2_32_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_16_SLICE) -o "$(OUTDIR)/invntt_radix2_16.s" "$(INVNTT_RADIX2_16_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_8_SLICE) -o "$(OUTDIR)/invntt_radix2_8.s" "$(INVNTT_RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_RADIX2_4_SLICE) -o "$(OUTDIR)/invntt_radix2_4.s" "$(INVNTT_RADIX2_4_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_64.s" -o "$(OUTDIR)/invntt_radix2_64.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_32.s" -o "$(OUTDIR)/invntt_radix2_32.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_16.s" -o "$(OUTDIR)/invntt_radix2_16.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_8.s" -o "$(OUTDIR)/invntt_radix2_8.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt_radix2_4.s" -o "$(OUTDIR)/invntt_radix2_4.o"
	$(CC) $(CFLAGS) $(SANFLAGS) invntt_radix2_64_diff.c "$(OUTDIR)/invntt_radix2_64.o" \
		"$(OUTDIR)/invntt_radix2_32.o" "$(OUTDIR)/invntt_radix2_16.o" \
		"$(OUTDIR)/invntt_radix2_8.o" "$(OUTDIR)/invntt_radix2_4.o" \
		$(LDFLAGS) -o "$(OUTDIR)/invntt_radix2_64_diff_ubsan"
	"$(OUTDIR)/invntt_radix2_64_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
