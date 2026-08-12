# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
RADIX3_SOURCE := $(JASMIN_DIR)/ntt_radix3.jazz
STAGE1_SOURCE := $(JASMIN_DIR)/ntt_stage1.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_ntt_radix3.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
RADIX3_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3
STAGE1_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-ntt-radix3-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(RADIX3_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(RADIX3_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX3_SLICE) -o "$(OUTDIR)/ntt_radix3.s" "$(RADIX3_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(STAGE1_SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(STAGE1_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix3.s" -o "$(OUTDIR)/ntt_radix3.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) ntt_radix3_diff.c "$(OUTDIR)/ntt_radix3.o" \
		"$(OUTDIR)/ntt_stage1.o" $(LDFLAGS) -o "$(OUTDIR)/ntt_radix3_diff"
	"$(OUTDIR)/ntt_radix3_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX3_SLICE) -o "$(OUTDIR)/ntt_radix3.s" "$(RADIX3_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(STAGE1_SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(STAGE1_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix3.s" -o "$(OUTDIR)/ntt_radix3.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) $(SANFLAGS) ntt_radix3_diff.c "$(OUTDIR)/ntt_radix3.o" \
		"$(OUTDIR)/ntt_stage1.o" $(LDFLAGS) -o "$(OUTDIR)/ntt_radix3_diff_ubsan"
	"$(OUTDIR)/ntt_radix3_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
