# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMIN_SOURCE := $(JASMIN_DIR)/ntt_stage1.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_ntt_stage1.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-ntt-stage1-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) ntt_stage1_diff.c "$(OUTDIR)/ntt_stage1.o" $(LDFLAGS) -o "$(OUTDIR)/ntt_stage1_diff"
	"$(OUTDIR)/ntt_stage1_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) $(SANFLAGS) ntt_stage1_diff.c "$(OUTDIR)/ntt_stage1.o" $(LDFLAGS) -o "$(OUTDIR)/ntt_stage1_diff_ubsan"
	"$(OUTDIR)/ntt_stage1_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
