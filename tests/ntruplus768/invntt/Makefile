# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMIN_SOURCE := $(JASMIN_DIR)/invntt.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_invntt.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
INVNTT_SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-invntt-test.XXXXXX))

.PHONY: check selfcheck ccheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

ccheck:
	$(CC) $(CFLAGS) -c invntt_diff.c -o /tmp/invntt_diff.o
	$(CC) $(CFLAGS) -c "$(C_SOURCE)" -o /tmp/invntt_c_ref.o

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_SLICE) -o "$(OUTDIR)/invntt.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/invntt.s" -o "$(OUTDIR)/invntt.o"
	$(CC) $(CFLAGS) invntt_diff.c "$(C_SOURCE)" "$(OUTDIR)/invntt.o" \
		$(LDFLAGS) -o "$(OUTDIR)/invntt_diff"
	"$(OUTDIR)/invntt_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(INVNTT_SLICE) -o "$(OUTDIR)/invntt.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/invntt.s" -o "$(OUTDIR)/invntt.o"
	$(CC) $(CFLAGS) $(SANFLAGS) invntt_diff.c "$(C_SOURCE)" "$(OUTDIR)/invntt.o" \
		$(LDFLAGS) -o "$(OUTDIR)/invntt_diff_ubsan"
	"$(OUTDIR)/invntt_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
