# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMIN_SOURCE := $(JASMIN_DIR)/ntt.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_ntt.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
NTT_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-ntt-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(NTT_SLICE) -o "$(OUTDIR)/ntt.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt.s" -o "$(OUTDIR)/ntt.o"
	$(CC) $(CFLAGS) ntt_diff.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/ntt.o" \
		$(LDFLAGS) -o "$(OUTDIR)/ntt_diff"
	"$(OUTDIR)/ntt_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(NTT_SLICE) -o "$(OUTDIR)/ntt.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt.s" -o "$(OUTDIR)/ntt.o"
	$(CC) $(CFLAGS) $(SANFLAGS) ntt_diff.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/ntt.o" \
		$(LDFLAGS) -o "$(OUTDIR)/ntt_diff_ubsan"
	"$(OUTDIR)/ntt_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
