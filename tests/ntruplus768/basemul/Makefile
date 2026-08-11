# -*- Makefile -*-

CC ?= /usr/bin/gcc
CFLAGS ?= -Wall -Wextra -Werror -O2 -g
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_basemul
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-basemul-test.XXXXXX))

.PHONY: run ubsan clean

run:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/basemul.s" "$(JASMIN_DIR)/basemul.jazz"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/basemul.s" -o "$(OUTDIR)/basemul.o"
	$(CC) $(CFLAGS) basemul_diff.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/basemul.o" -o "$(OUTDIR)/basemul_diff"
	"$(OUTDIR)/basemul_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/basemul.s" "$(JASMIN_DIR)/basemul.jazz"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/basemul.s" -o "$(OUTDIR)/basemul.o"
	$(CC) $(CFLAGS) $(SANFLAGS) basemul_diff.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/basemul.o" -o "$(OUTDIR)/basemul_diff_ubsan"
	"$(OUTDIR)/basemul_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
