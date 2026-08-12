# -*- Makefile -*-

CC ?= /usr/bin/gcc
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_basemul
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-poly-basemul-test.XXXXXX))

.PHONY: run ubsan clean

run:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/poly_basemul.s" "$(JASMIN_DIR)/poly_basemul.jazz"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/poly_basemul.s" -o "$(OUTDIR)/poly_basemul.o"
	$(CC) $(CFLAGS) poly_basemul_diff.c ../../../NTRU+/NTRU+768/poly.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/poly_basemul.o" $(LDFLAGS) -o "$(OUTDIR)/poly_basemul_diff"
	"$(OUTDIR)/poly_basemul_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/poly_basemul.s" "$(JASMIN_DIR)/poly_basemul.jazz"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/poly_basemul.s" -o "$(OUTDIR)/poly_basemul.o"
	$(CC) $(CFLAGS) $(SANFLAGS) poly_basemul_diff.c ../../../NTRU+/NTRU+768/poly.c ../../../NTRU+/NTRU+768/ntt.c "$(OUTDIR)/poly_basemul.o" $(LDFLAGS) -o "$(OUTDIR)/poly_basemul_diff_ubsan"
	"$(OUTDIR)/poly_basemul_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
