# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
JASMINC ?= /usr/local/bin/jasminc
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_fqinv
JASMIN_SOURCE := ../../../ntruplus/jasmin/768/ref/fqinv.jazz
PARAMS_SOURCE := ../../../NTRU+/NTRU+768/params.h
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
C_WRAPPER := ../baseinv/fqinv_wrapper.c
CHECKER := check_fqinv_jasmin.py
DRIVER := fqinv_diff.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-fqinv-jasmin-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --c-source "$(C_SOURCE)" \
	  --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --c-source "$(C_SOURCE)" \
	  --jasmin-source "$(JASMIN_SOURCE)"

run:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) \
	  -o "$(OUTDIR)/fqinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/fqinv.s" -o "$(OUTDIR)/fqinv.o"
	$(CC) $(CFLAGS) -c "$(C_WRAPPER)" -o "$(OUTDIR)/fqinv_wrapper.o"
	$(CC) $(CFLAGS) $(DRIVER) "$(OUTDIR)/fqinv_wrapper.o" \
	  "$(OUTDIR)/fqinv.o" -o "$(OUTDIR)/fqinv_diff"
	"$(OUTDIR)/fqinv_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) \
	  -o "$(OUTDIR)/fqinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/fqinv.s" -o "$(OUTDIR)/fqinv-ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(C_WRAPPER)" -o "$(OUTDIR)/fqinv_wrapper-ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) $(DRIVER) "$(OUTDIR)/fqinv_wrapper-ubsan.o" \
	  "$(OUTDIR)/fqinv-ubsan.o" -o "$(OUTDIR)/fqinv_diff_ubsan"
	"$(OUTDIR)/fqinv_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
