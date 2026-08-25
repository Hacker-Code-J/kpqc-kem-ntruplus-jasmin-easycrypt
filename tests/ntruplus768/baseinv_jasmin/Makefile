# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
JASMINC ?= /usr/local/bin/jasminc
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
LDFLAGS ?= -Wl,--gc-sections
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_baseinv
JASMIN_SOURCE := ../../../ntruplus/jasmin/768/ref/baseinv.jazz
PARAMS_SOURCE := ../../../NTRU+/NTRU+768/params.h
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_baseinv_jasmin.py
DRIVER := baseinv_diff.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-baseinv-jasmin-test.XXXXXX))

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
	  -o "$(OUTDIR)/baseinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/baseinv.s" -o "$(OUTDIR)/baseinv.o"
	$(CC) $(CFLAGS) $(DRIVER) "$(C_SOURCE)" "$(OUTDIR)/baseinv.o" \
	  $(LDFLAGS) -o "$(OUTDIR)/baseinv_diff"
	"$(OUTDIR)/baseinv_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) \
	  -o "$(OUTDIR)/baseinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/baseinv.s" \
	  -o "$(OUTDIR)/baseinv-ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) $(DRIVER) "$(C_SOURCE)" \
	  "$(OUTDIR)/baseinv-ubsan.o" $(LDFLAGS) \
	  -o "$(OUTDIR)/baseinv_diff_ubsan"
	"$(OUTDIR)/baseinv_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
