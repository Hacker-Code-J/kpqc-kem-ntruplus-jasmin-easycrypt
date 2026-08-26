# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
JASMINC ?= /usr/local/bin/jasminc
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
LDFLAGS ?= -Wl,--gc-sections
JFLAGS ?= -auto-spill-all -arch x86-64 -call-conv linux -system linux
SLICE_BASEINV := jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv
SLICE_BASEMUL := jade_ntruplus_ntruplus768_amd64_ref_poly_basemul
JASMIN_BASEINV := ../../../ntruplus/jasmin/768/ref/poly_baseinv.jazz
JASMIN_BASEMUL := ../../../ntruplus/jasmin/768/ref/poly_basemul.jazz
PARAMS_SOURCE := ../../../NTRU+/NTRU+768/params.h
NTT_HEADER := ../../../NTRU+/NTRU+768/ntt.h
POLY_HEADER := ../../../NTRU+/NTRU+768/poly.h
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_keygen_h.py
DRIVER := keygen_h_driver.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-keygen-h-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --ntt-header "$(NTT_HEADER)" \
	  --poly-header "$(POLY_HEADER)" \
	  --ntt-source "$(NTT_SOURCE)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --baseinv-jasmin "$(JASMIN_BASEINV)" \
	  --basemul-jasmin "$(JASMIN_BASEMUL)" \
	  --makefile "Makefile"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --ntt-header "$(NTT_HEADER)" \
	  --poly-header "$(POLY_HEADER)" \
	  --ntt-source "$(NTT_SOURCE)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --baseinv-jasmin "$(JASMIN_BASEINV)" \
	  --basemul-jasmin "$(JASMIN_BASEMUL)" \
	  --makefile "Makefile"

run:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE_BASEINV) \
	  -o "$(OUTDIR)/poly_baseinv.s" "$(JASMIN_BASEINV)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE_BASEMUL) \
	  -o "$(OUTDIR)/poly_basemul.s" "$(JASMIN_BASEMUL)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/poly_baseinv.s" -o "$(OUTDIR)/poly_baseinv.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/poly_basemul.s" -o "$(OUTDIR)/poly_basemul.o"
	$(CC) $(CFLAGS) "$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)" \
	  "$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o" $(LDFLAGS) \
	  -o "$(OUTDIR)/keygen_h_driver"
	"$(OUTDIR)/keygen_h_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE_BASEINV) \
	  -o "$(OUTDIR)/poly_baseinv.s" "$(JASMIN_BASEINV)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE_BASEMUL) \
	  -o "$(OUTDIR)/poly_basemul.s" "$(JASMIN_BASEMUL)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/poly_baseinv.s" \
	  -o "$(OUTDIR)/poly_baseinv_ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/poly_basemul.s" \
	  -o "$(OUTDIR)/poly_basemul_ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) "$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)" \
	  "$(OUTDIR)/poly_baseinv_ubsan.o" "$(OUTDIR)/poly_basemul_ubsan.o" $(LDFLAGS) \
	  -o "$(OUTDIR)/keygen_h_driver_ubsan"
	"$(OUTDIR)/keygen_h_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
