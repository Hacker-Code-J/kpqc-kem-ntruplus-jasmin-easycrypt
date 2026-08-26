# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
JASMINC ?= /usr/local/bin/jasminc
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
LDFLAGS ?= -Wl,--gc-sections
JFLAGS ?= -auto-spill-all -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv
JASMIN_SOURCE := ../../../ntruplus/jasmin/768/ref/poly_baseinv.jazz
PARAMS_HEADER := ../../../NTRU+/NTRU+768/params.h
POLY_HEADER := ../../../NTRU+/NTRU+768/poly.h
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_keygen_inverse.py
DRIVER := keygen_inverse_driver.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-keygen-inverse-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-header "$(PARAMS_HEADER)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --jasmin-source "$(JASMIN_SOURCE)" \
	  --makefile "Makefile"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-header "$(PARAMS_HEADER)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --jasmin-source "$(JASMIN_SOURCE)" \
	  --makefile "Makefile"

run:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) \
	  -o "$(OUTDIR)/poly_baseinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/poly_baseinv.s" -o "$(OUTDIR)/poly_baseinv.o"
	$(CC) $(CFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" \
	  "$(OUTDIR)/poly_baseinv.o" $(LDFLAGS) -o "$(OUTDIR)/keygen_inverse_driver"
	"$(OUTDIR)/keygen_inverse_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) \
	  -o "$(OUTDIR)/poly_baseinv.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/poly_baseinv.s" \
	  -o "$(OUTDIR)/poly_baseinv-ubsan.o"
	$(CC) $(CFLAGS) $(SANFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" \
	  "$(OUTDIR)/poly_baseinv-ubsan.o" $(LDFLAGS) \
	  -o "$(OUTDIR)/keygen_inverse_driver_ubsan"
	"$(OUTDIR)/keygen_inverse_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
