# -*- Makefile -*-

CC ?= cc
JASMINC ?= jasminc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
POLY_SOURCE := $(NTRU_ROOT)/poly.c
POLY_HEADER := $(NTRU_ROOT)/poly.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
NTT_SOURCE := $(NTRU_ROOT)/ntt.c
NTT_HEADER := $(NTRU_ROOT)/ntt.h
SYMMETRIC_HEADER := $(NTRU_ROOT)/symmetric.h
CHECKER := check_poly_sotp_roundtrip.py
VECTOR_CHECKER := check_poly_sotp_roundtrip_vectors.py
DRIVER := poly_sotp_roundtrip_driver.c
JASMIN_SOURCE := ../../../ntruplus/jasmin/768/ref/poly_sotp_decode.jazz
JASMIN_SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
SANFLAGS := -O1 -g -fsanitize=undefined -fno-sanitize-recover=all

.PHONY: all check selfcheck differential ubsan jasmin-differential clean

all: check selfcheck differential ubsan jasmin-differential

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --kem-source "$(KEM_SOURCE)"

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/poly_sotp_roundtrip_driver: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) $(NTT_SOURCE) $(NTT_HEADER) $(SYMMETRIC_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(POLY_SOURCE) $(NTT_SOURCE) -o "$@"

$(OUTDIR)/poly_sotp_roundtrip_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) $(NTT_SOURCE) $(NTT_HEADER) $(SYMMETRIC_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(POLY_SOURCE) $(NTT_SOURCE) -o "$@"

$(OUTDIR)/poly_sotp_decode_jasmin.s: $(JASMIN_SOURCE) | $(OUTDIR)
	$(JASMINC) -arch x86-64 -call-conv linux -system linux \
	  -slice $(JASMIN_SLICE) -o "$@" "$(JASMIN_SOURCE)"

$(OUTDIR)/poly_sotp_decode_jasmin.o: $(OUTDIR)/poly_sotp_decode_jasmin.s
	$(CC) $(CFLAGS) -c "$<" -o "$@"

$(OUTDIR)/poly_sotp_roundtrip_jasmin_driver: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) $(NTT_SOURCE) $(NTT_HEADER) $(SYMMETRIC_HEADER) $(OUTDIR)/poly_sotp_decode_jasmin.o | $(OUTDIR)
	$(CC) $(CFLAGS) -DNTRUPLUS_SOTP_JASMIN -I"$(NTRU_ROOT)" \
	  $(DRIVER) $(POLY_SOURCE) $(NTT_SOURCE) $(OUTDIR)/poly_sotp_decode_jasmin.o -o "$@"

differential: $(OUTDIR)/poly_sotp_roundtrip_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/poly_sotp_roundtrip_driver"

ubsan: $(OUTDIR)/poly_sotp_roundtrip_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/poly_sotp_roundtrip_driver_ubsan"

jasmin-differential: $(OUTDIR)/poly_sotp_roundtrip_driver $(OUTDIR)/poly_sotp_roundtrip_jasmin_driver
	$(PYTHON) $(VECTOR_CHECKER) \
	  --binary "$(OUTDIR)/poly_sotp_roundtrip_driver" \
	  --jasmin-binary "$(OUTDIR)/poly_sotp_roundtrip_jasmin_driver"

clean:
	rm -rf "$(OUTDIR)"
