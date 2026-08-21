# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
POLY_SOURCE := $(NTRU_ROOT)/poly.c
POLY_HEADER := $(NTRU_ROOT)/poly.h
NTT_SOURCE := $(NTRU_ROOT)/ntt.c
KEM_SOURCE := $(NTRU_ROOT)/kem.c
POLY_TOBYTES_SOURCE := $(JASMIN_DIR)/poly_tobytes.jazz
NTT_JASMIN_SOURCE := $(JASMIN_DIR)/ntt.jazz
CHECKER := check_decap_r1_tobytes.py
VECTOR_CHECKER := check_decap_r1_tobytes_vectors.py
DRIVER := decap_r1_tobytes_driver.c
NTT_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt
POLY_TOBYTES_SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -ffunction-sections -fdata-sections
LDFLAGS := -Wl,--gc-sections
SANFLAGS := -O1 -g -fsanitize=undefined -fno-sanitize-recover=all

.PHONY: all check selfcheck differential ubsan clean

all: check selfcheck differential ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --jasmin-source "$(POLY_TOBYTES_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --jasmin-source "$(POLY_TOBYTES_SOURCE)"

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/ntt.s: $(NTT_JASMIN_SOURCE) | $(OUTDIR)
	$(JASMINC) $(JFLAGS) -slice $(NTT_SLICE) -o "$@" "$(NTT_JASMIN_SOURCE)"

$(OUTDIR)/poly_tobytes.s: $(POLY_TOBYTES_SOURCE) | $(OUTDIR)
	$(JASMINC) $(JFLAGS) -slice $(POLY_TOBYTES_SLICE) -o "$@" "$(POLY_TOBYTES_SOURCE)"

$(OUTDIR)/ntt.o: $(OUTDIR)/ntt.s
	$(CC) $(CFLAGS) -c "$<" -o "$@"

$(OUTDIR)/poly_tobytes.o: $(OUTDIR)/poly_tobytes.s
	$(CC) $(CFLAGS) -c "$<" -o "$@"

$(OUTDIR)/ntt_ubsan.o: $(OUTDIR)/ntt.s
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$<" -o "$@"

$(OUTDIR)/poly_tobytes_ubsan.o: $(OUTDIR)/poly_tobytes.s
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$<" -o "$@"

$(OUTDIR)/decap_r1_tobytes_driver: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) $(NTT_SOURCE) $(OUTDIR)/ntt.o $(OUTDIR)/poly_tobytes.o | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" "$(OUTDIR)/ntt.o" "$(OUTDIR)/poly_tobytes.o" $(LDFLAGS) -o "$@"

$(OUTDIR)/decap_r1_tobytes_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) $(NTT_SOURCE) $(OUTDIR)/ntt_ubsan.o $(OUTDIR)/poly_tobytes_ubsan.o | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" "$(OUTDIR)/ntt_ubsan.o" "$(OUTDIR)/poly_tobytes_ubsan.o" $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/decap_r1_tobytes_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/decap_r1_tobytes_driver"

ubsan: $(OUTDIR)/decap_r1_tobytes_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/decap_r1_tobytes_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
