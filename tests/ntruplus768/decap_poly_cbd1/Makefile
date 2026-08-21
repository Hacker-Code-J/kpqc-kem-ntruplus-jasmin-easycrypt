# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
POLY_SOURCE := $(NTRU_ROOT)/poly.c
POLY_HEADER := $(NTRU_ROOT)/poly.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
CHECKER := check_decap_poly_cbd1.py
VECTOR_CHECKER := check_poly_cbd1_vectors.py
DRIVER := poly_cbd1_driver.c
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
	  --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)"

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/poly_cbd1_driver: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(POLY_SOURCE) $(LDFLAGS) -o "$@"

$(OUTDIR)/poly_cbd1_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(POLY_SOURCE) $(POLY_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(POLY_SOURCE) $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/poly_cbd1_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/poly_cbd1_driver"

ubsan: $(OUTDIR)/poly_cbd1_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/poly_cbd1_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
