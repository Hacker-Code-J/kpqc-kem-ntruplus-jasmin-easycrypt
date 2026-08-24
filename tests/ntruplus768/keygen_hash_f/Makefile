# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
SYMMETRIC_SOURCE := $(NTRU_ROOT)/symmetric.c
SYMMETRIC_HEADER := $(NTRU_ROOT)/symmetric.h
FIPS202_SOURCE := $(NTRU_ROOT)/fips202/fips202.c
FIPS202_HEADER := $(NTRU_ROOT)/fips202/fips202.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
CHECKER := check_keygen_hash_f.py
HASH_VECTOR_CHECKER := check_hash_f_vectors.py
LAYOUT_VECTOR_CHECKER := check_keygen_hash_f_layout_vectors.py
HASH_DRIVER := hash_f_driver.c
LAYOUT_DRIVER := keygen_hash_f_layout_driver.c
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -ffunction-sections -fdata-sections
LDFLAGS := -Wl,--gc-sections
SANFLAGS := -O1 -g -fsanitize=undefined -fno-sanitize-recover=all

.PHONY: all check selfcheck differential ubsan clean

all: check selfcheck differential ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --symmetric-source "$(SYMMETRIC_SOURCE)" \
	  --symmetric-header "$(SYMMETRIC_HEADER)" \
	  --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --symmetric-source "$(SYMMETRIC_SOURCE)" \
	  --symmetric-header "$(SYMMETRIC_HEADER)" \
	  --kem-source "$(KEM_SOURCE)"

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/hash_f_driver: $(HASH_DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(HASH_DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) $(LDFLAGS) -o "$@"

$(OUTDIR)/hash_f_driver_ubsan: $(HASH_DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(HASH_DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) $(LDFLAGS) -o "$@"

$(OUTDIR)/keygen_hash_f_layout_driver: $(LAYOUT_DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(LAYOUT_DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) $(LDFLAGS) -o "$@"

$(OUTDIR)/keygen_hash_f_layout_driver_ubsan: $(LAYOUT_DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(LAYOUT_DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/hash_f_driver $(OUTDIR)/keygen_hash_f_layout_driver
	$(PYTHON) $(HASH_VECTOR_CHECKER) --binary "$(OUTDIR)/hash_f_driver"
	$(PYTHON) $(LAYOUT_VECTOR_CHECKER) --binary "$(OUTDIR)/keygen_hash_f_layout_driver"

ubsan: $(OUTDIR)/hash_f_driver_ubsan $(OUTDIR)/keygen_hash_f_layout_driver_ubsan
	$(PYTHON) $(HASH_VECTOR_CHECKER) --binary "$(OUTDIR)/hash_f_driver_ubsan"
	$(PYTHON) $(LAYOUT_VECTOR_CHECKER) --binary "$(OUTDIR)/keygen_hash_f_layout_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
