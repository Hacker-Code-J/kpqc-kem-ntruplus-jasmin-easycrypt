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
CHECKER := check_decap_hash_g.py
VECTOR_CHECKER := check_hash_g_vectors.py
DRIVER := hash_g_driver.c
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
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

$(OUTDIR)/hash_g_driver: $(DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) -o "$@"

$(OUTDIR)/hash_g_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(SYMMETRIC_SOURCE) $(SYMMETRIC_HEADER) $(FIPS202_SOURCE) $(FIPS202_HEADER) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(SYMMETRIC_SOURCE) $(FIPS202_SOURCE) -o "$@"

differential: $(OUTDIR)/hash_g_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/hash_g_driver"

ubsan: $(OUTDIR)/hash_g_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/hash_g_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
