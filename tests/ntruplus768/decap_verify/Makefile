# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
CHECKER := check_decap_verify.py
VECTOR_CHECKER := check_verify_vectors.py
DRIVER := verify_driver.c
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -ffunction-sections -fdata-sections
LDFLAGS := -Wl,--gc-sections
SANFLAGS := -O1 -g -fsanitize=undefined -fno-sanitize-recover=all

.PHONY: all check selfcheck differential ubsan clean

all: check selfcheck differential ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)"

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/verify_driver: $(DRIVER) $(PARAMS_SOURCE) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

$(OUTDIR)/verify_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/verify_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/verify_driver"

ubsan: $(OUTDIR)/verify_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/verify_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
