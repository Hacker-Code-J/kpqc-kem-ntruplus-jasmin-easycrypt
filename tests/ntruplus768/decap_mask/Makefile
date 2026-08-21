# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
CHECKER := check_decap_mask.py
VECTOR_CHECKER := check_mask_vectors.py
DRIVER := mask_driver.c
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

$(OUTDIR)/mask_driver: $(DRIVER) $(PARAMS_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

$(OUTDIR)/mask_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/mask_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/mask_driver"

ubsan: $(OUTDIR)/mask_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/mask_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
