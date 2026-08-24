# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
OUTDIR ?= build

NTRU_ROOT := ../../../NTRU+/NTRU+768
PARAMS_SOURCE := $(NTRU_ROOT)/params.h
KEM_SOURCE := $(NTRU_ROOT)/kem.c
VECTOR_CHECKER := check_terminal_vectors.py
DRIVER := terminal_driver.c
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -ffunction-sections -fdata-sections
LDFLAGS := -Wl,--gc-sections
SANFLAGS := -O1 -g -fsanitize=undefined -fno-sanitize-recover=all

.PHONY: all check selfcheck differential ubsan clean

all: check selfcheck differential ubsan

check:
	$(MAKE) -C ../decap_fail check
	$(MAKE) -C ../decap_mask check

selfcheck:
	$(MAKE) -C ../decap_fail selfcheck
	$(MAKE) -C ../decap_mask selfcheck

$(OUTDIR):
	mkdir -p "$@"

$(OUTDIR)/terminal_driver: $(DRIVER) $(PARAMS_SOURCE) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

$(OUTDIR)/terminal_driver_ubsan: $(DRIVER) $(PARAMS_SOURCE) $(KEM_SOURCE) | $(OUTDIR)
	$(CC) $(CFLAGS) $(SANFLAGS) -I"$(NTRU_ROOT)" $(DRIVER) $(LDFLAGS) -o "$@"

differential: $(OUTDIR)/terminal_driver
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/terminal_driver"

ubsan: $(OUTDIR)/terminal_driver_ubsan
	$(PYTHON) $(VECTOR_CHECKER) --binary "$(OUTDIR)/terminal_driver_ubsan"

clean:
	rm -rf "$(OUTDIR)"
