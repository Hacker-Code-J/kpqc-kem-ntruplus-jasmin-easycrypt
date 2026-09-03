# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
PARAMS_SOURCE := ../../../NTRU+/NTRU+768/params.h
POLY_HEADER := ../../../NTRU+/NTRU+768/poly.h
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_keygen_secret_f.py
DRIVER := keygen_secret_f_driver.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-keygen-secret-f-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --makefile "Makefile"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
	  --params-source "$(PARAMS_SOURCE)" \
	  --poly-header "$(POLY_HEADER)" \
	  --poly-source "$(POLY_SOURCE)" \
	  --kem-source "$(KEM_SOURCE)" \
	  --makefile "Makefile"

run: check
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) \
	  -o "$(OUTDIR)/keygen_secret_f_driver"
	"$(OUTDIR)/keygen_secret_f_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) \
	  -o "$(OUTDIR)/keygen_secret_f_driver_ubsan"
	"$(OUTDIR)/keygen_secret_f_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
