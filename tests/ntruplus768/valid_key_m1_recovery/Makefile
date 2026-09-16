# -*- Makefile -*-

CC ?= /usr/bin/gcc
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
DRIVER := valid_key_m1_recovery_driver.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-valid-key-m1-recovery-test.XXXXXX))

.PHONY: all run ubsan

all: run ubsan

run:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) \
	  -o "$(OUTDIR)/valid_key_m1_recovery_driver"
	"$(OUTDIR)/valid_key_m1_recovery_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) "$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) \
	  -o "$(OUTDIR)/valid_key_m1_recovery_driver_ubsan"
	"$(OUTDIR)/valid_key_m1_recovery_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"
