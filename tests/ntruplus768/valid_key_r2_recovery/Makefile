# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
SOURCE_DIR := ../../../NTRU+/NTRU+768
SOURCES := $(SOURCE_DIR)/poly.c $(SOURCE_DIR)/ntt.c $(SOURCE_DIR)/symmetric.c $(SOURCE_DIR)/fips202/fips202.c
DRIVER := valid_key_r2_recovery_driver.c
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-valid-key-r2-recovery-test.XXXXXX))

.PHONY: all check selfcheck run ubsan analyze

all: check selfcheck run ubsan analyze

check:
	$(PYTHON) check_valid_key_r2_recovery.py

selfcheck:
	$(PYTHON) check_valid_key_r2_recovery.py --self-test

run:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) "$(DRIVER)" $(SOURCES) $(LDFLAGS) \
	  -o "$(OUTDIR)/valid_key_r2_recovery_driver"
	"$(OUTDIR)/valid_key_r2_recovery_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) "$(DRIVER)" $(SOURCES) $(LDFLAGS) \
	  -o "$(OUTDIR)/valid_key_r2_recovery_driver_ubsan"
	"$(OUTDIR)/valid_key_r2_recovery_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

analyze:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) -fanalyzer -c "$(DRIVER)" \
	  -o "$(OUTDIR)/valid_key_r2_recovery_driver_analyzer.o"
