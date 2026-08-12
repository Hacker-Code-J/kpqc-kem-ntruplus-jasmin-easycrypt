# -*- Makefile -*-

PYTHON ?= python3
CHECKER := check_ntt_schedule.py
SOURCE ?= ../../../NTRU+/NTRU+768/ntt.c

.PHONY: check selfcheck clean

check:
	$(PYTHON) $(CHECKER) $(SOURCE)

selfcheck:
	$(PYTHON) $(CHECKER) --self-check $(SOURCE)

clean:
	rm -rf __pycache__
