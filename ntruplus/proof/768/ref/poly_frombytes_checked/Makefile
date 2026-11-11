PYTHON ?= python3

.PHONY: all check
all: check

# One strict entry point also checks extraction, checker policy and the C ABI.
check:
	$(PYTHON) ../../../../../tests/ntruplus768/poly_frombytes_checked/verify_checked.py
