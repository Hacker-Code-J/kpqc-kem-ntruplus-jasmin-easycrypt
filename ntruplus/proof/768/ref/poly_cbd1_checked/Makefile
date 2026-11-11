PYTHON ?= python3

.PHONY: all check
all: check

# The complete-decapsulation replay checks this sampler and fresh extraction.
check:
	$(PYTHON) ../../../../../tests/ntruplus768/decap_complete/verify_decap_complete.py
