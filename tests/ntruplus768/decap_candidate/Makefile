PYTHON ?= python3
.PHONY: all check gates
all: check
check:
	$(PYTHON) verify_decap_candidate.py
gates:
	$(PYTHON) test_gates.py
