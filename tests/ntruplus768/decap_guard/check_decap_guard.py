#!/usr/bin/env python3
"""Strict source/reference/extraction binding for the standalone entry guard."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import prepare_reference as reference

TEST, ROOT = reference.TEST, reference.ROOT
sys.path.insert(0, str(TEST.parent / "poly_frombytes_checked"))
import check_poly_frombytes_checked as checked

require, sha = reference.require, reference.sha
check_proof_text = checked.check_proof_text
SOURCE = ROOT / "ntruplus/jasmin/768/ref/decap_guard.jazz"
SOURCE_SHA256 = "7e06fdb274a0b1f1cacecd4e4ffc330d959cd7cc11001a52ec74efd1bf1f64c4"
SLICE = "jade_ntruplus_ntruplus768_amd64_ref_decap_guard"
EXTRACTION_FILES = {"Array1152.ec", "Array2304.ec", "Array32.ec", "Array768.ec", "WArray1152.ec",
                    "WArray1536.ec", "WArray2304.ec", "WArray32.ec", "NTRUPlus768DecapGuard.ec"}


def check_source(data=None):
    data = SOURCE.read_bytes() if data is None else data
    require(sha(data) == SOURCE_SHA256, "guard Jasmin source pin drift")
    code = re.sub(r"//[^\n]*|/\*.*?\*/", "", data.decode(), flags=re.S)
    require(code.count('() = #declassify(status);') == 2 and code.count('#declassify') == 2,
            "only two secret-key canonicality status bits may be declassified")
    require('#[ct = "secret × secret × secret × secret × public × secret → secret × secret × secret × secret × public"]' in code,
            "guard public ciphertext / secret key CT policy drift")
    require(code.count("status = #protect_32(status, msf);") == 3, "guard SCT branch protections drift")
    require(code.count("CheckedDecoder::jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(") == 3,
            "guard must use checked decoder exactly three times")
    require('skpoly[NTRUPLUS_POLYBYTES:NTRUPLUS_POLYBYTES]' in code,
            "secret key second-block offset drift")
    checked.check_jasmin()


def check_extraction(stored, fresh):
    def contents(directory):
        paths = list(directory.rglob("*"))
        require(all(not path.is_symlink() for path in paths), "symlink in extraction")
        require(all(path.suffix == ".ec" for path in paths if path.is_file()), "unexpected extraction file")
        return {str(path.relative_to(directory)): path.read_bytes() for path in paths if path.is_file()}
    stored_bytes, fresh_bytes = contents(stored), contents(fresh)
    require(set(stored_bytes) == set(fresh_bytes) == EXTRACTION_FILES, "whole extraction inventory drift")
    require(stored_bytes == fresh_bytes, "raw extraction byte drift")
    return {name: sha(data) for name, data in stored_bytes.items()}


def check():
    reference.check_reference()
    check_source()
    original = (TEST / "reference/kem.c").read_bytes()
    reference.check_mixed(original, reference.splice(original))


if __name__ == "__main__":
    check()
    print("PASS: guard, reused checked decoder, exact official reference and one-block splice pins")
