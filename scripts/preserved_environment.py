"""Authenticate immutable environment metadata through its English representation."""

import hashlib
import json
from pathlib import PurePosixPath


FORMAT = "evidence-relative-paths-v1"


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate key in environment manifest")
        result[key] = value
    return result


def _document(data):
    document = json.loads(data, object_pairs_hook=_unique_object)
    if not isinstance(document, dict):
        raise ValueError("environment manifest must be an object")
    return document


def project_manifest(original_bytes):
    """Replace informational absolute evidence keys; preserve every payload record."""
    original = _document(original_bytes)
    if "metadata_representation" in original:
        raise ValueError("environment manifest was already projected")
    separate = original.get("separate_evidence_inputs")
    if not isinstance(separate, dict) or not separate:
        raise ValueError("historical separate-evidence inventory is missing")
    projected = {}
    marker = "/handoff/verification/"
    for name, record in separate.items():
        path = PurePosixPath(name)
        if (not path.is_absolute() or str(path) != name or ".." in path.parts
                or name.count(marker) != 1 or not isinstance(record, dict)
                or "historical_absolute_path_sha256" in record):
            raise ValueError("invalid historical evidence path record")
        prefix, suffix = name.split(marker)
        if not prefix or not suffix:
            raise ValueError("incomplete historical evidence path")
        relative = "handoff/verification/" + suffix
        if relative in projected:
            raise ValueError("historical evidence paths collide after projection")
        projected[relative] = {
            **record,
            "historical_absolute_path_sha256": hashlib.sha256(
                name.encode("utf-8")).hexdigest(),
        }
    result = dict(original)
    result["separate_evidence_inputs"] = projected
    result["metadata_representation"] = {
        "format": FORMAT,
        "original_manifest_sha256": hashlib.sha256(original_bytes).hexdigest(),
        "projected_field": "separate_evidence_inputs",
        "record_count": len(projected),
        "scope": (
            "English evidence-relative identifiers with hashes of historical "
            "absolute identifiers. Original archive metadata bytes remain unchanged."
        ),
    }
    return result


def authenticate_manifest(original_bytes, public_bytes):
    """Check original bytes first, then the entire deterministic representation."""
    public = _document(public_bytes)
    representation = public.get("metadata_representation")
    if representation is None:
        # Compatibility with an unprojected inventory retains its byte-exact gate.
        if original_bytes != public_bytes:
            raise ValueError("package manifest differs from repository inventory")
        return public
    if (not isinstance(representation, dict)
            or representation.get("format") != FORMAT):
        raise ValueError("unsupported environment metadata representation")
    if (hashlib.sha256(original_bytes).hexdigest()
            != representation.get("original_manifest_sha256")):
        raise ValueError("package manifest differs from pinned original manifest")
    projected = json.dumps(project_manifest(original_bytes), sort_keys=True,
                           ensure_ascii=False, allow_nan=False)
    expected = json.dumps(public, sort_keys=True, ensure_ascii=False, allow_nan=False)
    if projected != expected:
        raise ValueError("environment metadata projection differs from repository")
    return public
