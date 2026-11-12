#!/usr/bin/env python3
"""Attribute preserved inputs using local install records and exact Debian payloads."""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import preserved_environment  # noqa: E402
sys.path.pop(0)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def quoted(text):
    return [json.loads(value) for value in re.findall(r'"(?:[^"\\]|\\.)*"', text)]


def unfiltered_items(text):
    """Read item strings but not strings inside opam's conditional braces."""
    depth, values = 0, []
    for token in re.findall(r'"(?:[^"\\]|\\.)*"|[{}]', text):
        if token == "{":
            depth += 1
        elif token == "}":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced opam condition")
        elif depth == 0:
            values.append(json.loads(token))
    if depth:
        raise ValueError("Unbalanced opam condition")
    return values


def field(text, name):
    match = re.search(r"(?m)^" + re.escape(name) + r"\s*:\s*", text)
    if not match:
        return ""
    tail = text[match.end() :]
    end = re.search(r"(?m)^[A-Za-z][\w-]*(?:\s*:|\s*\{)", tail)
    return (tail[: end.start()] if end else tail).strip()


def url_metadata(text):
    match = re.search(r"(?ms)^url\s*\{(.*?)^\}", text)
    if not match:
        return {"src": [], "checksums": [], "raw": ""}
    block = re.sub(r"(?m)^\s+", "", match[1])
    return {
        "src": quoted(field(block, "src")),
        "checksums": quoted(field(block, "checksum")),
        "raw": match[0],
    }


def change_records(text):
    records = {}
    for name, value in re.findall(
        r'"([^"\n]+)"\s*\{\s*"(F:[^"\n]+)"\s*\}', field(text, "added")
    ):
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise ValueError("Unsafe install record: " + name)
        if name in records and records[name] != value:
            raise ValueError("Conflicting install record: " + name)
        records[name] = value
    return records


def is_notice(name):
    return bool(
        re.fullmatch(
            r"(?:LICENSE|LICENCE|COPYING|COPYRIGHT|NOTICE|AUTHORS)"
            r"(?:[._-](?!ml$|c$|h$|py$|rst$)[\w.-]+)?",
            name,
            re.I,
        )
    )


class Evidence:
    def __init__(self, root):
        self.root = root

    def add_bytes(self, data, origin, kind="metadata"):
        digest = sha(data)
        path = Path("notices" if kind == "notice" else "evidence") / (digest + ".txt")
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != data:
            raise ValueError("Conflicting evidence bytes")
        target.write_bytes(data)
        return {
            "original_path": str(origin),
            "sha256": digest,
            "bytes": len(data),
            "archive_path": str(path),
        }

    def add(self, path, kind="metadata"):
        return self.add_bytes(path.read_bytes(), str(path), kind)


def run(command):
    return subprocess.check_output(command, text=True, stderr=subprocess.DEVNULL)


def notice_paths(root):
    if not root.is_dir():
        return
    for directory, children, names in os.walk(root):
        children[:] = [
            x
            for x in children
            if x not in {".git", "_build", "build", "_opam", "node_modules"}
        ]
        for name in names:
            path = Path(directory) / name
            if is_notice(name) and path.is_file():
                yield path


def archive_notices(path):
    """Read actual notice bytes from a digest-checked source archive, never extract."""
    if zipfile.is_zipfile(path):
        with zipfile.ZipFile(path) as archive:
            for name in archive.namelist():
                if is_notice(PurePosixPath(name).name) and not name.endswith("/"):
                    yield name, archive.read(name)
        return
    with tarfile.open(path) as archive:
        for member in archive:
            if member.isfile() and is_notice(PurePosixPath(member.name).name):
                yield member.name, archive.extractfile(member).read()


def extra_sources(raw):
    result = []
    pattern = r'(?ms)^extra-source\s+"([^"\n]+)"\s*\{(.*?)^\}'
    for name, block in re.findall(pattern, raw):
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("Unsafe extra-source target")
        data = url_metadata("url {\n" + block + "\n}\n")
        result.append({"name": name, **data})
    return result


def component_table(components):
    lines = [
        "# Component inventory",
        "",
        "Declarations are recorded from upstream notices/metadata. "
        "They do not establish distribution clearance or a complete link map.",
        "",
        "| Component | Version | Recorded license | Captured files | Role |",
        "| --- | --- | --- | ---: | --- |",
    ]
    for key, item in sorted(components.items()):
        license_text = (
            item.get("license_expression")
            or ", ".join(item.get("license_declared", []))
            or "Not declared"
        )
        if item.get("license_metadata_notice_inconsistency"):
            license_text += "; opam metadata: CeCILL-C"
        cells = [
            key,
            item.get("version") or "Not established",
            license_text,
            str(len(item.get("captured_files", []))),
            ", ".join(item["roles"]),
        ]
        lines.append(
            "| "
            + " | ".join(x.replace("|", "\\|").replace("\n", " ") for x in cells)
            + " |"
        )
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-output", type=Path, required=True)
    parser.add_argument("--calibration-evidence", type=Path, required=True)
    parser.add_argument("--system-source-status", type=Path, required=True)
    args = parser.parse_args()
    manifest_path, capture = args.manifest.resolve(strict=True), args.capture.resolve(
        strict=True
    )
    output = args.output.resolve()
    source_output = args.source_output.resolve()
    if (
        source_output.exists()
        or source_output.is_relative_to(capture)
        or source_output.is_relative_to(output)
        or output.is_relative_to(source_output)
    ):
        raise ValueError("Choose a separate new source-companion directory")
    if output.exists() or output.is_relative_to(capture):
        raise ValueError(
            "Choose a new output directory outside the captured environment"
        )
    public_manifest_bytes = manifest_path.read_bytes()
    manifest_bytes = (capture / "manifest.json").read_bytes()
    manifest = preserved_environment.authenticate_manifest(
        manifest_bytes, public_manifest_bytes)
    for name, record in manifest["files"].items():
        target = capture / record["archive_path"]
        if target.is_symlink() or sha(target.read_bytes()) != record["sha256"]:
            raise ValueError("Captured input drift: " + name)
    output.mkdir(parents=True)
    source_output.mkdir(parents=True)
    evidence = Evidence(output)
    source_blobs = {}

    def source_blob(content, origin, kind):
        digest = sha(content)
        path = Path("blobs") / digest
        target = source_output / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.write_bytes(content)
        source_blobs.setdefault(
            digest,
            {
                "sha256": digest,
                "bytes": len(content),
                "archive_path": str(path),
                "origins": [],
                "kinds": [],
            },
        )
        record = source_blobs[digest]
        if origin not in record["origins"]:
            record["origins"].append(origin)
        if kind not in record["kinds"]:
            record["kinds"].append(kind)
        return {
            "sha256": digest,
            "archive_path": str(path),
            "bytes": len(content),
            "kind": kind,
        }

    components, mapping, switches, owners, module_owners = {}, {}, {}, {}, {}
    opam_root = Path("/home/hacker-code-j/.opam")
    for switch in (
        "cryptotools-2026.09",
        "easycrypt-5.2",
        "ocaml-base-compiler.4.12.0",
    ):
        prefix = opam_root / switch
        state = prefix / ".opam-switch/switch-state"
        installed = quoted(field(state.read_text(), "installed"))
        packages = {}
        for package in installed:
            name, version = package.split(".", 1)
            if name in packages:
                raise ValueError("Ambiguous installed package version")
            packages[name] = (
                version,
                prefix / ".opam-switch/packages" / package / "opam",
            )
        changes = {}
        modules = {}
        for path in sorted((prefix / ".opam-switch/install").glob("*.changes")):
            if path.stem not in packages:
                continue
            records = change_records(path.read_text())
            changes[path.stem] = (path, records)
            for relative in records:
                absolute = str(prefix / relative)
                owners.setdefault(absolute, []).append((switch, path.stem, relative))
                if relative.endswith(".cmx"):
                    modules.setdefault(Path(relative).stem.lower(), []).append(
                        {"package": path.stem, "installed_module": absolute}
                    )
        switches[switch] = {
            "prefix": prefix,
            "packages": packages,
            "changes": changes,
            "state": state,
        }
        module_owners[switch] = modules

    def opam_component(switch, package, role="captured-file-owner"):
        data = switches[switch]
        version, metadata = data["packages"][package]
        key = f"opam:{switch}/{package}@{version}"
        if key in components:
            if role not in components[key]["roles"]:
                components[key]["roles"].append(role)
            return key
        raw = metadata.read_text()
        licenses = quoted(field(raw, "license"))
        source = url_metadata(raw)
        item = {
            "name": package,
            "version": version,
            "ecosystem": "opam",
            "switch": switch,
            "roles": [role],
            "captured_files": [],
            "license_declared": licenses,
            "license_field_raw": field(raw, "license"),
            "license_expression": licenses[0] if len(licenses) == 1 else None,
            "license_interpretation": (
                "Verbatim package metadata, not a legal conclusion."
            ),
            "homepage": quoted(field(raw, "homepage")),
            "development_repository": quoted(field(raw, "dev-repo")),
            "source": source,
            "metadata": [evidence.add(metadata), evidence.add(data["state"])],
            "depends_raw": field(raw, "depends"),
            "notices": [],
            "ownership_confidence": (
                "high for exact installation records; source/binary correspondence "
                "separate"
            ),
            "exact_corresponding_source_status": (
                "NOT_ESTABLISHED_BY_PACKAGE_ATTRIBUTION"
            ),
            "gaps": [],
        }
        components[key] = item
        if package in data["changes"]:
            item["metadata"].append(evidence.add(data["changes"][package][0]))
        install = data["prefix"] / ".opam-switch/install" / (package + ".install")
        if install.exists():
            item["metadata"].append(evidence.add(install))
        roots = []
        for url in source["src"]:
            if url.startswith("file://"):
                roots.append(Path(url[7:]))
        roots += [
            data["prefix"] / ".opam-switch/sources" / (package + "." + version),
            data["prefix"] / ".opam-switch/sources" / package,
            data["prefix"] / ".opam-switch/build" / (package + "." + version),
        ]
        roots = sorted(set(p for p in roots if p.is_dir()))
        item["retained_source_trees"] = []
        for root in roots:
            observation = {
                "path": str(root),
                "status": "OBSERVED_RETAINED_TREE_NOT_BINARY_CORRESPONDENCE",
            }
            if (root / ".git").exists():
                observation["git_commit"] = run(
                    ["git", "-C", str(root), "rev-parse", "HEAD"]
                ).strip()
                observation["git_worktree_clean"] = not bool(
                    run(["git", "-C", str(root), "status", "--porcelain"])
                )
            item["retained_source_trees"].append(observation)
        notices = set()
        for root in [data["prefix"] / "doc" / package, *roots]:
            notices.update(notice_paths(root))
        for path in sorted(notices):
            item["notices"].append(evidence.add(path, "notice"))
        if package == "easycrypt" and "CeCILL-C" in licenses:
            mit_notices = [
                record
                for record in item["notices"]
                if (output / record["archive_path"])
                .read_bytes()
                .startswith(b"MIT License")
            ]
            if mit_notices:
                item["metadata_license_expression"] = item["license_expression"]
                item["source_license_expression"] = "MIT"
                item["license_expression"] = "MIT"
                item["license_expression_basis"] = mit_notices
                item["license_metadata_notice_inconsistency"] = {
                    "opam_declares": "CeCILL-C",
                    "observed_notice_heading": "MIT License",
                    "notice_sha256s": sorted({x["sha256"] for x in mit_notices}),
                    "resolution": (
                        "MIT source notice preserved; stale CeCILL-C metadata "
                        "separately retained. Not dual licensing."
                    ),
                }
                item["gaps"].append(
                    (
                        "Installed license metadata and retained MIT notice "
                        "disagree; no legal interpretation selected."
                    )
                )
        item["cached_source_archives"] = []
        for checksum in source["checksums"]:
            if "=" not in checksum:
                continue
            algorithm, expected = checksum.split("=", 1)
            if algorithm not in {"sha256", "sha512", "md5"}:
                continue
            path = opam_root / "download-cache" / algorithm / expected[:2] / expected
            if path.is_file():
                actual = hashlib.new(algorithm, path.read_bytes()).hexdigest()
                if actual != expected:
                    raise ValueError("Cached source archive mismatch")
                item["cached_source_archives"].append(
                    {
                        "path": str(path),
                        "algorithm": algorithm,
                        "digest": expected,
                        "status": "ARCHIVE_DIGEST_MATCHES_INSTALLED_OPAM_METADATA",
                        "copied_into_notice_companion": False,
                    }
                )
        if item["cached_source_archives"]:
            strength = {"sha512": 3, "sha256": 2, "md5": 1}
            selected = max(
                item["cached_source_archives"], key=lambda x: strength[x["algorithm"]]
            )
            for member, data_bytes in archive_notices(Path(selected["path"])):
                origin = (
                    "opam-source-archive:"
                    + selected["algorithm"]
                    + "="
                    + selected["digest"]
                    + "/"
                    + member
                )
                item["notices"].append(evidence.add_bytes(data_bytes, origin, "notice"))
            if not item["notices"]:
                with tarfile.open(selected["path"]) as archive:
                    for member in archive:
                        if not member.isfile() or PurePosixPath(
                            member.name
                        ).suffix not in {".ml", ".mli"}:
                            continue
                        content = archive.extractfile(member).read()
                        if (
                            b"Copyright" in content[:2048]
                            and b"Permission to use, copy, modify" in content[:2048]
                        ):
                            origin = (
                                "opam-source-archive:"
                                + selected["digest"]
                                + "/"
                                + member.name
                            )
                            record = evidence.add_bytes(content, origin, "notice")
                            record["scope"] = (
                                "Whole upstream source file containing its original "
                                "notice."
                            )
                            item["notices"].append(record)
            item["source_materials"] = [
                source_blob(
                    Path(selected["path"]).read_bytes(),
                    selected["path"],
                    "EXACT_CACHED_UPSTREAM_ARCHIVE",
                )
            ]
            if package == "bitwuzla-cxx":
                vendor = (
                    data["prefix"]
                    / ".opam-switch/sources"
                    / (package + "." + version)
                    / "vendor"
                )
                coverage = {}
                with tarfile.open(selected["path"]) as archive:
                    for member in archive:
                        if not member.isfile() or "/vendor/" not in member.name:
                            continue
                        relative = member.name.split("/vendor/", 1)[1]
                        name = relative.split("/")[0]
                        if name not in {
                            "bitwuzla",
                            "cadical",
                            "kissat",
                            "symfpu",
                            "cryptominisat",
                        }:
                            continue
                        local = vendor / relative
                        if not local.resolve().is_relative_to(vendor):
                            raise ValueError("Vendored source path escapes root")
                        content = archive.extractfile(member).read()
                        if not local.is_file() or sha(local.read_bytes()) != sha(
                            content
                        ):
                            raise ValueError(
                                "Retained vendored source differs from archive: "
                                + relative
                            )
                        coverage.setdefault(name, {})[member.name] = sha(content)
                item["vendored_archive_coverage"] = {}
                for name, hashes in coverage.items():
                    proof = {
                        "status": "EXACT_ARCHIVE_MEMBERS_MATCH_RETAINED_SOURCE",
                        "source_archive": item["source_materials"][0],
                        "member_hashes": hashes,
                        "scope": (
                            "Source-file identity only, not embedded-binary rebuild "
                            "correspondence."
                        ),
                    }
                    item["vendored_archive_coverage"][name] = {
                        "file_count": len(hashes),
                        "status": proof["status"],
                        "audit": evidence.add_bytes(
                            json.dumps(proof, indent=2).encode() + b"\n",
                            "generated archive/source comparison: " + name,
                        ),
                    }
        else:
            item["source_materials"] = []
            clean_git = next(
                (
                    root
                    for root, observation in zip(roots, item["retained_source_trees"])
                    if observation.get("git_worktree_clean")
                ),
                None,
            )
            if clean_git:
                commit = run(["git", "-C", str(clean_git), "rev-parse", "HEAD"]).strip()
                content = subprocess.check_output(
                    [
                        "git",
                        "-C",
                        str(clean_git),
                        "archive",
                        "--format=tar",
                        "--prefix=source/",
                        commit,
                    ]
                )
                material = source_blob(
                    gzip.compress(content, mtime=0),
                    str(clean_git) + "@" + commit,
                    "GIT_COMMIT_SOURCE_SNAPSHOT",
                )
                material["commit"] = commit
                item["source_materials"].append(material)
                item["git_source_submodule_entries"] = [
                    line
                    for line in run(
                        ["git", "-C", str(clean_git), "ls-tree", "-r", commit]
                    ).splitlines()
                    if line.startswith("160000 ")
                ]
            elif package == "jasmin" and version == "2026.09.0":
                archive = Path(
                    (
                        "/home/hacker-code-j/.local/share/cryptotools/2026.09/downloa"
                        "ds/jasmin-compiler-v2026.09.0.tar.bz2"
                    )
                )
                expected = (
                    "11fec571efb9f7b3a47fea324b4e2a68289e0b73b2248d237eccf139b5218190"
                )
                if sha(archive.read_bytes()) != expected:
                    raise ValueError("Local Jasmin source archive changed")
                item["source_materials"].append(
                    source_blob(
                        archive.read_bytes(),
                        str(archive),
                        "EXACT_LOCAL_JASMIN_RELEASE_ARCHIVE",
                    )
                )
                item["source"]["release_archive_sha256"] = expected
                item["source"]["release_archive_url"] = (
                    "https://github.com/jasmin-lang/jasmin/releases/download/v2026.09"
                    ".0/jasmin-compiler-v2026.09.0.tar.bz2"
                )
        item["patches_raw"] = field(raw, "patches")
        item["extra_sources"] = extra_sources(raw)
        for extra in item["extra_sources"]:
            extra["available_material"] = None
            for checksum in extra["checksums"]:
                algorithm, expected = checksum.split("=", 1)
                if algorithm not in {"sha256", "sha512", "md5"}:
                    continue
                path = (
                    opam_root / "download-cache" / algorithm / expected[:2] / expected
                )
                if path.is_file():
                    content = path.read_bytes()
                    if hashlib.new(algorithm, content).hexdigest() != expected:
                        raise ValueError("Extra-source cache digest mismatch")
                    extra["available_material"] = source_blob(
                        content, str(path), "EXACT_OPAM_EXTRA_SOURCE"
                    )
                    break
            if extra["available_material"] is None:
                item["gaps"].append(
                    "Unavailable registered extra-source: " + extra["name"]
                )
        extra_names = {x["name"] for x in item["extra_sources"]}
        item["unresolved_patch_names"] = [
            name
            for name in unfiltered_items(item["patches_raw"])
            if name not in extra_names
        ]
        if item["unresolved_patch_names"]:
            item["gaps"].append(
                "Patch names have no exact registered extra-source mapping."
            )
        if not item["notices"]:
            item["gaps"].append(
                (
                    "No actual notice file found in retained sources or installed "
                    "package documentation."
                )
            )
        if not licenses:
            item["gaps"].append("Installed package metadata has no license field.")
        if (
            not source["checksums"]
            and not item["source_materials"]
            and not any(x["available_material"] for x in item["extra_sources"])
            and not any(x.get("git_commit") for x in item["retained_source_trees"])
        ):
            item["gaps"].append(
                (
                    "No immutable source digest/commit established from installed "
                    "metadata and retained tree."
                )
            )
        item["gaps"].append(
            (
                "Archived materials do not establish an exact binary rebuild or "
                "complete embedded dependency closure."
            )
        )
        return key

    def assign(path, key, method, details):
        if path in mapping:
            raise ValueError("Duplicate captured-file attribution")
        record = manifest["files"][path]
        mapping[path] = {
            "sha256": record["sha256"],
            "component": key,
            "method": method,
            "evidence": details,
            "capture_provenance": record.get("provenance"),
            "linked_component_scope": (
                "Container ownership only; embedded dependencies may differ."
            ),
        }
        components[key]["captured_files"].append(path)

    for path in manifest["files"]:
        matches = owners.get(path, [])
        if len(matches) > 1:
            raise ValueError("Ambiguous installation ownership: " + path)
        if matches:
            switch, package, relative = matches[0]
            key = opam_component(switch, package)
            record_path, records = switches[switch]["changes"][package]
            if sha(Path(path).read_bytes()) != manifest["files"][path]["sha256"]:
                raise ValueError("Installed package bytes differ from capture: " + path)
            assign(
                path,
                key,
                "OPAM_EXACT_INSTALLATION_CHANGE_RECORD",
                {
                    "path": str(record_path),
                    "relative_installed_path": relative,
                    "record": records[relative],
                    "record_is_content_hash": False,
                    "installed_bytes_match_capture": True,
                },
            )

    why_root = opam_root / "cryptotools-2026.09/.opam-switch/sources/why3.1.8.2"
    for path in manifest["files"]:
        if path not in mapping and Path(path).is_relative_to(why_root):
            assign(
                path,
                opam_component("cryptotools-2026.09", "why3"),
                "RETAINED_PACKAGE_SOURCE_WITH_INSTALLED_OPAM_METADATA",
                {
                    "retained_source": str(why_root),
                    "note": (
                        "Source path and captured digest observed; archive-to-file "
                        "correspondence not proved."
                    ),
                },
            )
    source_list = "/home/hacker-code-j/easycrypt/theories/datatypes/List.ec"
    installed_list = str(
        opam_root / "cryptotools-2026.09/lib/easycrypt/theories/datatypes/List.ec"
    )
    if (
        manifest["files"][source_list]["sha256"]
        == manifest["files"][installed_list]["sha256"]
    ):
        assign(
            source_list,
            mapping[installed_list]["component"],
            "BYTE_IDENTITY_WITH_ATTRIBUTED_INSTALLED_SOURCE",
            {
                "matched_file": installed_list,
                "sha256": manifest["files"][installed_list]["sha256"],
            },
        )
    else:
        root = Path(source_list).parents[2]
        raw = (root / "easycrypt.opam").read_text()
        calibration_root = args.calibration_evidence.resolve(strict=True)
        calibration_manifest = json.loads(
            (calibration_root / "manifest.json").read_text()
        )
        calibration_input = calibration_manifest["calibration_input"]
        if calibration_input["sha256"] != manifest["files"][source_list]["sha256"]:
            raise ValueError(
                "Upstream calibration evidence does not match captured input"
            )
        upstream_records, upstream_notices, source_materials = [], [], []
        for record in calibration_manifest["preserved_sources"]:
            local = calibration_root / record["local_evidence"]
            if not local.resolve().is_relative_to(calibration_root):
                raise ValueError("Calibration source evidence escapes root")
            content = local.read_bytes()
            if (
                sha(content) != record["sha256"]
                or hashlib.sha1(
                    b"blob " + str(len(content)).encode() + b"\0" + content
                ).hexdigest()
                != record["git_blob"]
            ):
                raise ValueError("Calibration upstream blob identity mismatch")
            upstream_records.append(
                {**record, "preserved_evidence": evidence.add(local)}
            )
            if is_notice(record["source_path"]):
                upstream_notices.append(evidence.add(local, "notice"))
            source_materials.append(
                source_blob(
                    content, record["source_url"], "EXACT_UPSTREAM_CALIBRATION_FILE"
                )
            )
        key = (
            "source:easycrypt-calibration-list@"
            + manifest["files"][source_list]["sha256"]
        )
        components[key] = {
            "name": "EasyCrypt calibration List.ec from separate retained source tree",
            "version": calibration_input["exact_upstream_revision"],
            "ecosystem": "source",
            "roles": ["captured-file-owner"],
            "captured_files": [],
            "license_declared": quoted(field(raw, "license")),
            "license_expression": "MIT",
            "metadata_license_expression": "CeCILL-C",
            "source_license_expression": "MIT",
            "source": {
                "file_sha256": manifest["files"][source_list]["sha256"],
                "development_repository": quoted(field(raw, "dev-repo")),
                "git_commit": calibration_input["exact_upstream_revision"],
                "git_blob": calibration_input["git_blob"],
                "source_path": calibration_input["exact_upstream_path"],
                "file_identity_scope": (
                    "Exact upstream file; not an identity claim for the whole local "
                    "source tree."
                ),
                "upstream_records": upstream_records,
                "retained_source_tree": str(root),
            },
            "metadata": [
                evidence.add(root / "easycrypt.opam"),
                evidence.add(root / "dune-project"),
                evidence.add(calibration_root / "manifest.json"),
                evidence.add(calibration_root / "github-metadata.json"),
            ],
            "notices": upstream_notices,
            "source_materials": source_materials,
            "license_metadata_notice_inconsistency": {
                "opam_declares": "CeCILL-C",
                "observed_notice_heading": "MIT License",
                "resolution": (
                    "Official file-level MIT notice and stale CeCILL-C metadata "
                    "preserved separately; not dual licensing."
                ),
            },
            "ownership_confidence": (
                "exact official Git blob and SHA256 identity from preserved "
                "primary-source evidence"
            ),
            "gaps": [
                "No Git metadata exists in this retained tree.",
                (
                    "File differs from installed2026.09 List.ec; do not substitute "
                    "installed source provenance."
                ),
                (
                    "File-level provenance does not identify the entire unpacked "
                    "source tree."
                ),
            ],
        }
        assign(
            source_list,
            key,
            "PINNED_SOURCE_FILE_AND_LOCAL_PROJECT_METADATA",
            {
                "source_file_sha256": manifest["files"][source_list]["sha256"],
                "different_installed_file_sha256": manifest["files"][installed_list][
                    "sha256"
                ],
            },
        )
    config_key = "local:easycrypt-configuration"
    components[config_key] = {
        "name": "Local EasyCrypt/Why3 configuration",
        "version": None,
        "ecosystem": "local",
        "roles": ["captured-file-owner"],
        "captured_files": [],
        "license_declared": [],
        "license_expression": None,
        "notices": [],
        "source": {"status": "CAPTURED_PLAINTEXT_IS_THE_OBSERVED_SOURCE"},
        "ownership_confidence": (
            "file origin known; author/generation process not established"
        ),
        "gaps": [
            "License and authorship of local configuration have not been established."
        ],
    }
    for name in ["easycrypt.conf", "why3.conf"]:
        path = "/home/hacker-code-j/.config/easycrypt/" + name
        assign(
            path,
            config_key,
            "LOCAL_CONFIGURATION_FILE",
            evidence.add(capture / manifest["files"][path]["archive_path"]),
        )

    for field_name in ["python_restoration", "coreutils_restoration"]:
        restoration = manifest[field_name]
        package = capture / restoration["package_path"]
        if sha(package.read_bytes()) != restoration["package_sha256"]:
            raise ValueError("Historic Debian package drift")
        control = run(["dpkg-deb", "--field", str(package)])
        fields = dict(re.findall(r"(?m)^([\w-]+): (.*)$", control))
        key = "deb:" + fields["Package"] + "@" + fields["Version"]
        item = {
            "name": fields["Package"],
            "version": fields["Version"],
            "ecosystem": "deb",
            "roles": ["captured-file-owner"],
            "captured_files": [],
            "source": {
                "package": fields.get("Source", fields["Package"]),
                "binary_package_url": restoration["source_url"],
                "binary_package_sha256": restoration["package_sha256"],
                "source_package_companion": "system-sources/source-packages.json",
                "source_package_companion_validation": "SEPARATE_PARENT_WORKSTREAM",
            },
            "metadata": [
                evidence.add_bytes(control.encode(), "dpkg-deb --field " + str(package))
            ],
            "license_expression": None,
            "license_declared": [],
            "notices": [],
            "ownership_confidence": "high: exact authenticated binary package payload",
            "gaps": [
                (
                    "Full corresponding source and embedded dependency coverage "
                    "require separate source-package companion."
                )
            ],
        }
        components[key] = item
        archive = tarfile.open(
            fileobj=io.BytesIO(
                subprocess.check_output(["dpkg-deb", "--fsys-tarfile", str(package)])
            )
        )
        members = {
            member.name.removeprefix("./"): member for member in archive.getmembers()
        }
        original = restoration["original_path"]
        payload = archive.extractfile(members[original.lstrip("/")]).read()
        if sha(payload) != manifest["files"][original]["sha256"]:
            raise ValueError("Debian package ownership payload mismatch")
        for name, member in members.items():
            if (
                member.isfile()
                and name.startswith("usr/share/doc/")
                and Path(name).name == "copyright"
            ):
                data = archive.extractfile(member).read()
                item["notices"].append(
                    evidence.add_bytes(
                        data,
                        "deb:" + restoration["package_sha256"] + "/" + name,
                        "notice",
                    )
                )
                item["license_declared"] = sorted(
                    set(
                        re.findall(
                            r"(?m)^License:\s*(.*)", data.decode(errors="replace")
                        )
                    )
                )
        assign(
            original,
            key,
            "EXACT_AUTHENTICATED_DEBIAN_PACKAGE_PAYLOAD",
            {
                "package_sha256": restoration["package_sha256"],
                "member": original.lstrip("/"),
            },
        )

    bash_info = run(
        [
            "dpkg-query",
            "-W",
            "-f=${Package}\t${Version}\t${source:Package}\t${source:Version}",
            "bash",
        ]
    ).split("\t")
    bash_md5sums = Path("/var/lib/dpkg/info/bash.md5sums")
    bash_records = dict(
        (name, value)
        for value, name in (
            line.split(None, 1) for line in bash_md5sums.read_text().splitlines()
        )
    )
    expected = bash_records.get("bin/bash")
    bash_bytes = (
        capture / manifest["files"]["/usr/bin/bash"]["archive_path"]
    ).read_bytes()
    if hashlib.md5(bash_bytes).hexdigest() != expected:
        raise ValueError("Captured Bash differs from installed package md5 record")
    bash_key = "deb:bash@" + bash_info[1]
    components[bash_key] = {
        "name": "bash",
        "version": bash_info[1],
        "ecosystem": "deb",
        "roles": ["captured-file-owner"],
        "captured_files": [],
        "source": {
            "package": bash_info[2],
            "version": bash_info[3],
            "source_package_companion": "system-sources/source-packages.json",
            "source_package_companion_validation": "SEPARATE_PARENT_WORKSTREAM",
        },
        "metadata": [
            evidence.add(bash_md5sums),
            evidence.add_bytes(
                run(["dpkg-query", "-s", "bash"]).encode(), "dpkg-query -s bash"
            ),
        ],
        "license_declared": [
            "GPL version 3 or any later version; file-specific notices also apply"
        ],
        "license_expression": None,
        "notices": [evidence.add(Path("/usr/share/doc/bash/copyright"), "notice")],
        "ownership_confidence": (
            "high installed package mapping and exact md5 payload match; md5 is not "
            "package signature authentication"
        ),
        "gaps": [
            (
                "Signed historic package/source authentication handled by separate "
                "source-package companion."
            )
        ],
    }
    assign(
        "/usr/bin/bash",
        bash_key,
        "DPKG_EXACT_PAYLOAD_MD5_AND_MERGED_USR_PATH",
        {
            "recorded_member": "bin/bash",
            "md5": expected,
            "dpkg_owner_query": run(["dpkg-query", "-S", "/bin/bash"]).strip(),
        },
    )
    if set(mapping) != set(manifest["files"]):
        raise ValueError(
            "Unattributed captured files: "
            + str(sorted(set(manifest["files"]) - set(mapping)))
        )

    linkage = []
    primary = [
        (switch, str(data["prefix"] / "bin" / name))
        for switch, names in [
            ("cryptotools-2026.09", ["easycrypt", "why3"]),
            ("ocaml-base-compiler.4.12.0", ["coqc", "coqtop"]),
        ]
        for data in [switches[switch]]
        for name in names
    ]
    for switch, original in primary:
        target = capture / manifest["files"][original]["archive_path"]
        command = ["nm", "-C", "--defined-only", str(target)]
        symbols = run(command)
        modules = sorted(
            set(re.findall(r"\bcaml([^\s]+?)(?:\.|__)code_begin$", symbols, re.M))
        )
        matches, unmatched = {}, []
        for module in modules:
            candidates = module_owners[switch].get(module.lower(), [])
            if not candidates and "." in module:
                candidates = module_owners[switch].get(module.split(".")[0].lower(), [])
            if not candidates:
                unmatched.append(module)
            for candidate in candidates:
                key = opam_component(
                    switch, candidate["package"], "defined-embedded-module-candidate"
                )
                matches.setdefault(key, []).append({"module": module, **candidate})
        linkage.append(
            {
                "captured_file": original,
                "sha256": manifest["files"][original]["sha256"],
                "command": command,
                "symbol_output_sha256": sha(symbols.encode()),
                "method": (
                    "Defined native OCaml module symbols matched to exact installed "
                    ".cmx ownership records."
                ),
                "confidence": (
                    "Module presence observed; source archive and exact build "
                    "linkage not proved by names."
                ),
                "module_matches": matches,
                "unmapped_modules": unmatched,
                "closure_complete": False,
            }
        )
        if original.endswith("/easycrypt"):
            vendor = (
                switches[switch]["prefix"]
                / ".opam-switch/sources/bitwuzla-cxx.0.9.1/vendor"
            )
            solver_patterns = {
                "bitwuzla": r"bitwuzla::",
                "cadical": r"CaDiCaL::",
                "kissat": r"\bkissat_",
                "symfpu": r"symfpu::",
                "cryptominisat": r"CMSat::",
            }
            for name, pattern in solver_patterns.items():
                matching = [
                    line for line in symbols.splitlines() if re.search(pattern, line)
                ]
                root = vendor / name
                if not root.exists():
                    continue
                key = "vendored:bitwuzla-cxx.0.9.1/" + name
                notice_list = [
                    evidence.add(f, "notice") for f in sorted(notice_paths(root))
                ]
                version = (
                    (root / "VERSION").read_text().strip()
                    if (root / "VERSION").is_file()
                    else None
                )
                if name == "bitwuzla":
                    version = re.search(
                        r"version:\s*'([^']+)'", (root / "meson.build").read_text()
                    ).group(1)
                if name == "cryptominisat":
                    version = re.search(
                        r'set\(CMS_FULL_VERSION "([^"]+)"',
                        (root / "CMakeLists.txt").read_text(),
                    ).group(1)
                source_records = []
                for source in [
                    root / "meson.build",
                    vendor / "bitwuzla/subprojects" / (name + ".wrap"),
                ]:
                    if source.exists():
                        source_records.append(evidence.add(source))
                components[key] = {
                    "name": name,
                    "version": version,
                    "ecosystem": "vendored",
                    "roles": ["defined-native-symbols-observed"]
                    if matching
                    else ["vendor-source-present-linkage-unconfirmed"],
                    "captured_files": [],
                    "embedded_in": original if matching else None,
                    "license_declared": [],
                    "license_expression": None,
                    "notices": notice_list,
                    "source": {
                        "parent_package": "opam:cryptotools-2026.09/bitwuzla-cxx@0.9.1",
                        "retained_tree": str(root),
                        "metadata": source_records,
                        "archive_coverage": components[
                            "opam:cryptotools-2026.09/bitwuzla-cxx@0.9.1"
                        ]["vendored_archive_coverage"][name],
                    },
                    "defined_symbol_examples": matching[:3],
                    "ownership_confidence": "defined symbol evidence"
                    if matching
                    else "source availability only",
                    "gaps": [
                        (
                            "Version/license variant and full "
                            "corresponding-source/build linkage require review of "
                            "original notices and source metadata."
                        )
                    ],
                }
                root_notice = next(
                    (
                        x
                        for x in [
                            root / "COPYING",
                            root / "LICENSE",
                            root / "LICENSE.txt",
                        ]
                        if x.is_file()
                    ),
                    None,
                )
                if root_notice:
                    notice_text = root_notice.read_text()
                    components[key]["license_declaration_evidence"] = evidence.add(
                        root_notice, "notice"
                    )
                    if (
                        name in {"bitwuzla", "cadical"}
                        and "MIT License" in notice_text[:1024]
                    ):
                        components[key]["license_declared"] = ["MIT"]
                        components[key]["license_expression"] = "MIT"
                    elif name == "kissat":
                        readme = root / "README.md"
                        if "License: MIT" in readme.read_text():
                            components[key]["license_declared"] = ["MIT"]
                            components[key]["license_expression"] = "MIT"
                            components[key][
                                "license_declaration_evidence"
                            ] = evidence.add(readme)
                    elif name == "symfpu":
                        components[key]["license_declared"] = [notice_text.strip()]
                        components[key][
                            "license_expression"
                        ] = "GPL V3 OR BSD 3-Clause (upstream wording)"
                    elif name == "cryptominisat":
                        components[key]["license_declared"] = [
                            (
                                "MIT default with conditional GPL provisions in "
                                "upstream notice."
                            )
                        ]
                        components[key]["gaps"].append(
                            (
                                "Exact solver build options and conditional GPL "
                                "applicability are not resolved by symbol presence."
                            )
                        )

            # The wrapper explicitly links PicoSAT separately inside the CMS tree.
            pico = vendor / "cryptominisat/src/picosat"
            pico_symbols = [
                line for line in symbols.splitlines() if re.search(r"\bpicosat_", line)
            ]
            pico_version = re.search(
                r'#define PICOSAT_VERSION "([^"]+)"',
                (pico / "pico_config.h").read_text(),
            ).group(1)
            cms = components["vendored:bitwuzla-cxx.0.9.1/cryptominisat"]
            cms_audit = json.loads(
                (
                    output / cms["source"]["archive_coverage"]["audit"]["archive_path"]
                ).read_text()
            )
            pico_members = {
                name: digest
                for name, digest in cms_audit["member_hashes"].items()
                if "/src/picosat/" in name
            }
            if not pico_members:
                raise ValueError("PicoSAT source members absent from wrapper archive")
            wrapper_key = "opam:cryptotools-2026.09/bitwuzla-cxx@0.9.1"
            wrapper = components[wrapper_key]
            cached_wrapper = wrapper["cached_source_archives"][0]["path"]
            recipe_records = []
            with tarfile.open(cached_wrapper) as archive:
                for relative in ["dune", "vendor/dune"]:
                    matching = [
                        item
                        for item in archive.getmembers()
                        if item.isfile()
                        and "/".join(PurePosixPath(item.name).parts[1:]) == relative
                    ]
                    if len(matching) != 1:
                        raise ValueError("Ambiguous wrapper build recipe")
                    path = vendor.parent / relative
                    if archive.extractfile(matching[0]).read() != path.read_bytes():
                        raise ValueError(
                            "Retained build recipe differs from source archive"
                        )
                    recipe_records.append(
                        {
                            "relative_source_path": relative,
                            "source_archive": wrapper["source_materials"][0],
                            "evidence": evidence.add(path),
                        }
                    )
            vendor_recipe = (vendor / "dune").read_text()
            recipe_observation = {
                "status": "SOURCE_RECIPE_OBSERVED_NOT_HISTORICAL_BUILD_ATTESTATION",
                "recipes": recipe_records,
                "configured_solver_flags": [
                    flag
                    for flag in [
                        "-DBZLA_USE_CADICAL",
                        "-DBZLA_USE_KISSAT",
                        "-DBZLA_USE_CMS",
                    ]
                    if flag in vendor_recipe
                ],
                "bliss_named_in_retained_recipe": "bliss" in vendor_recipe.lower(),
                "cms_build_surface": (
                    "Explicit Dune source list; not its upstream CMake MIT option."
                ),
                "limitations": (
                    "Historical build log/cache unavailable; recipe alone does not "
                    "prove binary build options or resolve conditional license "
                    "provisions."
                ),
            }
            wrapper["build_recipe_observation"] = recipe_observation
            cms["build_recipe_observation"] = recipe_observation
            components["vendored:bitwuzla-cxx.0.9.1/cryptominisat-picosat"] = {
                "name": "PicoSAT bundled inside CryptoMiniSat",
                "version": pico_version,
                "ecosystem": "vendored",
                "roles": ["defined-native-symbols-observed"]
                if pico_symbols
                else ["explicit-source-recipe-linkage"],
                "captured_files": [],
                "embedded_in": original if pico_symbols else None,
                "defined_symbol_examples": pico_symbols[:3],
                "declared_version_string_present_in_binary": pico_version.encode()
                in target.read_bytes(),
                "license_declared": [
                    (
                        "Permissive upstream LICENSE text; no SPDX identifier in its "
                        "header."
                    )
                ],
                "license_expression": None,
                "notices": [evidence.add(pico / "LICENSE", "notice")],
                "source": {
                    "parent_component": "vendored:bitwuzla-cxx.0.9.1/cryptominisat",
                    "parent_package": wrapper_key,
                    "retained_tree": str(pico),
                    "source_archive": wrapper["source_materials"][0],
                    "archive_member_hashes": pico_members,
                    "metadata": [
                        evidence.add(pico / "pico_config.h"),
                        evidence.add(pico / "version.c"),
                    ],
                    "archive_coverage": {
                        "file_count": len(pico_members),
                        "status": "EXACT_ARCHIVE_MEMBERS_MATCH_RETAINED_SOURCE",
                    },
                },
                "build_recipe_observation": recipe_observation,
                "ownership_confidence": (
                    "Exact archived source files plus explicit Dune link and "
                    "defined-symbol evidence."
                ),
                "gaps": [
                    (
                        "Exact binary build correspondence and complete link closure "
                        "are not established."
                    )
                ],
            }

    common = []
    for name in [
        "GPL-2",
        "GPL-3",
        "LGPL-2",
        "LGPL-2.1",
        "LGPL-3",
        "Apache-2.0",
        "BSD",
        "GFDL-1.2",
        "GFDL-1.3",
    ]:
        path = Path("/usr/share/common-licenses") / name
        if path.is_file():
            common.append(evidence.add(path, "notice"))
    for key, item in list(components.items()):
        if item["ecosystem"] != "opam":
            continue
        installed = switches[item["switch"]]["packages"]
        item["installed_declared_dependencies"] = sorted(
            {name for name in quoted(item["depends_raw"]) if name in installed}
        )
        item[
            "dependency_interpretation"
        ] = "Conditional opam dependency names; not an asserted link map."
        item["captured_file_count"] = len(item["captured_files"])
    system_status_bytes = args.system_source_status.read_bytes()
    system_status = json.loads(system_status_bytes)
    system_versions = {
        item["name"]: item["version"] for item in system_status["packages"]
    }
    for item in components.values():
        if item["ecosystem"] != "deb":
            continue
        source_name = item["source"]["package"].split()[0]
        version = item["source"].get("version", item["version"])
        if system_versions.get(source_name) != version:
            raise ValueError(
                "System source status version does not match captured component"
            )
        item["source"]["version"] = version
        item["source"]["source_package_companion"] = "system-sources/"
        item["source"]["source_package_companion_validation"] = system_status["status"]
        item["source"]["acquisition_status_record"] = "system-source-status.json"
    system_record = {
        "status": system_status["status"],
        "archive_path": "system-source-status.json",
        "sha256": sha(system_status_bytes),
        "original_path": str(args.system_source_status.resolve()),
        "packages": system_status["packages"],
    }
    (output / "system-source-status.json").write_bytes(system_status_bytes)
    (source_output / "system-source-status.json").write_bytes(system_status_bytes)
    inventory = {
        "schema": 1,
        "status": "ATTRIBUTION_AND_NOTICE_INVENTORY_NOT_DISTRIBUTION_CLEARANCE",
        "preserved_manifest_sha256": sha(manifest_bytes),
        "captured_file_count": len(mapping),
        "component_count": len(components),
        "components": components,
        "system_source_acquisition": system_record,
        "common_license_texts": common,
        "limitations": [
            (
                "All captured files are attributed; this does not establish complete "
                "embedded/static dependency licensing."
            ),
            (
                "Native plugins and system executable embedded components are not "
                "exhaustively analyzed."
            ),
            (
                "Installed .changes records establish file association, not "
                "immutable source-to-binary reproducibility."
            ),
            (
                "Conditional dependencies and vendored source presence are not proof "
                "of actual linkage."
            ),
            (
                "Exact corresponding source, patches and reproducible build closure "
                "remain separate requirements."
            ),
            (
                "License expressions are copied from metadata; file-specific terms "
                "and exceptions require review."
            ),
        ],
    }
    for name, value in [
        ("inventory.json", inventory),
        ("files.json", mapping),
        ("embedded-components.json", linkage),
    ]:
        (output / name).write_text(
            json.dumps(value, indent=2, ensure_ascii=False) + "\n"
        )
    (output / "COMPONENTS.md").write_text(component_table(components))
    shutil.copytree(output / "evidence", source_output / "evidence")
    source_manifest = {
        "schema": 1,
        "status": "SOURCE_MATERIALS_ARCHIVED_BUILD_NOT_REPLAYED",
        "preserved_manifest_sha256": sha(manifest_bytes),
        "notice_inventory_sha256": sha((output / "inventory.json").read_bytes()),
        "blobs": source_blobs,
        "blob_count": len(source_blobs),
        "blob_bytes": sum(x["bytes"] for x in source_blobs.values()),
        "system_source_acquisition": system_record,
        "components": {
            key: {
                name: item.get(name)
                for name in [
                    "source",
                    "metadata",
                    "source_materials",
                    "extra_sources",
                    "patches_raw",
                    "unresolved_patch_names",
                    "git_source_submodule_entries",
                    "build_recipe_observation",
                    "gaps",
                ]
            }
            for key, item in components.items()
        },
        "limitations": [
            (
                "Raw source materials and original installed build recipes are "
                "provided; no binary rebuild is asserted."
            ),
            (
                "Conditional dependencies, tool versions, system libraries and "
                "per-plugin linking remain outside proven build closure."
            ),
            "System Debian corresponding source packages are a separate companion.",
            (
                "Original archive bytes are preserved; Git-derived snapshots are "
                "labelled separately."
            ),
        ],
    }
    (source_output / "source-materials.json").write_text(
        json.dumps(source_manifest, indent=2) + "\n"
    )
    (source_output / "SHA256SUMS").write_text(
        "".join(
            f"{sha(path.read_bytes())}  {path.relative_to(source_output)}\n"
            for path in sorted(source_output.rglob("*"))
            if path.is_file()
        )
    )
    entries = sorted(p for p in output.rglob("*") if p.is_file())
    (output / "SHA256SUMS").write_text(
        "".join(f"{sha(p.read_bytes())}  {p.relative_to(output)}\n" for p in entries)
    )
    if (
        manifest_path.read_bytes() != public_manifest_bytes
        or (capture / "manifest.json").read_bytes() != manifest_bytes
    ):
        raise ValueError("Preserved manifest changed during inventory")
    print(
        json.dumps(
            {
                "files": len(mapping),
                "components": len(components),
                "notices": len(list((output / "notices").glob("*"))),
                "metadata_files": len(list((output / "evidence").glob("*"))),
            }
        )
    )


if __name__ == "__main__":
    main()
