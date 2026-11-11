"""Boundary tests for local provenance inspection, without modifying inputs."""
import tempfile
import io
import tarfile
import unittest
from pathlib import Path

import inventory


class InventoryTests(unittest.TestCase):
    def test_patch_names_exclude_version_conditions(self):
        raw = '["fix.diff" {ocaml:version >= "5.0"} "plain.patch"]'
        self.assertEqual(inventory.unfiltered_items(raw), ["fix.diff", "plain.patch"])
        with self.assertRaises(ValueError):
            inventory.unfiltered_items('"fix" {"5.0"')

    def test_registered_extra_sources_preserve_checksums(self):
        raw = (
            'extra-source "fix.patch" {\n src: "https://example.test/fix"\n'
            ' checksum: "sha256=abc"\n}\n'
        )
        record = inventory.extra_sources(raw)[0]
        self.assertEqual(record["name"], "fix.patch")
        self.assertEqual(record["checksums"], ["sha256=abc"])
        with self.assertRaises(ValueError):
            inventory.extra_sources(raw.replace("fix.patch", "../fix.patch"))

    def test_archive_notices_read_bytes_without_extracting_links(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "source.tar"
            with tarfile.open(path, "w") as archive:
                item = tarfile.TarInfo("pkg/LICENSE")
                data = b"original\r\nnotice"
                item.size = len(data)
                archive.addfile(item, io.BytesIO(data))
                link = tarfile.TarInfo("pkg/NOTICE")
                link.type = tarfile.SYMTYPE
                link.linkname = "/private"
                archive.addfile(link)
            self.assertEqual(
                list(inventory.archive_notices(path)), [("pkg/LICENSE", data)]
            )
            self.assertFalse((root / "pkg").exists())

    def test_multiline_fields_preserve_qualifiers(self):
        text = (
            'license: ["MIT" "LGPL-2.1-only"]\ndepends: [\n "coq" {>= "8"}\n]\nurl '
            '{\n src: "https://example.test/source"\n checksum: "sha256=abc"\n}\n'
        )
        self.assertEqual(
            inventory.quoted(inventory.field(text, "license")), ["MIT", "LGPL-2.1-only"]
        )
        self.assertIn('{>= "8"}', inventory.field(text, "depends"))
        self.assertEqual(
            inventory.url_metadata(text)["src"], ["https://example.test/source"]
        )

    def test_change_records_ignore_directories(self):
        text = 'added: [\n "lib/coq" {"D"}\n "lib/coq/file.vo"\n {"F:S123T42"}\n]\n'
        self.assertEqual(
            inventory.change_records(text), {"lib/coq/file.vo": "F:S123T42"}
        )

    def test_unsafe_change_path_rejected(self):
        for name in ("../private", "/etc/private", "lib/../private"):
            with self.assertRaises(ValueError):
                inventory.change_records('added: ["' + name + '" {"F:S1T1"}]')

    def test_duplicate_conflicting_change_records_rejected(self):
        with self.assertRaises(ValueError):
            inventory.change_records('added: ["lib/f" {"F:S1T1"} "lib/f" {"F:S2T2"}]')

    def test_notice_matching_avoids_source_code(self):
        for name in ("LICENSE", "COPYING.LESSER", "LICENSE-GPL3", "NOTICE.txt"):
            self.assertTrue(inventory.is_notice(name))
        for name in ("license.ml", "copyright.c", "README.md", "licenses.ml"):
            self.assertFalse(inventory.is_notice(name))

    def test_evidence_preserves_bytes_and_deduplicates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence = inventory.Evidence(root)
            data = b"license\r\nexact bytes\xff"
            one = evidence.add_bytes(data, "upstream-a/LICENSE", "notice")
            two = evidence.add_bytes(data, "upstream-b/COPYING", "notice")
            self.assertEqual(one["archive_path"], two["archive_path"])
            self.assertEqual((root / one["archive_path"]).read_bytes(), data)


if __name__ == "__main__":
    unittest.main()
