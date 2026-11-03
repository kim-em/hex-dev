"""Evidence reader regression tests, independent of large retained capsules."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from scripts.bench.groebner_capsule import Capsule


class CapsuleTests(unittest.TestCase):
    def make(self, directory, change=None):
        entries = {"data.json": b'{"value": 3}\n'}
        entries["sha256.json"] = json.dumps({k: hashlib.sha256(v).hexdigest()
                                            for k, v in entries.items()}).encode()
        if change:
            change(entries)
        path = Path(directory) / "capsule.tar.gz"
        with tarfile.open(path, "w:gz") as archive:
            folder = tarfile.TarInfo("capsule/")
            folder.type = tarfile.DIRTYPE
            archive.addfile(folder)
            for name, data in entries.items():
                info = tarfile.TarInfo("capsule/" + name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
        return path

    def test_verified_payload(self):
        with tempfile.TemporaryDirectory() as directory:
            capsule = Capsule(self.make(directory))
            self.assertEqual(capsule.json("data.json"), {"value": 3})
            self.assertEqual(capsule.count, 1)  # Excludes directories and manifest.
            local = Path(directory) / "data.json"
            local.write_bytes(capsule.read("data.json"))
            capsule.bind(local, "data.json")
            local.write_bytes(b'{"value": 4}\n')
            with self.assertRaisesRegex(ValueError, "local input differs"):
                capsule.bind(local, "data.json")

    def test_corrupted_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.make(directory, lambda files: files.update({"data.json": b"corrupt"}))
            with self.assertRaisesRegex(ValueError, "digest mismatch"):
                Capsule(path)

    def test_missing_payload(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.make(directory, lambda files: files.pop("data.json"))
            with self.assertRaisesRegex(ValueError, "manifest/member mismatch"):
                Capsule(path)

    def test_unlisted_payload(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.make(directory, lambda files: files.update({"extra": b"extra"}))
            with self.assertRaisesRegex(ValueError, "manifest/member mismatch"):
                Capsule(path)

    def test_duplicate_member(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.make(directory)
            with tarfile.open(path) as archive:
                entries = [(member, archive.extractfile(member).read())
                           for member in archive if member.isfile()]
            with tarfile.open(path, "w:gz") as archive:
                for member, data in entries + entries[:1]:
                    archive.addfile(member, io.BytesIO(data))
            with self.assertRaisesRegex(ValueError, "duplicate capsule member"):
                Capsule(path)

    def test_link_member(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.make(directory)
            with tarfile.open(path) as archive:
                entries = [(member, archive.extractfile(member).read())
                           for member in archive if member.isfile()]
            with tarfile.open(path, "w:gz") as archive:
                for member, data in entries:
                    archive.addfile(member, io.BytesIO(data))
                link = tarfile.TarInfo("capsule/link")
                link.type = tarfile.SYMTYPE
                link.linkname = "data.json"
                archive.addfile(link)
            with self.assertRaisesRegex(ValueError, "unsupported capsule member"):
                Capsule(path)


if __name__ == "__main__":
    unittest.main()
