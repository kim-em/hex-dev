"""Read F4 evidence through its verified per-payload SHA-256 manifest."""
import hashlib
from pathlib import PurePosixPath
import tarfile

from scripts.bench.groebner_json import loads


class Capsule:
    def __init__(self, path):
        self.path = path
        with path.open("rb") as stream:
            self.sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
        self.payloads = {}
        with tarfile.open(path) as archive:
            members = archive.getmembers()
            files = [member for member in members if member.isfile()]
            if not files or any(not member.isfile() and not member.isdir() for member in members):
                raise ValueError("unsupported capsule member")
            names = [member.name for member in files]
            if len(names) != len(set(names)):
                raise ValueError("duplicate capsule member")
            roots = {PurePosixPath(name).parts[0] for name in names}
            if len(roots) != 1:
                raise ValueError("capsule must have one root")
            prefix = next(iter(roots)) + "/"
            manifest_name = prefix + "sha256.json"
            manifest = loads(archive.extractfile(manifest_name).read().decode())
            expected = {prefix + name for name in manifest} | {manifest_name}
            if set(names) != expected:
                raise ValueError("capsule manifest/member mismatch")
            for member in files:
                data = archive.extractfile(member).read()
                relative = member.name.removeprefix(prefix)
                if member.name != manifest_name and hashlib.sha256(data).hexdigest() != manifest[relative]:
                    raise ValueError("capsule payload digest mismatch: " + relative)
                self.payloads[relative] = data
        self.count = len(self.payloads)-1

    def read(self, relative):
        return self.payloads[relative]

    def text(self, relative):
        return self.read(relative).decode()

    def json(self, relative):
        return loads(self.text(relative))

    def bind(self, path, relative):
        """Reject substituted unpacked files before an analysis consumes them."""
        if path.read_bytes() != self.read(relative):
            raise ValueError("local input differs from capsule: " + relative)
