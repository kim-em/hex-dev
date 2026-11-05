"""Read lossless capsule parts whose individual files fit GitHub's size limit."""
import hashlib
from pathlib import Path
import tempfile
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_json import loads


def load_capsule(path: Path):
    if path.suffix!='.json':return Capsule(path)
    raw=path.read_bytes();index=loads(raw.decode())
    if index.get('format')!=1 or not index.get('parts'):
        raise ValueError('invalid capsule parts index')
    total=hashlib.sha256();size=0
    with tempfile.TemporaryDirectory(prefix='f4-capsule-')as directory:
        joined=Path(directory)/'joined.tar.xz'
        with joined.open('wb')as output:
            for part in index['parts']:
                name=part['file'];expected=part['bytes']
                if not isinstance(name,str)or name in['.','..']or '/'in name or '\\'in name or not name:
                    raise ValueError('capsule part must be a basename')
                if type(expected)is not int or not 0<expected<=100*1024**2:
                    raise ValueError('invalid capsule part size')
                source=path.parent/name
                if source.is_symlink()or not source.is_file()or source.stat().st_size!=expected:
                    raise ValueError('capsule part is missing or has wrong size')
                digest=hashlib.sha256();count=0
                with source.open('rb')as stream:
                    while data:=stream.read(1024**2):
                        count+=len(data)
                        if count>expected:raise ValueError('capsule part grew while reading')
                        digest.update(data);total.update(data);output.write(data)
                if count!=expected or digest.hexdigest()!=part['sha256']:
                    raise ValueError('capsule part digest differs')
                size+=count
        if size!=index['bytes']or total.hexdigest()!=index['sha256']:
            raise ValueError('assembled capsule digest differs')
        result=Capsule(joined)
    result.path=path
    result.index_sha256=hashlib.sha256(raw).hexdigest()
    return result
