"""Round-trip and corruption checks for lossless scientific capsule parts."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from scripts.bench.groebner_parts import load_capsule


class PartsTests(unittest.TestCase):
    def fixture(self,root):
        archive=root/'original.tar.xz';data=b'complete scientific output\n'
        payloads={'value.txt':data,'sha256.json':json.dumps({'value.txt':hashlib.sha256(data).hexdigest()}).encode()}
        with tarfile.open(archive,'w:xz')as stream:
            for name,value in payloads.items():
                member=tarfile.TarInfo('test/'+name);member.size=len(value)
                stream.addfile(member,io.BytesIO(value))
        raw=archive.read_bytes();middle=len(raw)//2;parts=[]
        for i,payload in enumerate([raw[:middle],raw[middle:]]):
            name=f'evidence.part{i}';(root/name).write_bytes(payload)
            parts.append(dict(file=name,bytes=len(payload),sha256=hashlib.sha256(payload).hexdigest()))
        index=dict(format=1,parts=parts,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        path=root/'evidence.parts.json';path.write_text(json.dumps(index))
        return path,index,data

    def test_round_trip(self):
        with tempfile.TemporaryDirectory()as directory:
            path,_,data=self.fixture(Path(directory));cap=load_capsule(path)
            self.assertEqual(cap.read('value.txt'),data)
            self.assertEqual(cap.path,path)
            self.assertEqual(cap.index_sha256,hashlib.sha256(path.read_bytes()).hexdigest())

    def test_corrupt_part(self):
        with tempfile.TemporaryDirectory()as directory:
            path,index,_=self.fixture(Path(directory));part=path.parent/index['parts'][0]['file']
            data=bytearray(part.read_bytes());data[-1]^=1;part.write_bytes(data)
            with self.assertRaisesRegex(ValueError,'part digest'):load_capsule(path)

    def test_reordered_parts(self):
        with tempfile.TemporaryDirectory()as directory:
            path,index,_=self.fixture(Path(directory));index['parts'].reverse();path.write_text(json.dumps(index))
            with self.assertRaisesRegex(ValueError,'assembled capsule'):load_capsule(path)

    def test_parent_path(self):
        with tempfile.TemporaryDirectory()as directory:
            path,index,_=self.fixture(Path(directory));index['parts'][0]['file']='../outside'
            path.write_text(json.dumps(index))
            with self.assertRaisesRegex(ValueError,'basename'):load_capsule(path)

    def test_malformed_index(self):
        with tempfile.TemporaryDirectory()as directory:
            path,index,_=self.fixture(Path(directory))
            for value in [[],{},dict(index,sha256=None),dict(index,parts=[{}])]:
                path.write_text(json.dumps(value))
                with self.assertRaises(ValueError):load_capsule(path)

    def test_oversize_part(self):
        with tempfile.TemporaryDirectory()as directory:
            path,index,_=self.fixture(Path(directory));index['parts'][0]['bytes']=96*1024**2
            path.write_text(json.dumps(index))
            with self.assertRaisesRegex(ValueError,'part size'):load_capsule(path)


if __name__=='__main__':unittest.main()
