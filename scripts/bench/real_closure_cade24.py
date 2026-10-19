#!/usr/bin/env python3
"""Fetch and verify the original CADE-24 input archive without executing it."""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import struct
import tempfile
import time
import urllib.error
import urllib.request
import zipfile
import zlib

REPORT = Path(__file__).resolve().parents[2] / 'reports/bench-results/real-closure-cade24-inputs'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_range(url, start, size, total, opener=urllib.request.urlopen):
    """Refuse a server that ignores Range; never read the 42 GB container."""
    require(0 < size <= 1_000_000 and 0 <= start < start + size <= total,
            'invalid bounded archive range')
    request = urllib.request.Request(url, headers={
        'Range': f'bytes={start}-{start + size - 1}', 'Accept-Encoding': 'identity'})
    for attempt in range(3):
        try:
            with opener(request, timeout=60) as response:
                require(response.status == 206, 'server did not honor archive Range')
                require(response.headers.get('Content-Range') ==
                        f'bytes {start}-{start + size - 1}/{total}', 'wrong Content-Range')
                require(response.headers.get('Content-Encoding', 'identity') == 'identity',
                        'unexpected HTTP content encoding')
                data = response.read(size + 1)
            break
        except urllib.error.HTTPError as error:
            if attempt == 2 or error.code not in (429, 500, 502, 503, 504):
                raise
            error.close()
            time.sleep(attempt + 1)
    require(len(data) == size, 'wrong range response length')
    return data


def inflate(data, member):
    decoder = zlib.decompressobj(-15)
    result = decoder.decompress(data, member['size'] + 1)
    require(decoder.eof and not decoder.unconsumed_tail and not decoder.unused_data,
            'invalid or oversized compressed member')
    require(len(result) == member['size'], 'member size differs')
    require(zlib.crc32(result) == member['crc32'], 'member CRC differs')
    require(digest(result) == member['sha256'], 'member SHA-256 differs')
    return result


def fetch_member(manifest, member, reader=read_range):
    url, total, offset = manifest['archive_url'], manifest['archive_size'], member['offset']
    header = reader(url, offset, 30, total)
    signature, version, flags, method, _, _, crc, compressed, size, name_len, extra_len = \
        struct.unpack('<I5H3I2H', header)
    require(signature == 0x04034B50 and version <= 20 and flags == 0 and method == 8,
            'unsupported ZIP local header')
    require((crc, compressed, size) ==
            (member['crc32'], member['compressed_size'], member['size']),
            'ZIP local header differs from source manifest')
    require(name_len <= 1024 and extra_len <= 4096, 'oversized ZIP local header')
    body = reader(url, offset + 30, name_len + extra_len + compressed, total)
    require(body[:name_len].decode('ascii') == member['name'], 'ZIP member name differs')
    return inflate(body[name_len + extra_len:], member)


def root_calls(tree):
    return sorted([
        dict(line=node.lineno, coefficients_ascending=ast.unparse(node.args[0]))
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id == 'MkRoots'
    ], key=lambda item: item['line'])


def helper_calls(tree):
    """Retain actual helper arguments, including the Strzeboński polynomials."""
    return sorted([
        dict(line=node.lineno, helper=node.func.id,
             arguments=[ast.unparse(argument) for argument in node.args])
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id in ('Sqrt', 'FindRoots')
    ], key=lambda item: item['line'])


def selections(tree):
    return sorted([
        dict(line=node.lineno, collection=ast.unparse(node.value), index=ast.unparse(node.slice))
        for node in ast.walk(tree) if isinstance(node, ast.Subscript)
    ], key=lambda item: item['line'])


def bindings(tree):
    return sorted([
        dict(line=node.lineno, targets=[ast.unparse(target) for target in node.targets],
             value=ast.unparse(node.value))
        for node in ast.walk(tree) if isinstance(node, ast.Assign)
    ], key=lambda item: item['line'])


def tower_stages(tree):
    stages = []
    for node in tree.body:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in [f'r{i}' for i in range(5)]:
            value = node.value
            require(isinstance(value, ast.Subscript) and isinstance(value.value, ast.Call)
                    and isinstance(value.value.func, ast.Name)
                    and value.value.func.id == 'MkRoots' and len(value.value.args) == 1
                    and isinstance(value.value.args[0], ast.List)
                    and isinstance(value.slice, ast.Constant)
                    and type(value.slice.value) is int, 'invalid tower root assignment')
            stages.append(dict(name=node.targets[0].id,
                               coefficients_ascending=[ast.unparse(value)
                                   for value in node.value.value.args[0].elts],
                               returned_root_index=node.value.slice.value))
    require([stage['name'] for stage in stages] == [f'r{i}' for i in range(5)],
            'tower stage inventory differs')
    return stages


def verify(folder, manifest, tower):
    members = {}
    for member in manifest['members']:
        path = folder / member['file']
        require(path.stat().st_size == member['size'], 'source member size differs')
        data = path.read_bytes()
        require(len(data) == member['size'] and digest(data) == member['sha256'],
                'source member differs: ' + member['file'])
        members[member['file']] = data
    require(all(name in members for name in
                ['releaseList.json', 'documents.json', 'CADE24.html', 'cade24ex.zip']),
            'required original source member missing')
    releases = json.loads(members['releaseList.json'])
    release = next((item for item in releases if item.get('Id') == manifest['release']['id']), None)
    require(release is not None, 'original release missing')
    wanted = manifest['release']
    require(release.get('Name') == wanted['name'] and
            wanted['paper_title'] in ' '.join(release.get('Description', '').split()),
            'release paper identity differs')
    entry = next((item for item in release.get('Files', [])
                  if item.get('Id') == wanted['file_id']), None)
    require(entry is not None, 'original release file missing')
    require(entry.get('FileName') == wanted['file_name'] and
            entry.get('UploadDate') == wanted['upload_date'] and
            entry.get('Url') == './0/' + wanted['file_id'], 'release source link differs')
    examples = [item.get('Id') for release in releases for item in release.get('Files', [])
                if item.get('Type') == 'Example']
    require(examples == [wanted['file_id']], 'unique Example release identity differs')
    documents = json.loads(members['documents.json'])
    require(any(item.get('Id') == manifest['wiki']['id'] and
                item.get('Title') == manifest['wiki']['title'] for item in documents),
            'original wiki document identity differs')
    require(b'http://z3.codeplex.com/downloads/get/606232' in members['CADE24.html'],
            'original CADE wiki examples link missing')
    trees = {}
    with zipfile.ZipFile(io.BytesIO(members['cade24ex.zip'])) as archive:
        expected = {'cade24ex/' + item['name'] for item in manifest['scripts']}
        names = [item.filename for item in archive.infolist() if not item.is_dir()]
        require(len(names) == len(expected) and set(names) == expected,
                'script member inventory differs')
        for item in manifest['scripts']:
            info = archive.getinfo('cade24ex/' + item['name'])
            require(info.file_size == item['size'] and info.CRC == item['crc32'],
                    'script member metadata differs')
            body = archive.read(info)
            require(digest(body) == item['sha256'], 'script SHA-256 differs')
            tree = ast.parse(body.decode('utf-8'))
            require(root_calls(tree) == item['root_calls'], 'root input transcription differs')
            require(helper_calls(tree) == item['helper_calls'], 'helper arguments differ')
            require(selections(tree) == item['selections'], 'root selections differ')
            require(bindings(tree) == item['bindings'], 'source assignment bindings differ')
            trees[item['name']] = tree
    normal, eager = trees[tower['source']], trees[tower['eager_source']]
    require(tower_stages(normal) == tower_stages(eager) == tower['stages'],
            'clean/eager tower root inputs or selected indices differ')
    # The entire source syntax, not just the coefficient lists, agrees after
    # removing the single normalization-policy call from the eager script.
    policy = ast.parse('set_param("rcf.lazy_algebraic_normalization", False)').body[0]
    stripped = [node for node in eager.body if ast.dump(node) != ast.dump(policy)]
    require(len(stripped) + 1 == len(eager.body) and
            ast.dump(ast.Module(body=stripped, type_ignores=[])) == ast.dump(normal),
            'eager script differs beyond its normalization-policy call')
    return dict(scripts=len(trees), tower_stages=len(tower['stages']),
                tower_degrees=[len(stage['coefficients_ascending']) - 1
                               for stage in tower['stages']],
                clean_eager_identical_except_policy=True,
                archive_sha256=digest(members['cade24ex.zip']),
                manifest_sha256=digest(json.dumps(manifest, sort_keys=True).encode()),
                tower_inputs_sha256=digest(json.dumps(tower, sort_keys=True).encode()),
                verifier_sha256=digest(Path(__file__).read_bytes()))


def verify_inventory(manifest, tower, checks):
    """Offline CI check of committed transcriptions and retained result bindings."""
    require(checks['manifest_sha256'] == digest(json.dumps(manifest, sort_keys=True).encode()),
            'stale source inventory binding')
    require(checks['tower_inputs_sha256'] == digest(json.dumps(tower, sort_keys=True).encode()),
            'stale tower transcription binding')
    require(checks['verifier_sha256'] == digest(Path(__file__).read_bytes()),
            'stale verifier binding')
    require(checks['tower_degrees'] == [4, 2, 4, 5, 5] and
            [len(stage['coefficients_ascending']) - 1 for stage in tower['stages']]
            == checks['tower_degrees'], 'wrong original tower degrees')
    require([stage['name'] for stage in tower['stages']] == [f'r{i}' for i in range(5)]
            and all(stage['returned_root_index'] == 0 for stage in tower['stages']),
            'original tower assignments or selections differ')
    require(checks['scripts'] == len(manifest['scripts']) == 14 and
            checks['tower_stages'] == len(tower['stages']) == 5 and
            checks['clean_eager_identical_except_policy'] is True, 'source summary differs')
    original = next((item for item in manifest['members'] if item['file'] == 'cade24ex.zip'), None)
    require(original is not None, 'original example archive member missing')
    require(checks['archive_sha256'] == original['sha256'], 'source archive binding differs')
    for name in [tower['source'], tower['eager_source']]:
        script = next((item for item in manifest['scripts'] if item['name'] == name), None)
        require(script is not None, 'original tower script inventory missing')
        require([call['coefficients_ascending'] for call in script['root_calls']] ==
                ['[' + ', '.join(stage['coefficients_ascending']) + ']'
                 for stage in tower['stages']], 'tower transcription differs from root inventory')
        require([item['index'] for item in script['selections']] == ['0'] * 5,
                'original tower root indices differ')


def fetch(folder, manifest):
    require(not folder.exists() and not folder.is_symlink(), 'destination already exists')
    folder.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=folder.name + '.', dir=folder.parent) as temporary:
        staging = Path(temporary) / 'complete'
        staging.mkdir()
        for member in manifest['members']:
            (staging / member['file']).write_bytes(fetch_member(manifest, member))
        require(not folder.exists() and not folder.is_symlink(), 'destination appeared during fetch')
        staging.rename(folder)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['fetch', 'check'])
    parser.add_argument('folder', type=Path)
    args = parser.parse_args()
    manifest = json.loads((REPORT / 'source.json').read_text())
    tower = json.loads((REPORT / 'tower8.json').read_text())
    if args.action == 'fetch':
        fetch(args.folder, manifest)
    print(json.dumps(verify(args.folder, manifest, tower), indent=2))


if __name__ == '__main__':
    main()
