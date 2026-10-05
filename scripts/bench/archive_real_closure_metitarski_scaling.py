#!/usr/bin/env python3
"""Archive one complete capture and verify both reports against its raw points."""
import argparse
import json
from pathlib import Path
import shutil

try:
    from .analyze_real_closure_metitarski_scaling import digest, require, summarize
except ImportError:
    from analyze_real_closure_metitarski_scaling import digest, require, summarize

BEGIN = '<!-- metitarski-results -->'
END = '<!-- /metitarski-results -->'
REPORT = Path('reports/bench-results/real-closure-metitarski-scaling/README.md')
ARCHIVE = Path('reports/bench-results/real-closure-metitarski-scaling-14b03f')


def results_text(result):
    """Derive every reported number from the validated retained point inventory."""
    def ms(value):
        return '—' if value is None else f'{value / 1e6:.3f}'
    lines = [BEGIN, '## Retained results', '',
             f"Measured source: `{result['source']}`.", '',
             f"Completed samples: {result['completed_samples']} of {result['attempts']} attempts.", '',
             '| Degree | Completed trials | Median ms | Range ms | Median ms / n³ | Head bytes | Descriptor bytes |',
             '| --- | --- | --- | --- | --- | --- | --- |']
    for row in result['rows']:
        limits = f"{ms(row['min_ns'])}–{ms(row['max_ns'])}" if row['min_ns'] is not None else '—'
        lines.append(f"| {row['degree']} | {row['completed_trials']} | {ms(row['median_ns'])} | "
                     f"{limits} | {ms(row['normalized_median_ns'])} | {row['head_bytes']} | "
                     f"{row['descriptor_bytes']} |")
    lines += ['', f"Harness verdict: `{result['harness_verdict']}`; slope: "
              f"`{result['harness_slope']}`; leading points dropped: "
              f"`{result['harness_dropped_leading']}`.", '',
              'The ranges and medians use every completed trial. The raw export retains each',
              'batch duration, repeat count, signal-floor flag and failure status; the derived',
              'analysis retains them by degree. The harness verdict is reported separately',
              'from these descriptive observations. This finite ladder does not establish',
              'asymptotic complexity or acceptance of the other Phase 4 families.', END]
    return '\n'.join(lines)


def verify(folder, report):
    result = summarize(folder, archive=True)
    require(json.loads((folder/'analysis.json').read_text()) == result,
            'derived analysis differs from retained points')
    fragment = results_text(result)
    for path in [folder/'README.md', report]:
        text = path.read_text()
        require(text.count(BEGIN) == text.count(END) == 1 and fragment in text,
                'reported results differ from retained points: '+str(path))
    return result


def create(capture, folder, report):
    result = summarize(capture)
    record = json.loads((capture/'manifest.json').read_text())
    # Requiring a new directory retains existing captures and archives.
    folder.mkdir(parents=True, exist_ok=False)
    omitted = {name: record['artifacts'][name]
               for name in ['hexrealclosure_bench', 'hexrealclosure_phase4']}
    for source in capture.rglob('*'):
        if source.is_file() and str(source.relative_to(capture)) not in omitted:
            target = folder/source.relative_to(capture)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    (folder/'analysis.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    fragment = results_text(result)
    (folder/'README.md').write_text(
        '# MetiTarski degree ladder capture\n\n'
        'This archive retains all command logs, functional and measured-input packets,\n'
        'independent oracle outputs, raw timings, host metadata and seven measured\n'
        'source snapshots. The two executables are omitted; their SHA-256 identities\n'
        'remain in the original manifest and archive index. `analysis.json` and the\n'
        'tables are recomputed from every retained raw point.\n\n'+fragment+'\n')
    protocol = report.read_text()
    require(BEGIN not in protocol and END not in protocol, 'report already has results')
    report.write_text(protocol+'\n'+fragment+'\n\n'
                      '[Raw capture and source snapshots](../'+folder.name+'/README.md).\n')
    index = dict(schema='metitarski-scaling-v1', commit=record['commit'],
                 omitted_snapshots=omitted,
                 files={str(p.relative_to(folder)):digest(p)
                        for p in folder.rglob('*') if p.is_file()})
    (folder/'archive.json').write_text(json.dumps(index, indent=2, sort_keys=True)+'\n')
    return verify(folder, report)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--archive', type=Path, default=ARCHIVE)
    parser.add_argument('--report', type=Path, default=REPORT)
    args = parser.parse_args()
    if args.capture:
        result = create(args.capture, args.archive, args.report)
    else:
        result = verify(args.archive, args.report)
    print(json.dumps(dict(source=result['source'], attempts=result['attempts'],
                          completed=result['completed_samples'])))
