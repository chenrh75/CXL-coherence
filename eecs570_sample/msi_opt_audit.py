#!/usr/bin/env python3
"""Check repaired protocol scenarios and every subsequent drain interleaving."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

SCENARIOS = (
    'ids', 'rdshared', 'rdany_clean', 'address', 'rdany_shared', 'history',
    'dirty_snoop', 'clean_snoop', 'first_ack', 'stale_read', 'cacheflushed_channel',
    'handoff', 'handoff_response_first', 'bogus', 'dirty_cur', 'rdcurr_dirty',
    'flush_dirty', 'wrinv', 'wrcur', 'itomwr', 'own_nodata', 'clean_nodata_snoop',
    'id_reuse', 'go_before_data',
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scenario', choices=('all',) + SCENARIOS, default='all')
    parser.add_argument('--java', default=shutil.which('java') or '/tmp/msi-tla-jre/bin/java')
    parser.add_argument('--ids', type=int, default=1)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    if not Path(args.java).is_file():
        parser.error('Java was not found; supply --java /path/to/java')
    if args.ids < 1:
        parser.error('--ids must be positive')
    if args.workers < 1:
        parser.error('--workers must be positive')
    here = Path(__file__).resolve().parent
    output = (args.output_dir or Path(tempfile.mkdtemp(prefix='cxl-cache-checks-'))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    for module in ('msi_opt.tla', 'msi_opt_audit.tla'):
        shutil.copyfile(here / module, output / module)
    scenarios = SCENARIOS if args.scenario == 'all' else (args.scenario,)
    results = []
    print(f'Logs and counterexamples: {output}', flush=True)
    for scenario in scenarios:
        config = output / f'{scenario}.cfg'
        config.write_text(
            'CONSTANTS\n  ProcCount = 3\n  ValueCount = 2\n'
            f'  MaxUQID = {args.ids}\n  Undefined = Undefined\n  Scenario = "{scenario}"\n'
            'SPECIFICATION AuditSpec\nCHECK_DEADLOCK FALSE\n'
            'INVARIANTS TypeOK Safety AuditProperty\nPROPERTY EventualDone\n'
        )
        trace = output / f'{scenario}.json'
        trace.unlink(missing_ok=True)
        command = [args.java, '-XX:+UseParallelGC', '-Xmx1g', '-cp', str(here.parent / 'tla2tools.jar'),
                   'tlc2.TLC', '-workers', str(args.workers), '-noGenerateSpecTE', '-config', config.name,
                   '-dumpTrace', 'json', str(trace), '-metadir', str(output / f'{scenario}-states'),
                   'msi_opt_audit']
        with (output / f'{scenario}.log').open('w') as log:
            completed = subprocess.run(command, cwd=output, stdout=log, stderr=subprocess.STDOUT)
        log_text = (output / f'{scenario}.log').read_text()
        passed = (completed.returncode == 0
                  and 'Model checking completed. No error has been found.' in log_text)
        stats = re.search(r'(\d+) states generated, (\d+) distinct states found', log_text)
        result = {'scenario': scenario, 'passed': passed, 'exit_code': completed.returncode,
                  'distinct_states': int(stats.group(2)) if stats else None,
                  'diagnostics': re.findall(r'^Error: (.*)$', log_text, re.MULTILINE)[:2]}
        results.append(result)
        print(f'{scenario}: {"PASS" if passed else "FAIL"} ({result["distinct_states"]} states)', flush=True)
    (output / 'summary.json').write_text(json.dumps(results, indent=2) + '\n')
    return 0 if all(item['passed'] for item in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
