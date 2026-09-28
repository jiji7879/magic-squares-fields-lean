"""Compile Audit.lean and reject missing reports or unexpected endpoint axioms."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    targets = re.findall(r'^#print axioms (\S+)', (ROOT / 'scripts/Audit.lean').read_text(), re.M)
    result = subprocess.run(['lake', 'env', 'lean', 'scripts/Audit.lean'], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(result.returncode)
    reports = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        reports[name] = set(re.findall(r'[\w.]+', raw))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        reports[name] = set()
    for name in targets:
        if name not in reports:
            raise SystemExit(f'Missing axiom report for {name}; inspect Lean output format.')
        unexpected = reports[name] - ALLOWED
        if unexpected:
            raise SystemExit(f'Unexpected axioms for {name}: {sorted(unexpected)}')
    print(f'PASS: {len(targets)} endpoint reports; all axioms are in {sorted(ALLOWED)}.')


if __name__ == '__main__':
    main()
