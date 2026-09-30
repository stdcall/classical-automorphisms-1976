"""Advisory Russian prose check, shared Book rules and the Typst parser."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    sources = sorted((ROOT/'content').rglob('*.typ'))
    result = subprocess.run(
        ['vale', '--config', str(ROOT/'config/vale/.vale.ini'),
         '--output', 'JSON', *map(str, sources)],
        capture_output=True, text=True)
    if result.returncode not in (0, 1) or not result.stdout.strip():
        raise SystemExit(result.stderr or result.stdout or 'Vale produced no JSON')
    count = 0
    for name, issues in json.loads(result.stdout).items():
        for item in issues:
            count += 1
            print(f'{name}:{item["Line"]}:{item["Span"][0]} '
                  f'{item["Check"]}: {item["Message"]}')
    print(f'Vale: {count} findings (advisory)')


if __name__ == '__main__':
    main()
