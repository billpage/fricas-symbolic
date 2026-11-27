#!/usr/bin/env python3
"""Generate docs/tutorial/tutorial.md from its template and recorded transcripts.

    python3 tools/tutorial/build_tutorial.py            # write tutorial.md
    python3 tools/tutorial/build_tutorial.py --check    # fail if tutorial.md differs

The template (docs/tutorial/tutorial.src.md) is ordinary GitHub markdown with
placeholders of the form

    <!--run:NAME:SECTION-->            one section of transcript NAME
    <!--run:NAME:SECTION+SECTION-->    several sections, in the order given

NAME is the stem of a file in docs/tutorial/transcripts/ (see the README there)
and SECTION is a "-- ==== SECTION" marker in the script that produced it.  Each
placeholder is replaced by a ```text block holding the commands and results of
that section, exactly as FriCAS printed them, with these display rules only:
`)clear` lines, macro definitions, declarations and function definitions are
shown without their (empty) result, and the Type line is dropped when it is
Boolean, Void, InputForm or String, or a SymbolicExpression-family type (the
text says what the type is).  No result is ever typed by hand.
"""
import argparse
import difflib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from parse_run import parse  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
TUT = ROOT / 'docs' / 'tutorial'

DECL = re.compile(r"^[A-Za-z0-9_]+ : .* := ")
FUNDEF = re.compile(r"^[A-Za-z0-9_]+\(.*\) : .* == ")
HIDE_TYPES = {'Boolean', 'Void', 'InputForm', 'String'}
HIDE_PREFIXES = ('SymbolicExpression(', 'SymbolicTerm(',
                 'GeneralSymbolicExpression(',
                 'Union(SymbolicExpression(', 'Union(GeneralSymbolicExpression(')


def render(section):
    out = []
    for c in section:
        inp = c['in']
        if inp.startswith(')clear'):
            continue
        out.append(inp)
        if '==>' in inp or DECL.match(inp) or FUNDEF.match(inp):
            continue
        for m in c['msgs']:
            if m.startswith('>>'):
                _, _, b = m.partition('library code:')
                out.append('   >> Error detected within library code:')
                out.append('   ' + b.strip())
        for line in c['out']:
            out.append('   ' + line)
        t = c['type']
        if t and t not in HIDE_TYPES and not t.startswith(HIDE_PREFIXES) and c['out']:
            out.append('   Type: ' + t)
    return '\n'.join(out)


def build(src_path, transcripts):
    parsed = {}

    def sections(name):
        if name not in parsed:
            f = transcripts / (name + '.out')
            if not f.exists():
                sys.exit(f'error: no transcript {f}')
            parsed[name] = parse(str(f))[0]
        return parsed[name]

    def fill(m):
        name, wanted = m.group(1), m.group(2).split('+')
        secs = sections(name)
        body = []
        for w in wanted:
            if w not in secs:
                sys.exit(f'error: transcript {name} has no section {w!r}; '
                         f'it has {sorted(secs)}')
            body += secs[w]
        return '```text\n' + render(body) + '\n```'

    return re.sub(r'<!--run:([\w-]+):([\w+-]+)-->', fill,
                  Path(src_path).read_text())


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--src', default=TUT / 'tutorial.src.md')
    ap.add_argument('--transcripts', default=TUT / 'transcripts', type=Path)
    ap.add_argument('-o', '--output', default=TUT / 'tutorial.md', type=Path)
    ap.add_argument('--check', action='store_true',
                    help='do not write; exit 1 if the output file would change')
    a = ap.parse_args()
    text = build(a.src, a.transcripts)
    if a.check:
        old = a.output.read_text() if a.output.exists() else ''
        if old == text:
            print(f'{a.output.name}: up to date')
            return
        sys.stdout.writelines(difflib.unified_diff(
            old.splitlines(True), text.splitlines(True), 'committed', 'generated', n=1))
        sys.exit(f'{a.output.name} is out of date; run build_tutorial.py')
    a.output.write_text(text)
    print(f'{a.output}: {len(text.splitlines())} lines')


if __name__ == '__main__':
    main()
