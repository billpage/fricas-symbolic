"""Split a recorded FriCAS run into sections, commands, results and types.

A transcript is the output of the run_fricas tool for a script that has
"-- ==== NAME" marker lines (one per section) and ends with "-- ==== end".
parse(path) returns ({section: [command, ...]}, [section order]); a command is
{'in': input line, 'out': result lines, 'msgs': message paragraphs,
 'type': the Type: line or None, 'done': bool}.
Used by build_tutorial.py; "python3 parse_run.py TRANSCRIPT OUT.json" dumps the
parse for inspection.
"""
import re, sys, json
def parse(path):
    txt = open(path).read()
    # drop everything before the tutorial header and after the end marker
    i = re.search(r'^-- ====', txt, re.M).start()
    j = re.search(r'^-- ==== end', txt, re.M).start()
    body = txt[i:j].replace('\r', '')
    raw = []
    prev_ind = False
    cur_p = []
    for l in body.split('\n'):
        ind = l.startswith(' ') or l.startswith('Type:')
        if not l.strip():
            if cur_p: raw.append('\n'.join(cur_p)); cur_p = []
            prev_ind = False
            continue
        if cur_p and prev_ind and not ind:
            raw.append('\n'.join(cur_p)); cur_p = []
        cur_p.append(l)
        prev_ind = ind
    if cur_p: raw.append('\n'.join(cur_p))
    paras = raw
    sections, cur, cmd = {}, None, None
    order = []
    def newcmd(inp):
        nonlocal cmd
        cmd = {'in': inp, 'out': [], 'msgs': [], 'type': None, 'done': False}
        sections[cur].append(cmd)
    for p in paras:
        lines = p.split('\n')
        if not lines or all(not l.strip() for l in lines):
            continue
        first = lines[0]
        if first.startswith('   Type:') or first.startswith('Type:'):
            t = ' '.join(l.strip() for l in lines)
            t = t.replace('Type: ', '', 1)
            if cmd is not None: cmd['type'] = t; cmd['done'] = True
            continue
        if first.startswith('   '):
            msg = [l.strip() for l in lines]
            if any(m.startswith('Type:') for m in msg):
                if cmd is not None: cmd['done'] = True; cmd['type'] = 'Void'
                msg = [m for m in msg if not m.startswith('Type:')]
                if msg and cmd is not None: cmd['msgs'].append(' '.join(msg))
                continue
            if cmd is not None:
                cmd['msgs'].append(' '.join(msg))
                if msg[0].startswith('Continuing') or msg[0].startswith('All user variables'):
                    cmd['done'] = True
            continue
        # column-0 paragraph: may start with comment lines
        keep = []
        for l in lines:
            if l.startswith('-- ===='):
                cur = l[len('-- ===='):].strip(); sections[cur] = []; order.append(cur); cmd = None
            elif l.startswith('--'):
                continue
            else:
                keep.append(l)
        if not keep: continue
        if cmd is None or cmd['done']:
            # a column-0 paragraph with several lines: first is the input
            newcmd(keep[0])
            if len(keep) > 1:
                cmd['out'] = keep[1:]
        else:
            cmd['out'] += keep
    return sections, order
if __name__ == '__main__':
    s, o = parse(sys.argv[1])
    json.dump({'order': o, 'sections': s}, open(sys.argv[2], 'w'), indent=1)
    for k in o:
        print(k, len(s[k]))
