"""Judge a FriCAS unit-test log by its statistics() summaries.

Usage: python3 tools/check_summary.py LOG

Passes (exit 0) when the log has at least one "File summary." block from
FriCAS's unit-test package and every such block reports
"unexpected failures: 0" and "unexpected passes: 0". Prints the summary lines.
A log without any summary (compile error, crash, wrong path) fails.
"""

import re
import sys


def main(path: str) -> int:
    text = open(path, encoding="utf-8", errors="replace").read()
    blocks = re.findall(r"File summary\.(.*?)total tests:\s*(\d+)", text, re.S)
    if not blocks:
        print(f"{path}: no statistics() summary found; see the log")
        tail = text.strip().splitlines()[-25:]
        print("\n".join("    " + line for line in tail))
        return 1
    ok = True
    for body, total in blocks:
        nums = dict(re.findall(r"(unexpected failures|expected failures|unexpected passes):\s*(\d+)", body))
        line = (f"total tests {total}, unexpected failures {nums.get('unexpected failures')}, "
                f"expected failures {nums.get('expected failures')}, "
                f"unexpected passes {nums.get('unexpected passes')}")
        bad = nums.get("unexpected failures") != "0" or nums.get("unexpected passes") != "0"
        ok = ok and not bad
        print(f"{path}: {'FAIL' if bad else 'ok'}: {line}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
