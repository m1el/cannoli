"""Compare the RC11 definitions of ORC11/RC11.lean with herd7's rc11.cat.

Usage: litmus.py <lean-output> <litmus-dir> <herd7> <herd-libdir>

<lean-output> is what `tools/Litmus.lean` prints. For every test this checks
that herd7 with rc11.cat finds
  * the same number of consistent executions,
  * the same set of final states (registers and memory),
  * the same answer to "is some consistent execution racy",
and the same for each final state alone: herd7 runs again with a `filter`
restricting it to the executions ending in that state, and must find as many
executions as Lean does, racy exactly when one of Lean's is.
"""

import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict


def parse_lean(path):
    tests = {}
    cur = None
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("test "):
                m = re.match(r"test (\S+) candidates=(\d+) consistent=(\d+)", line)
                cur = {"consistent": int(m.group(3)), "execs": []}
                tests[m.group(1)] = cur
            elif line.startswith("exec "):
                body, racy = line[5:].rsplit(" racy=", 1)
                cur["execs"].append((frozenset(body.split()), racy == "true"))
    return tests


def herd(herd7, libdir, path):
    out = subprocess.run(
        [herd7, "-I", libdir, "-model", "rc11.cat", path],
        capture_output=True, text=True, check=True).stdout
    states = set()
    lines = out.splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("States "))
    for l in lines[i + 1:i + 1 + int(lines[i].split()[1])]:
        toks = [t.strip().replace("[", "").replace("]", "") for t in l.split(";") if t.strip()]
        states.add(frozenset(toks))
    pos, neg = map(int, re.search(r"Positive: (\d+) Negative: (\d+)", out).groups())
    undef = "Flag *undef*" in out
    return states, pos + neg, undef, out


def herd_cond(state):
    return " /\\ ".join(sorted(state))


def main():
    lean_out, dirname, herd7, libdir = sys.argv[1:5]
    tests = parse_lean(lean_out)
    failures = 0
    checks = 0
    for name, t in tests.items():
        path = os.path.join(dirname, name + ".litmus")
        states, count, undef, _ = herd(herd7, libdir, path)
        lstates = {s for s, _ in t["execs"]}
        lracy = any(r for _, r in t["execs"])
        problems = []
        if count != t["consistent"]:
            problems.append(f"executions: lean {t['consistent']}, herd {count}")
        if states != lstates:
            problems.append(f"states: only lean {sorted(map(sorted, lstates - states))}, "
                            f"only herd {sorted(map(sorted, states - lstates))}")
        if undef != lracy:
            problems.append(f"racy: lean {lracy}, herd {undef}")
        # per final state
        per = defaultdict(list)
        for s, r in t["execs"]:
            per[s].append(r)
        src = open(path).read()
        for s, rs in per.items():
            checks += 1
            filtered = src.replace("exists (", f"filter ({herd_cond(s)})\nexists (", 1)
            with tempfile.NamedTemporaryFile("w", suffix=".litmus", delete=False) as f:
                f.write(filtered)
            try:
                _, c, u, _ = herd(herd7, libdir, f.name)
            finally:
                os.unlink(f.name)
            if c != len(rs) or u != any(rs):
                problems.append(f"state {herd_cond(s)}: lean {len(rs)} execs racy={any(rs)}, "
                                f"herd {c} execs racy={u}")
        checks += 1
        verdict = "ok" if not problems else "MISMATCH"
        print(f"{verdict:8} {name:16} execs={t['consistent']:3} states={len(lstates):2} "
              f"racy={lracy}")
        for p in problems:
            print("         " + p)
        failures += bool(problems)
    print(f"{len(tests)} tests, {checks} herd7 runs, {failures} mismatches")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
