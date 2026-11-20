#!/usr/bin/env python3
"""Audit: how many idol-lib graph 'definition' nodes are top-level, and how many
are nested locals (indented) or otherwise not definitions. argv: REPO PIN"""
import json, subprocess, sys, collections
repo, pin = sys.argv[1], sys.argv[2]
def git(*a): return subprocess.run(["git", "-C", repo, *a], capture_output=True, check=True).stdout.decode(errors="replace")
files = [p for p in git("ls-tree", "-r", "--name-only", pin, "graphs/").split() if p.endswith("graph.json")]
src = {}
tot = collections.Counter(); bylib = collections.defaultdict(collections.Counter); nested = []
refs_to = collections.Counter()
for f in files:
    g = json.loads(git("show", f"{pin}:{f}"))
    defs = {n["id"]: n for n in g["nodes"] if n.get("kind") == "definition"}
    for n in defs.values():
        path = n["source"]["path"]; ln = n["source"]["span"]["start_line"]
        if path not in src: src[path] = git("show", f"{pin}:{path}").split("\n")
        line = src[path][ln - 1] if ln - 1 < len(src[path]) else ""
        kind = "top" if line[:1] not in (" ", "\t") else "nested"
        tot[kind] += 1; bylib[n["library"]][kind] += 1
        if kind == "nested": nested.append((n["library"], n["name"], path, ln, line.strip()[:60]))
    for n in defs.values():
        for r in n.get("references", []):
            cs = [c for c in r["candidates"] if c in defs and c != n["id"]]
            if len(cs) == 1: refs_to[cs[0]] += 1
    for nid, k in refs_to.items():
        pass
out = {"pin": pin, "definitions": sum(tot.values()), "top_level": tot["top"], "nested_locals": tot["nested"],
       "by_library": {k: dict(v) for k, v in sorted(bylib.items())}}
print(json.dumps(out, indent=1))
for x in nested[:15]: print("NESTED", *x, sep="\t")
