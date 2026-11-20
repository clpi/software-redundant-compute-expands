# Measurement scaffolding (Python). Reads a git checkout read-only; writes JSON to stdout.
# Canonical unit: parallel support = records whose projected implication was already
# supported by an earlier record, at each resolution level (projections of symbol ids).
import hashlib, json, re, subprocess, sys, random, collections
REPO = sys.argv[1]
PINS = sys.argv[2].split(",")
LIBS = ["adler32","base64","cbor","crc32","jq","json","lz4","md5","msgpack","qoi","sha1","sha256","snappy","xxhash"]
SKIP = {"battery.id","bench.id","vectors.id","cases.id"}
DEF = re.compile(r"^([A-Za-z][A-Za-z0-9]*)\s*=\s*(.*)$")
def h(t): return hashlib.sha256(t.encode()).hexdigest()[:16]
def git(*a): return subprocess.run(["git","-C",REPO,*a],capture_output=True,check=True).stdout
blob_cache = {}
def blob(pin, path):
    oid = git("rev-parse", f"{pin}:{path}").decode().strip()
    if oid not in blob_cache:
        blob_cache[oid] = git("cat-file","-p",oid)
    return oid, blob_cache[oid]
def ls(pin, prefix):
    out = git("ls-tree","-r","--name-only",pin,prefix).decode().splitlines()
    return out
def bodies(pin, lib):
    # definition body text per name (first definition wins), name stripped from first line
    res = {}
    for p in sorted(ls(pin, lib + "/")):
        name = p.rsplit("/",1)[-1]
        if not p.endswith(".id") or name in SKIP: continue
        _, data = blob(pin, p)
        cur, body = None, []
        def flush():
            if cur is not None and cur not in res:
                res[cur] = (p, "\n".join(body))
        for ln in data.decode(errors="replace").splitlines():
            m = DEF.match(ln)
            if m and not ln[:1].isspace():
                flush(); cur, body = m.group(1), [m.group(2)]
            elif cur is not None: body.append(ln)
        flush()
    return res
def measure(pin):
    log, nodes = [], {}
    body = {}
    for lib in LIBS:
        _, data = blob(pin, f"graphs/{lib}/graph.json")
        g = json.loads(data)
        for n in g["nodes"]: nodes[n["id"]] = (lib, n)
        for e in g["edges"]: log.append((lib, e))
        for name, (path, b) in bodies(pin, lib).items():
            body[f"def:{lib}:{name}"] = (path, b)
    def key(level, nid):
        lib, n = nodes[nid]
        if level == "symbol": return nid
        if level == "content":   # sound total equivalence: defs by body text, terms by value
            if n["kind"] == "definition":
                b = body.get(nid)
                return "def|" + (h(b[1]) if b else "missing:" + nid)
            return n["kind"] + "|" + n["shape"]
        if level == "file":
            if n["kind"] == "definition":
                b = body.get(nid); return "file|" + lib + "|" + (b[0] if b else "?")
            return n["kind"] + "|" + lib
        if level == "library": return "lib|" + lib
        if level == "joined-name":  # the joined.json identification (defs by name across libs)
            if n["kind"] == "definition": return "def|" + n["name"]
            return n["kind"] + "|" + n["shape"]
        raise ValueError(level)
    levels = ["symbol","content","joined-name","file","library"]
    out = {"pin": pin, "records": len(log), "levels": {}}
    for lv in levels:
        impl = [ (tuple(sorted(key(lv,p) for p in e["premises"])), key(lv, e["conclusion"])) for _, e in log ]
        # incremental fold
        seen, inc, flags = set(), 0, []
        for x in impl:
            r = x in seen; inc += r; flags.append(r); seen.add(x)
        scratch = len(impl) - len(set(impl))
        orders = set()
        for s in range(5):
            l2 = impl[:]; random.Random(s).shuffle(l2)
            orders.add(len(l2) - len(set(l2)))
        groups = collections.Counter(impl)
        dup = {k:v for k,v in groups.items() if v > 1}
        bykind = collections.Counter(e["kind"] for (_, e), f in zip(log, flags) if f)
        out["levels"][lv] = {"parallel": inc, "scratch": scratch, "agree": inc == scratch,
            "order_invariant": orders == {scratch}, "groups": len(dup),
            "members_in_groups": sum(dup.values()), "by_kind": dict(bykind)}
    # monotone chain check: symbol <= content <= joined? (content vs joined not nested in general)
    return out
res = [measure(p) for p in PINS]
print(json.dumps(res, indent=1))
