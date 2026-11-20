# Record-level layer (G6) at successive pins, incremental through a blob cache,
# with from-scratch recounts. Records: elements of every list-valued field
# (recursively one level into dicts) of every JSON file under graphs/.
import hashlib, json, subprocess, sys, collections
REPO, PINS = sys.argv[1], sys.argv[2].split(",")
def git(*a): return subprocess.run(["git","-C",REPO,*a],capture_output=True,check=True).stdout
def H(b): return hashlib.sha256(b).hexdigest()
cache = {}   # blob oid -> list of record hashes (computed once per distinct blob)
hashed = 0
def records_of(data):
    try: obj = json.loads(data)
    except Exception: return []
    out = []
    def take(lst):
        for x in lst: out.append(H(json.dumps(x, sort_keys=True, separators=(",",":")).encode()))
    if isinstance(obj, list): take(obj)
    elif isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, list) and v and isinstance(v[0], dict): take(v)
            elif isinstance(v, dict):
                for k2, v2 in v.items():
                    if isinstance(v2, list) and v2 and isinstance(v2[0], dict): take(v2)
    return out
def red(l): return len(l) - len(set(l))
rows = []
for pin in PINS:
    tree = git("ls-tree","-r",pin,"graphs/").decode().splitlines()
    files = []
    for ln in tree:
        meta, path = ln.split("\t",1)
        oid = meta.split()[2]
        if not path.endswith(".json"): continue
        if oid not in cache:
            cache[oid] = records_of(git("cat-file","-p",oid)); hashed += 1
        files.append((path, oid, cache[oid]))
    recs = [r for _, _, rs in files for r in rs]
    # from-scratch recount: reread every blob without the cache
    scratch = []
    for path, oid, _ in files: scratch += records_of(git("cat-file","-p",oid))
    nonempty = [f for f in files if f[2]]
    file_red = red([oid for _, oid, _ in nonempty])
    # which files share records with another file
    owner = collections.defaultdict(set)
    for path, _, rs in files:
        for r in set(rs): owner[r].add(path)
    cross = collections.Counter()
    for r, ps in owner.items():
        if len(ps) > 1:
            for p in ps: cross[p] += 1
    rows.append({"pin": pin, "json_files": len(files), "records": len(recs),
                 "record_red": red(recs), "scratch_record_red": red(scratch),
                 "agree": red(recs) == red(scratch) and len(recs) == len(scratch),
                 "file_red_nonempty": file_red, "blobs_hashed_so_far": hashed,
                 "files_sharing_records": dict(cross.most_common(12))})
print(json.dumps(rows, indent=1))
