/* horn: incremental Horn reasoning over one append-only clause log (native build of ../horn.py).

   Class: TPTP CNF, Horn, no equality, function-free up to ground terms (EPR). Clauses are appended
   one at a time; each new fact is joined against the facts already derived through the body
   positions it can occupy (semi-naive forward chaining), so an appended clause costs only the
   derivations it enables. The worklist is FIFO, so a refutation is found at the smallest
   derivation depth reachable first, which keeps proofs short. A refutation is printed as the
   derivation DAG and can be re-checked by ../check.py (--proof-json).

   Usage: horn PROBLEM.p [--root DIR] [--proof-json FILE]
   Output: "% SZS status Unsatisfiable|Satisfiable|GaveUp for NAME" and a stats line. */
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void die(const char *m) { fprintf(stderr, "horn: %s\n", m); exit(3); }
static void *xmalloc(size_t n) { void *p = malloc(n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xrealloc(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }

typedef struct { int *a; int n, cap; } ivec;
static void ipush(ivec *v, int x) { if (v->n == v->cap) { v->cap = v->cap ? v->cap * 2 : 4; v->a = xrealloc(v->a, v->cap * sizeof(int)); } v->a[v->n++] = x; }

/* ---------------- symbols */
typedef struct { char **s; int n, cap; int *tab; int tcap; } symtab;
static symtab SY;
static uint64_t hstr(const char *s) { uint64_t h = 1469598103934665603ULL; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ULL; } return h; }
static int intern(const char *s) {
    if (SY.tcap == 0) { SY.tcap = 1024; SY.tab = xmalloc(SY.tcap * sizeof(int)); memset(SY.tab, -1, SY.tcap * sizeof(int)); }
    if (SY.n * 2 >= SY.tcap) {
        int nc = SY.tcap * 2; int *nt = xmalloc(nc * sizeof(int)); memset(nt, -1, nc * sizeof(int));
        for (int i = 0; i < SY.n; i++) { uint64_t h = hstr(SY.s[i]) & (nc - 1); while (nt[h] >= 0) h = (h + 1) & (nc - 1); nt[h] = i; }
        free(SY.tab); SY.tab = nt; SY.tcap = nc;
    }
    uint64_t h = hstr(s) & (SY.tcap - 1);
    while (SY.tab[h] >= 0) { if (!strcmp(SY.s[SY.tab[h]], s)) return SY.tab[h]; h = (h + 1) & (SY.tcap - 1); }
    if (SY.n == SY.cap) { SY.cap = SY.cap ? SY.cap * 2 : 256; SY.s = xrealloc(SY.s, SY.cap * sizeof(char *)); }
    SY.s[SY.n] = strdup(s); SY.tab[h] = SY.n; return SY.n++;
}

/* ---------------- clauses: terms >= 0 are constants (symbol ids), < 0 are variables -(k+1) */
typedef struct { int pred, ar, *args; } atom;
typedef struct { int name; int has_head; atom head; atom *body; int nb, nvars; char *unsafe; } rule;
static rule *R; static int NR, CR;

/* ---------------- facts */
typedef struct { int pred, off, rule, poff, np; } fact;
static fact *F; static int NF, CF;
static int *ARGS; static long NARGS, CARGS;     /* fact argument storage */
static int *PREM; static long NPREM, CPREM;     /* premise fact ids */
static int *PAR;  static int NPAR;              /* arity of each predicate symbol, -1 unknown */
static int *FT; static long FTCAP, FTN;         /* fact dedup table */
typedef struct { uint64_t key; ivec v; } ixe;    /* (pred,pos,val) -> fact ids */
static ixe *IX; static long IXCAP, IXN;
static ivec *BYP; static int NBYP;              /* pred -> list of rule*256+pos */
static char *IXON; static int NIXON;            /* (pred*64+pos) -> argument index built yet (on demand) */
static int ixon(int p, int k) { long i = (long)p * 64 + k; return i < NIXON && IXON[i]; }
static ivec CONSTS; static char *ISCONST; static int NISC;
static long OPS;
static int REFUTED = -1, REF_POFF, REF_NP;
static int *QUEUE; static long QH, QT, QCAP;

static uint64_t hfact(int p, const int *a, int n) { uint64_t h = (uint64_t)p * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < n; i++) { h ^= (uint64_t)(unsigned)a[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); } return h; }
static ivec *ixget(int p, int pos, int val, int create) {
    uint64_t key = ((uint64_t)(unsigned)p << 40) ^ ((uint64_t)(unsigned)pos << 32) ^ (uint64_t)(unsigned)val;
    key = key * 2 + 1;
    if (IXCAP == 0) { IXCAP = 4096; IX = xmalloc(IXCAP * sizeof(ixe)); memset(IX, 0, IXCAP * sizeof(ixe)); }
    if (create && IXN * 2 >= IXCAP) {
        long nc = IXCAP * 2; ixe *nt = xmalloc(nc * sizeof(ixe)); memset(nt, 0, nc * sizeof(ixe));
        for (long i = 0; i < IXCAP; i++) if (IX[i].key) { uint64_t h = (IX[i].key * 0x9E3779B97F4A7C15ULL) & (nc - 1); while (nt[h].key) h = (h + 1) & (nc - 1); nt[h] = IX[i]; }
        free(IX); IX = nt; IXCAP = nc;
    }
    uint64_t h = (key * 0x9E3779B97F4A7C15ULL) & (IXCAP - 1);
    while (IX[h].key) { if (IX[h].key == key) return &IX[h].v; h = (h + 1) & (IXCAP - 1); }
    if (!create) return NULL;
    IX[h].key = key; IXN++; return &IX[h].v;
}
static int fact_eq(int f, int p, const int *a, int n) { if (F[f].pred != p) return 0; return !memcmp(ARGS + F[f].off, a, n * sizeof(int)); }
static int arity(int p) { return p < NPAR ? PAR[p] : -1; }
static int find_fact(int p, const int *a, int n) {
    if (!FTCAP) return -1;
    uint64_t h = hfact(p, a, n) & (FTCAP - 1);
    while (FT[h] >= 0) { if (fact_eq(FT[h], p, a, n)) return FT[h]; h = (h + 1) & (FTCAP - 1); }
    return -1;
}
static void ft_insert(int f) {
    if (FTN * 2 >= FTCAP) {
        long nc = FTCAP ? FTCAP * 2 : 4096; int *nt = xmalloc(nc * sizeof(int)); memset(nt, -1, nc * sizeof(int));
        for (long i = 0; i < FTCAP; i++) if (FT[i] >= 0) { int g = FT[i]; uint64_t h = hfact(F[g].pred, ARGS + F[g].off, arity(F[g].pred)) & (nc - 1); while (nt[h] >= 0) h = (h + 1) & (nc - 1); nt[h] = g; }
        free(FT); FT = nt; FTCAP = nc;
    }
    int n = arity(F[f].pred);
    uint64_t h = hfact(F[f].pred, ARGS + F[f].off, n) & (FTCAP - 1);
    while (FT[h] >= 0) h = (h + 1) & (FTCAP - 1);
    FT[h] = f; FTN++;
}
static void insert_fact(int p, const int *a, int n, int rule_i, const int *prem, int np) {
    if (find_fact(p, a, n) >= 0) return;
    if (NF == CF) { CF = CF ? CF * 2 : 1024; F = xrealloc(F, CF * sizeof(fact)); }
    if (NARGS + n > CARGS) { CARGS = (CARGS + n) * 2; ARGS = xrealloc(ARGS, CARGS * sizeof(int)); }
    if (NPREM + np > CPREM) { CPREM = (CPREM + np) * 2 + 1024; PREM = xrealloc(PREM, CPREM * sizeof(int)); }
    int f = NF++;
    F[f].pred = p; F[f].off = (int)NARGS; F[f].rule = rule_i; F[f].poff = (int)NPREM; F[f].np = np;
    memcpy(ARGS + NARGS, a, n * sizeof(int)); NARGS += n;
    memcpy(PREM + NPREM, prem, np * sizeof(int)); NPREM += np;
    ft_insert(f);
    ipush(ixget(p, 255, 0, 1), f);
    for (int k = 0; k < n; k++) if (ixon(p, k)) ipush(ixget(p, k, a[k], 1), f);
    if (QT == QCAP) { QCAP = QCAP ? QCAP * 2 : 4096; QUEUE = xrealloc(QUEUE, QCAP * sizeof(int)); }
    QUEUE[QT++] = f;
}

/* ---------------- firing and joining */
typedef struct { int r; int *bind; int *prem; int np; } pend;   /* rule instances with unsafe head variables */
static pend *PEND; static int NPEND, CPEND;

static void fire_unsafe_rec(int r, int *bind, const int *prem, int np, int vi, int used_new, int from) {
    rule *ru = &R[r];
    while (vi < ru->nvars && !(ru->unsafe[vi] && bind[vi] == INT32_MIN)) vi++;
    if (vi == ru->nvars) {
        if (from >= 0 && !used_new) return;
        int a[64]; for (int k = 0; k < ru->head.ar; k++) { int t = ru->head.args[k]; a[k] = t >= 0 ? t : bind[-t - 1]; }
        insert_fact(ru->head.pred, a, ru->head.ar, r, prem, np); return;
    }
    for (int c = 0; c < CONSTS.n; c++) {
        bind[vi] = CONSTS.a[c];
        fire_unsafe_rec(r, bind, prem, np, vi + 1, used_new || (from >= 0 && c >= from), from);
    }
    bind[vi] = INT32_MIN;
}

static void fire(int r, int *bind, const int *prem, int np) {
    rule *ru = &R[r];
    if (!ru->has_head) {
        if (REFUTED < 0) {
            REFUTED = r;
            if (NPREM + np > CPREM) { CPREM = (CPREM + np) * 2 + 1024; PREM = xrealloc(PREM, CPREM * sizeof(int)); }
            REF_POFF = (int)NPREM; memcpy(PREM + NPREM, prem, np * sizeof(int)); NPREM += np; REF_NP = np;
        }
        return;
    }
    int has_unsafe = 0;
    for (int v = 0; v < ru->nvars; v++) if (ru->unsafe[v]) has_unsafe = 1;
    if (has_unsafe) {
        if (NPEND == CPEND) { CPEND = CPEND ? CPEND * 2 : 64; PEND = xrealloc(PEND, CPEND * sizeof(pend)); }
        pend *pe = &PEND[NPEND++]; pe->r = r; pe->np = np;
        pe->bind = xmalloc(ru->nvars * sizeof(int)); memcpy(pe->bind, bind, ru->nvars * sizeof(int));
        pe->prem = xmalloc(np * sizeof(int)); memcpy(pe->prem, prem, np * sizeof(int));
        if (CONSTS.n == 0) { int c = intern("c0"); ipush(&CONSTS, c); }
        int b2[64]; memcpy(b2, bind, ru->nvars * sizeof(int));
        fire_unsafe_rec(r, b2, prem, np, 0, 0, -1);
        return;
    }
    int a[64]; for (int k = 0; k < ru->head.ar; k++) { int t = ru->head.args[k]; a[k] = t >= 0 ? t : bind[-t - 1]; }
    insert_fact(ru->head.pred, a, ru->head.ar, r, prem, np);
}

static int match(const atom *at, int f, int *bind, int *undo, int *nu) {
    const int *v = ARGS + F[f].off;
    for (int k = 0; k < at->ar; k++) {
        int t = at->args[k];
        if (t >= 0) { if (v[k] != t) return 0; }
        else { int x = -t - 1; if (bind[x] == INT32_MIN) { bind[x] = v[k]; undo[(*nu)++] = x; } else if (bind[x] != v[k]) return 0; }
    }
    return 1;
}
/* An argument position is indexed only once some join looks a fact up by it; then every fact of
   that predicate so far is indexed in one pass and later ones as they arrive. Positions no join
   ever binds cost nothing. */
static void build_ix(int p, int k) {
    long i = (long)p * 64 + k;
    if (i >= NIXON) { long nn = (i + 1) * 2; IXON = xrealloc(IXON, nn); memset(IXON + NIXON, 0, nn - NIXON); NIXON = (int)nn; }
    IXON[i] = 1;
    ivec *all = ixget(p, 255, 0, 0);
    if (!all) return;
    int n = all->n;
    for (int j = 0; j < n; j++) { int f = ixget(p, 255, 0, 0)->a[j]; ipush(ixget(p, k, ARGS[F[f].off + k], 1), f); }
}
static ivec *cands(const atom *at, const int *bind, int *count) {
    ivec *best = NULL; int bn = -1;
    for (int k = 0; k < at->ar; k++) {
        int t = at->args[k]; int val = t >= 0 ? t : bind[-t - 1];
        if (val == INT32_MIN) continue;
        if (!ixon(at->pred, k)) build_ix(at->pred, k);
        ivec *v = ixget(at->pred, k, val, 0);
        int n = v ? v->n : 0;
        if (bn < 0 || n < bn) { best = v; bn = n; if (n == 0) break; }
    }
    if (bn < 0) { best = ixget(at->pred, 255, 0, 0); bn = best ? best->n : 0; }
    *count = bn; return best;
}
static void join(int r, char *done, int left, int *bind, int *prem, int np) {
    if (REFUTED >= 0) return;
    rule *ru = &R[r];
    if (left == 0) { fire(r, bind, prem, np); return; }
    int bi = -1, bc = 0; ivec *bv = NULL;
    for (int i = 0; i < ru->nb; i++) if (!done[i]) {
        int c; ivec *v = cands(&ru->body[i], bind, &c);
        if (bi < 0 || c < bc) { bi = i; bc = c; bv = v; if (c == 0) break; }
    }
    if (bc == 0) return;
    done[bi] = 1;
    int n = bv->n; atom *at = &ru->body[bi];
    /* the candidate vector may grow (and move) while we recurse: re-read it by key each step */
    for (int j = 0; j < n && REFUTED < 0; j++) {
        int c2; ivec *v2 = cands(at, bind, &c2); int f = v2->a[j];
        OPS++;
        int undo[64], nu = 0;
        if (match(at, f, bind, undo, &nu)) { prem[np] = f; join(r, done, left - 1, bind, prem, np + 1); }
        for (int u = 0; u < nu; u++) bind[undo[u]] = INT32_MIN;
    }
    done[bi] = 0;
}
static void join_with_fact(int r, int pos, int f) {
    rule *ru = &R[r]; int bind[64]; char done[64] = {0}; int prem[64]; int undo[64], nu = 0;
    for (int v = 0; v < ru->nvars; v++) bind[v] = INT32_MIN;
    if (!match(&ru->body[pos], f, bind, undo, &nu)) return;
    done[pos] = 1; prem[0] = f; OPS++;
    join(r, done, ru->nb - 1, bind, prem, 1);
}
static void run_queue(void) {
    while (QH < QT && REFUTED < 0) {
        int f = QUEUE[QH++]; int p = F[f].pred;
        if (p >= NBYP) continue;
        for (int i = 0; i < BYP[p].n && REFUTED < 0; i++) { int x = BYP[p].a[i]; join_with_fact(x >> 8, x & 255, f); }
    }
}

/* ---------------- TPTP parsing */
typedef struct { char *s; int kind; } tok;  /* kind: 1 word, 2 punct, 3 quoted */
static tok *TK; static int NT, CT, TI;
static char *readfile(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) { fprintf(stderr, "horn: cannot open %s\n", path); exit(3); }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = xmalloc(n + 1); if (fread(b, 1, n, f) != (size_t)n) die("read"); b[n] = 0; fclose(f); return b;
}
static void addtok(const char *s, int len, int kind) {
    if (NT == CT) { CT = CT ? CT * 2 : 1024; TK = xrealloc(TK, CT * sizeof(tok)); }
    TK[NT].s = xmalloc(len + 1); memcpy(TK[NT].s, s, len); TK[NT].s[len] = 0; TK[NT].kind = kind; NT++;
}
static void tokenize(const char *b) {
    const char *p = b;
    while (*p) {
        if (isspace((unsigned char)*p)) { p++; continue; }
        if (*p == '%') { while (*p && *p != '\n') p++; continue; }
        if (p[0] == '/' && p[1] == '*') { p += 2; while (*p && !(p[0] == '*' && p[1] == '/')) p++; if (*p) p += 2; continue; }
        if (*p == '\'' || *p == '"') { char q = *p; const char *s = p++; while (*p && *p != q) { if (*p == '\\' && p[1]) p++; p++; } if (*p) p++; addtok(s, (int)(p - s), 3); continue; }
        if (isalnum((unsigned char)*p) || *p == '_' || *p == '$') { const char *s = p; while (isalnum((unsigned char)*p) || *p == '_' || *p == '$') p++; addtok(s, (int)(p - s), 1); continue; }
        if (p[0] == '!' && p[1] == '=') { addtok(p, 2, 2); p += 2; continue; }
        addtok(p, 1, 2); p++;
    }
}
static int is_var_s(const char *s) { return isupper((unsigned char)s[0]) || s[0] == '_'; }
static int OUT_OF_CLASS; static const char *WHY;
static int eat(const char *t) { if (TI < NT && !strcmp(TK[TI].s, t)) { TI++; return 1; } return 0; }
static void expect(const char *t) { if (!eat(t)) { fprintf(stderr, "horn: expected %s near token %d (%s)\n", t, TI, TI < NT ? TK[TI].s : "EOF"); exit(3); } }

/* clause under construction */
typedef struct { int neg; int pred; ivec args; } lit;
static lit *LITS; static int NL, CL;
static char *VARNAMES[64]; static int NV;
static int var_id(const char *s) { for (int i = 0; i < NV; i++) if (!strcmp(VARNAMES[i], s)) return i; if (NV == 64) die("clause has more than 64 variables"); VARNAMES[NV] = strdup(s); return NV++; }
static void ground_term(char *buf, size_t cap, size_t *len) {   /* appends a term; returns via buf; marks out of class on a variable */
    const char *nm = TK[TI++].s;
    if (is_var_s(nm)) { OUT_OF_CLASS = 1; WHY = "function symbol over a variable"; }
    size_t l = strlen(nm); if (*len + l + 2 >= cap) die("term too long"); memcpy(buf + *len, nm, l); *len += l;
    if (eat("(")) {
        buf[(*len)++] = '(';
        for (;;) { ground_term(buf, cap, len); if (eat(",")) { buf[(*len)++] = ','; continue; } expect(")"); break; }
        buf[(*len)++] = ')';
    }
    buf[*len] = 0;
}
static int term(void) {
    const char *nm = TK[TI].s;
    if (TI + 1 < NT && !strcmp(TK[TI + 1].s, "(")) { static char buf[1 << 16]; size_t len = 0; ground_term(buf, sizeof buf, &len); return intern(buf); }
    TI++;
    if (is_var_s(nm)) return -(var_id(nm) + 1);
    return intern(nm);
}
static void literal(void) {
    int neg = 0; if (eat("~")) neg = 1;
    if (!strcmp(TK[TI].s, "(")) { OUT_OF_CLASS = 1; WHY = "nested literal"; TI++; return; }
    const char *nm = TK[TI++].s;
    if (NL == CL) { CL = CL ? CL * 2 : 16; LITS = xrealloc(LITS, CL * sizeof(lit)); }
    lit *l = &LITS[NL++]; l->neg = neg; l->pred = intern(nm); l->args.n = l->args.cap = 0; l->args.a = NULL;
    if (eat("(")) { for (;;) { ipush(&l->args, term()); if (eat(",")) continue; expect(")"); break; } }
    if (TI < NT && (!strcmp(TK[TI].s, "=") || !strcmp(TK[TI].s, "!="))) { OUT_OF_CLASS = 1; WHY = "equality"; }
}

static int known_consts_n;
static int EACH; static long NCLAUSES;   /* --each: answer after every appended clause */
static void add_rule_from_lits(int name) {
    int npos = 0, hi = -1;
    for (int i = 0; i < NL; i++) if (!LITS[i].neg) { npos++; hi = i; }
    if (npos > 1) { OUT_OF_CLASS = 1; WHY = "non-Horn clause"; return; }
    if (NR == CR) { CR = CR ? CR * 2 : 64; R = xrealloc(R, CR * sizeof(rule)); }
    rule *ru = &R[NR]; memset(ru, 0, sizeof *ru); ru->name = name; ru->nvars = NV;
    ru->body = xmalloc((NL) * sizeof(atom));
    for (int i = 0; i < NL; i++) {
        atom a = { LITS[i].pred, LITS[i].args.n, xmalloc(LITS[i].args.n * sizeof(int) + 1) };
        memcpy(a.args, LITS[i].args.a, a.ar * sizeof(int));
        while (a.pred >= NPAR) { PAR = xrealloc(PAR, (NPAR + 1) * sizeof(int)); PAR[NPAR++] = -1; }
        if (PAR[a.pred] >= 0 && PAR[a.pred] != a.ar) { OUT_OF_CLASS = 1; WHY = "predicate used with two arities"; return; }
        PAR[a.pred] = a.ar;
        for (int k = 0; k < a.ar; k++) if (a.args[k] >= 0) {
            int c = a.args[k];
            while (c >= NISC) { ISCONST = xrealloc(ISCONST, NISC + 1); ISCONST[NISC++] = 0; }
            if (!ISCONST[c]) { ISCONST[c] = 1; ipush(&CONSTS, c); }
        }
        if (i == hi) { ru->has_head = 1; ru->head = a; } else ru->body[ru->nb++] = a;
    }
    ru->unsafe = xmalloc(NV + 1);
    for (int v = 0; v < NV; v++) {
        int inb = 0; for (int i = 0; i < ru->nb; i++) for (int k = 0; k < ru->body[i].ar; k++) if (ru->body[i].args[k] == -(v + 1)) inb = 1;
        ru->unsafe[v] = ru->has_head && !inb;
        if (!ru->has_head && !inb) ru->unsafe[v] = 0;
    }
    int r = NR++;
    for (int i = 0; i < ru->nb; i++) {
        int p = ru->body[i].pred;
        while (p >= NBYP) { BYP = xrealloc(BYP, (NBYP + 1) * sizeof(ivec)); memset(&BYP[NBYP++], 0, sizeof(ivec)); }
        ipush(&BYP[p], r * 256 + i);
    }
    int from = known_consts_n; int grew = CONSTS.n > known_consts_n; known_consts_n = CONSTS.n;
    if (ru->nb == 0) { int bind[64]; for (int v = 0; v < NV; v++) bind[v] = INT32_MIN; fire(r, bind, NULL, 0); }
    else { int bind[64]; char done[64] = {0}; int prem[64]; for (int v = 0; v < NV; v++) bind[v] = INT32_MIN; join(r, done, ru->nb, bind, prem, 0); }
    if (grew) {   /* new constants widen every unsafe head variable seen before */
        int np0 = NPEND;
        for (int i = 0; i < np0; i++) if (PEND[i].r != r) {
            int b2[64]; memcpy(b2, PEND[i].bind, R[PEND[i].r].nvars * sizeof(int));
            fire_unsafe_rec(PEND[i].r, b2, PEND[i].prem, PEND[i].np, 0, 0, from);
        }
    }
    /* With --each the clauses so far must be decided before the next one arrives, so the log is
       saturated now. Otherwise saturation waits until every clause is in: saturating each prefix
       would explore the closure of the first few rules alone (on a Rubik's cube problem, the
       subgroup the first four moves generate) before the rules that reach the goal arrive. */
    if (EACH) run_queue();
}

static void parse_file(const char *path, const char *root, char **sel, int nsel);
static void parse_tokens(const char *root, char **sel, int nsel) {
    while (TI < NT && (REFUTED < 0 || EACH) && !OUT_OF_CLASS) {
        const char *kw = TK[TI++].s;
        if (!strcmp(kw, "include")) {
            expect("("); char *f = TK[TI++].s; char fn[4096]; size_t l = strlen(f);
            snprintf(fn, sizeof fn, "%s/%.*s", root, (int)(l - 2), f + 1);
            char *subsel[4096]; int ns = 0, has = 0;
            if (eat(",")) { expect("["); has = 1; while (!eat("]")) { if (strcmp(TK[TI].s, ",")) subsel[ns++] = TK[TI].s; TI++; } }
            expect(")"); expect(".");
            tok *sTK = TK; int sNT = NT, sCT = CT, sTI = TI;
            TK = NULL; NT = CT = TI = 0;
            parse_file(fn, root, has ? subsel : NULL, has ? ns : -1);
            TK = sTK; NT = sNT; CT = sCT; TI = sTI;
            continue;
        }
        if (strcmp(kw, "cnf")) { OUT_OF_CLASS = 1; WHY = "non-CNF formula"; return; }
        expect("("); const char *name = TK[TI++].s; expect(","); TI++; expect(",");
        NL = 0; for (int i = 0; i < NV; i++) free(VARNAMES[i]); NV = 0;
        int depth = 0;
        for (;;) {
            const char *t = TK[TI].s;
            if (!strcmp(t, "(")) { depth++; TI++; continue; }
            if (!strcmp(t, ")") && depth > 0) { depth--; TI++; continue; }
            if (!strcmp(t, "|")) { TI++; continue; }
            if (!strcmp(t, ")") || !strcmp(t, ",")) break;
            literal();
            if (OUT_OF_CLASS) return;
        }
        while (strcmp(TK[TI].s, ".")) TI++;
        TI++;
        int keep = 1;
        if (nsel >= 0) { keep = 0; for (int i = 0; i < nsel; i++) if (!strcmp(sel[i], name)) keep = 1; }
        /* $true makes the clause a tautology, $false is an empty disjunct */
        int taut = 0, w = 0;
        for (int i = 0; i < NL; i++) {
            const char *pn = SY.s[LITS[i].pred];
            if (!strcmp(pn, "$true")) { if (!LITS[i].neg) taut = 1; continue; }
            if (!strcmp(pn, "$false")) { if (LITS[i].neg) taut = 1; continue; }
            LITS[w++] = LITS[i];
        }
        NL = w;
        if (keep && !taut) add_rule_from_lits(intern(name));
        if (keep && EACH) { NCLAUSES++; printf("%% after %ld %s ops %ld facts %d\n", NCLAUSES, REFUTED >= 0 ? "Unsatisfiable" : "Satisfiable", OPS, NF); }
    }
}
static void parse_file(const char *path, const char *root, char **sel, int nsel) {
    char *b = readfile(path); tokenize(b); free(b);
    parse_tokens(root, sel, nsel);
}

/* ---------------- proof output */
static void put_json_str(FILE *o, const char *s) { fputc('"', o); for (; *s; s++) { if (*s == '"' || *s == '\\') fputc('\\', o); fputc(*s, o); } fputc('"', o); }
static void put_fact(FILE *o, int f) {
    fputc('[', o); put_json_str(o, SY.s[F[f].pred]); fputs(",[", o);
    for (int k = 0; k < arity(F[f].pred); k++) { if (k) fputc(',', o); put_json_str(o, SY.s[ARGS[F[f].off + k]]); }
    fputs("]]", o);
}
static long proof_steps(int *order_out) {   /* iterative post-order over the derivation DAG */
    char *seen = calloc(NF + 1, 1); long n = 0;
    int *st = xmalloc((NF + REF_NP + 4) * 2 * sizeof(int)); long sp = 0;
    for (int i = REF_NP - 1; i >= 0; i--) { st[sp++] = PREM[REF_POFF + i]; st[sp++] = 0; }
    while (sp) {
        int done = st[--sp], f = st[--sp];
        if (done) { if (order_out) order_out[n] = f; n++; continue; }
        if (seen[f]) continue;
        seen[f] = 1; st[sp++] = f; st[sp++] = 1;
        for (int i = F[f].np - 1; i >= 0; i--) { int q = PREM[F[f].poff + i]; if (!seen[q]) { st[sp++] = q; st[sp++] = 0; } }
    }
    free(st); free(seen); return n + 1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: horn PROBLEM.p [--root DIR] [--proof-json FILE]\n"); return 2; }
    const char *path = argv[1], *root = ".", *pj = NULL;
    for (int i = 2; i < argc; i++) { if (!strcmp(argv[i], "--root") && i + 1 < argc) root = argv[++i]; else if (!strcmp(argv[i], "--proof-json") && i + 1 < argc) pj = argv[++i]; else if (!strcmp(argv[i], "--each")) EACH = 1; }
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    parse_file(path, root, NULL, -1);
    if (!OUT_OF_CLASS) run_queue();
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    const char *base = strrchr(path, '/'); base = base ? base + 1 : path;
    if (OUT_OF_CLASS) { printf("%% SZS status GaveUp for %s\n%% reason %s\n", base, WHY); return 0; }
    long ps = 0;
    if (REFUTED >= 0) {
        printf("%% SZS status Unsatisfiable for %s\n", base);
        int *order = xmalloc((NF + 1) * sizeof(int));
        ps = proof_steps(order);
        if (pj) {
            FILE *o = fopen(pj, "w"); if (!o) die("cannot write proof");
            fputc('[', o);
            for (long i = 0; i < ps - 1; i++) {
                int f = order[i]; if (i) fputc(',', o);
                fputc('[', o); put_fact(o, f); fputc(',', o); put_json_str(o, SY.s[R[F[f].rule].name]); fputs(",[", o);
                for (int k = 0; k < F[f].np; k++) { if (k) fputc(',', o); put_fact(o, PREM[F[f].poff + k]); }
                fputs("]]", o);
            }
            if (ps > 1) fputc(',', o);
            fputs("[[\"$false\",[]],", o); put_json_str(o, SY.s[R[REFUTED].name]); fputs(",[", o);
            for (int k = 0; k < REF_NP; k++) { if (k) fputc(',', o); put_fact(o, PREM[REF_POFF + k]); }
            fputs("]]]\n", o); fclose(o);
        }
    } else printf("%% SZS status Satisfiable for %s\n", base);
    printf("%% secs %.4f ops %ld facts %d proof_steps %ld\n", secs, OPS, NF, ps);
    return 0;
}
