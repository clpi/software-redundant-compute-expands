/* hyper: positive unit hyperresolution for Horn CNF with function symbols and no equality.

   Every derived clause is a positive unit (an atom, possibly with variables). A given-clause loop
   picks units by weight with an age turn every few picks; a picked unit becomes active and is
   resolved against every body literal of every rule, the other body literals taking active units.
   New units are dropped when an existing unit subsumes them, and they remove the existing units
   they subsume. A rule without a head (a negated conjecture) that fires is a refutation.
   Positive hyperresolution is refutation complete for Horn clauses, and the loop is fair, so on an
   unsatisfiable input it finds a refutation given time; it never answers Satisfiable.

   Terms are hash-consed. Unification is structure sharing over banks (one per clause copy) with an
   occurs check. Discrimination trees give candidate units for subsumption and unification.

   Usage: hyper PROBLEM.p [--root DIR] [--limit SECONDS] [--proof-json FILE]
   Prints "% SZS status Unsatisfiable|GaveUp|Timeout for NAME", then counts. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <ctype.h>

static void die(const char *m) { fprintf(stderr, "hyper: %s\n", m); exit(2); }
static void *xmalloc(size_t n) { void *p = malloc(n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xrealloc(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }

/* ---------------- symbols */
typedef struct { char *name; int arity; } sym;
static sym *SY; static int NSY, CSY;
static int *SYH; static int SYHC;
static uint64_t hstr(const char *s, int a) { uint64_t h = 1469598103934665603ULL ^ (uint64_t)a; while (*s) h = (h ^ (unsigned char)*s++) * 1099511628211ULL; return h; }
static int sym_of(const char *s, int a) {
    if (!SYHC) { SYHC = 1024; SYH = xmalloc(SYHC * sizeof(int)); for (int i = 0; i < SYHC; i++) SYH[i] = -1; }
    uint64_t h = hstr(s, a) & (SYHC - 1);
    while (SYH[h] >= 0) { sym *y = &SY[SYH[h]]; if (y->arity == a && !strcmp(y->name, s)) return SYH[h]; h = (h + 1) & (SYHC - 1); }
    if (NSY == CSY) { CSY = CSY ? CSY * 2 : 256; SY = xrealloc(SY, CSY * sizeof(sym)); }
    SY[NSY].name = strdup(s); SY[NSY].arity = a; SYH[h] = NSY;
    if ((NSY + 1) * 2 > SYHC) {
        int nc = SYHC * 2; int *nt = xmalloc(nc * sizeof(int)); for (int i = 0; i < nc; i++) nt[i] = -1;
        for (int i = 0; i <= NSY; i++) { uint64_t g = hstr(SY[i].name, SY[i].arity) & (nc - 1); while (nt[g] >= 0) g = (g + 1) & (nc - 1); nt[g] = i; }
        free(SYH); SYH = nt; SYHC = nc;
    }
    return NSY++;
}

/* ---------------- hash-consed terms: f >= 0 a symbol, f < 0 the variable -f-1 */
typedef struct { int f, n, a0, w, gr, vo; } term;   /* vo = variable occurrences */   /* args in AR[a0 .. a0+n), w = symbol count, gr = ground */
static term *T; static int NT, CT;
static int *AR; static long NAR, CAR;
static int *TH; static long THC, THN;
static uint64_t hterm(int f, int n, const int *a) { uint64_t h = (uint64_t)(f + 7) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < n; i++) h = (h ^ (uint64_t)(unsigned)a[i]) * 1099511628211ULL; return h; }
static int mk(int f, int n, const int *a) {
    if (!THC) { THC = 1 << 16; TH = xmalloc(THC * sizeof(int)); for (long i = 0; i < THC; i++) TH[i] = -1; }
    uint64_t h = hterm(f, n, a) & (THC - 1);
    while (TH[h] >= 0) { term *t = &T[TH[h]]; if (t->f == f && t->n == n && !memcmp(AR + t->a0, a, n * sizeof(int))) return TH[h]; h = (h + 1) & (THC - 1); }
    if (NT == CT) { CT = CT ? CT * 2 : 1 << 16; T = xrealloc(T, CT * sizeof(term)); }
    if (NAR + n > CAR) { while (NAR + n > CAR) CAR = CAR ? CAR * 2 : 1 << 16; AR = xrealloc(AR, CAR * sizeof(int)); }
    int id = NT++; T[id].f = f; T[id].n = n; T[id].a0 = (int)NAR; memcpy(AR + NAR, a, n * sizeof(int)); NAR += n;
    int w = 1, gr = f >= 0, vo = f < 0; for (int i = 0; i < n; i++) { w += T[a[i]].w; gr &= T[a[i]].gr; vo += T[a[i]].vo; } T[id].w = w; T[id].gr = gr; T[id].vo = vo;
    TH[h] = id; THN++;
    if (THN * 2 > THC) {
        long nc = THC * 2; int *nt = xmalloc(nc * sizeof(int)); for (long i = 0; i < nc; i++) nt[i] = -1;
        for (int i = 0; i < NT; i++) { uint64_t g = hterm(T[i].f, T[i].n, AR + T[i].a0) & (nc - 1); while (nt[g] >= 0) g = (g + 1) & (nc - 1); nt[g] = i; }
        free(TH); TH = nt; THC = nc;
    }
    return id;
}
static int mkvar(int v) { return mk(-v - 1, 0, NULL); }
#define ISVAR(t) (T[t].f < 0)
#define VNO(t) (-T[t].f - 1)
#define ARG(t, i) (AR[T[t].a0 + (i)])

/* ---------------- banks: bindings for clause copies */
#define MAXV 256
#define MAXB 66
static int BT[MAXB][MAXV], BB[MAXB][MAXV];   /* BT = bound term or -1, BB = its bank */
static int TRB[1 << 16], TRV[1 << 16]; static int NTR;
static void bind(int b, int v, int t, int tb) { BT[b][v] = t; BB[b][v] = tb; TRB[NTR] = b; TRV[NTR] = v; NTR++; if (NTR >= (1 << 16)) die("trail overflow"); }
static void undo_to(int m) { while (NTR > m) { NTR--; BT[TRB[NTR]][TRV[NTR]] = -1; } }
static inline void deref(int *t, int *b) { while (ISVAR(*t)) { int v = VNO(*t); if (v >= MAXV) die("too many variables"); int u = BT[*b][v]; if (u < 0) return; *b = BB[*b][v]; *t = u; } }
static int occurs(int v, int vb, int t, int b) {
    deref(&t, &b);
    if (ISVAR(t)) return VNO(t) == v && b == vb;
    for (int i = 0; i < T[t].n; i++) if (occurs(v, vb, ARG(t, i), b)) return 1;
    return 0;
}
static int unify(int s, int sb, int t, int tb) {
    deref(&s, &sb); deref(&t, &tb);
    if (s == t && (sb == tb || T[s].gr)) return 1;
    if (ISVAR(s)) { if (ISVAR(t) && VNO(s) == VNO(t) && sb == tb) return 1; if (occurs(VNO(s), sb, t, tb)) return 0; bind(sb, VNO(s), t, tb); return 1; }
    if (ISVAR(t)) { if (occurs(VNO(t), tb, s, sb)) return 0; bind(tb, VNO(t), s, sb); return 1; }
    if (T[s].f != T[t].f || T[s].n != T[t].n) return 0;
    for (int i = 0; i < T[s].n; i++) if (!unify(ARG(s, i), sb, ARG(t, i), tb)) return 0;
    return 1;
}
/* one-way match: variables of general g (bank MB) may bind; specific s is taken literally (and read in MATCH_BANK) */
static int MATCH_BANK = 0;
#define MB (MAXB - 1)
static int match(int g, int s) {
    if (ISVAR(g)) { int v = VNO(g); if (BT[MB][v] >= 0) return BT[MB][v] == s; bind(MB, v, s, MATCH_BANK); return 1; }
    if (g == s && T[g].gr) return 1;
    if (ISVAR(s) || T[g].f != T[s].f || T[g].n != T[s].n) return 0;
    for (int i = 0; i < T[g].n; i++) if (!match(ARG(g, i), ARG(s, i))) return 0;
    return 1;
}
/* instantiate under bindings, renaming variables to 0.. in order of first occurrence */
static int RMB[1 << 14], RMV[1 << 14], RMN;
static int inst_rec(int t, int b) {
    deref(&t, &b);
    if (ISVAR(t)) { int v = VNO(t); for (int i = 0; i < RMN; i++) if (RMB[i] == b && RMV[i] == v) return mkvar(i); if (RMN >= MAXV) die("too many variables in a unit"); RMB[RMN] = b; RMV[RMN] = v; return mkvar(RMN++); }
    if (!T[t].n) return t;
    int a[64]; if (T[t].n > 64) die("arity above 64");
    for (int i = 0; i < T[t].n; i++) a[i] = inst_rec(ARG(t, i), b);
    return mk(T[t].f, T[t].n, a);
}
static int inst(int t, int b, int *nv) { RMN = 0; int r = inst_rec(t, b); if (nv) *nv = RMN; return r; }


/* ---------------- discrimination trees: preorder symbol strings, a variable stored as STAR */
#define STAR (-1)
#define QVAR (-3)
typedef struct { int sym, parent, child, sib; int *ent; int nent, cent; } dnode;
typedef struct { dnode *N; int nn, cn; int *H; long HC, HN; } dtree;
static void dt_init(dtree *d) {
    d->cn = 1024; d->N = xmalloc(d->cn * sizeof(dnode)); d->nn = 1;
    d->N[0] = (dnode){ -2, -1, -1, -1, NULL, 0, 0 };
    d->HC = 4096; d->H = xmalloc(d->HC * sizeof(int)); for (long i = 0; i < d->HC; i++) d->H[i] = -1; d->HN = 0;
}
static uint64_t dh(int p, int s) { return ((uint64_t)(unsigned)p * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)(unsigned)(s + 3) * 0xC2B2AE3D27D4EB4FULL); }
static int dt_get(dtree *d, int p, int s) {
    uint64_t h = dh(p, s) & (d->HC - 1);
    while (d->H[h] >= 0) { int c = d->H[h]; if (d->N[c].parent == p && d->N[c].sym == s) return c; h = (h + 1) & (d->HC - 1); }
    return -1;
}
static int dt_add(dtree *d, int p, int s) {
    if (d->nn == d->cn) { d->cn *= 2; d->N = xrealloc(d->N, d->cn * sizeof(dnode)); }
    int c = d->nn++; d->N[c] = (dnode){ s, p, -1, d->N[p].child, NULL, 0, 0 }; d->N[p].child = c;
    if ((d->HN + 1) * 2 > d->HC) {
        long nc = d->HC * 2; int *nt = xmalloc(nc * sizeof(int)); for (long i = 0; i < nc; i++) nt[i] = -1;
        for (int i = 1; i < d->nn; i++) { uint64_t g = dh(d->N[i].parent, d->N[i].sym) & (nc - 1); while (nt[g] >= 0) g = (g + 1) & (nc - 1); nt[g] = i; }
        free(d->H); d->H = nt; d->HC = nc; d->HN = d->nn - 1;
    } else {
        uint64_t h = dh(p, s) & (d->HC - 1); while (d->H[h] >= 0) h = (h + 1) & (d->HC - 1); d->H[h] = c; d->HN++;
    }
    return c;
}
static void dt_insert_rec(dtree *d, int *node, int t) {
    int s = ISVAR(t) ? STAR : T[t].f;
    int c = dt_get(d, *node, s); if (c < 0) c = dt_add(d, *node, s); *node = c;
    if (!ISVAR(t)) for (int i = 0; i < T[t].n; i++) dt_insert_rec(d, node, ARG(t, i));
}
static void dt_insert(dtree *d, int t, int e) {
    int node = 0; dt_insert_rec(d, &node, t);
    dnode *n = &d->N[node]; if (n->nent == n->cent) { n->cent = n->cent ? n->cent * 2 : 2; n->ent = xrealloc(n->ent, n->cent * sizeof(int)); }
    n->ent[n->nent++] = e;
}
/* the query, flattened */
static int QS[1 << 16], QE[1 << 16], QN;
static int flat_rec(int t) {
    int i = QN++; if (QN >= (1 << 16)) die("query too large");
    if (ISVAR(t)) QS[i] = QVAR; else { QS[i] = T[t].f; for (int k = 0; k < T[t].n; k++) flat_rec(ARG(t, k)); }
    QE[i] = QN; return i;
}
static void flatten(int t) { QN = 0; flat_rec(t); }
/* the query is a term under bindings: flatten through them, without building it */
static int flat_rec_b(int t, int b) {
    deref(&t, &b);
    int i = QN++; if (QN >= (1 << 16)) die("query too large");
    if (ISVAR(t)) QS[i] = QVAR; else { QS[i] = T[t].f; for (int k = 0; k < T[t].n; k++) flat_rec_b(ARG(t, k), b); }
    QE[i] = QN; return i;
}
static void flatten_b(int t, int b) { QN = 0; flat_rec_b(t, b); }
static int *CAND; static long NCAND, CCAND;
static void take(dnode *n) { if (NCAND + n->nent > CCAND) { while (NCAND + n->nent > CCAND) CCAND = CCAND ? CCAND * 2 : 1024; CAND = xrealloc(CAND, CCAND * sizeof(int)); } memcpy(CAND + NCAND, n->ent, n->nent * sizeof(int)); NCAND += n->nent; }
static int sym_arity(int s) { return s == STAR ? 0 : SY[s].arity; }
/* generalizations of the query: stored terms that may match onto it */
static void dt_gen(dtree *d, int node, int i) {
    if (i == QN) { take(&d->N[node]); return; }
    int c = dt_get(d, node, STAR); if (c >= 0) dt_gen(d, c, QE[i]);
    if (QS[i] >= 0) { c = dt_get(d, node, QS[i]); if (c >= 0) dt_gen(d, c, i + 1); }
}
static void dt_inst(dtree *d, int node, int i);
static void dt_unif(dtree *d, int node, int i);
/* skip k stored subterms below node, then continue the query at position i in mode m */
static void dt_skip(dtree *d, int node, int k, int i, int m) {
    if (k == 0) { if (m) dt_unif(d, node, i); else dt_inst(d, node, i); return; }
    for (int c = d->N[node].child; c >= 0; c = d->N[c].sib) dt_skip(d, c, k - 1 + sym_arity(d->N[c].sym), i, m);
}
/* instances of the query */
static void dt_inst(dtree *d, int node, int i) {
    if (i == QN) { take(&d->N[node]); return; }
    if (QS[i] == QVAR) { dt_skip(d, node, 1, QE[i], 0); return; }
    int c = dt_get(d, node, QS[i]); if (c >= 0) dt_inst(d, c, i + 1);
}
/* terms that may unify with the query */
static void dt_unif(dtree *d, int node, int i) {
    if (i == QN) { take(&d->N[node]); return; }
    if (QS[i] == QVAR) { dt_skip(d, node, 1, QE[i], 1); return; }
    int c = dt_get(d, node, STAR); if (c >= 0) dt_unif(d, c, QE[i]);
    c = dt_get(d, node, QS[i]); if (c >= 0) dt_unif(d, c, i + 1);
}

/* ---------------- clauses and units */
typedef struct { int head, nb, *body, nv, name, orig, guard; } rule;   /* orig: problem clause, -1 for a magic rule; guard: body[0] is the magic literal */
static rule *R; static int NR, CR;
typedef struct { int atom, rule, np, par0, w; long age; char st; } unit;   /* st: 0 passive, 1 active, 2 dead */
static unit *U; static int NU, CU;
static int *PAR; static long NPAR, CPAR;
static dtree KEPT, ACT;
static int OUT_OF_CLASS, MAGIC, RES, SINGLE, MAXW, DROPPED, EQ = -1, HAS_EQ, SCHED_RATIO = 5, SELMODE;   /* DROPPED: the weight bound discarded a clause, so saturation proves nothing */ static const char *WHY = "";

/* ---------------- TPTP CNF reader with nested terms */
typedef struct { char *s; int kind; } tok;   /* kind: 'w' word, 'V' variable, 'q' quoted, 'p' punctuation */
static tok *TK; static int NTK, CTK, TI;
static void lex(const char *b) {
    NTK = 0; TI = 0;
    for (const char *p = b; *p;) {
        if (isspace((unsigned char)*p)) { p++; continue; }
        if (*p == '%') { while (*p && *p != '\n') p++; continue; }
        if (p[0] == '/' && p[1] == '*') { p += 2; while (*p && !(p[0] == '*' && p[1] == '/')) p++; if (*p) p += 2; continue; }
        const char *st = p; int kind;
        if (*p == '\'' || *p == '"') { char q = *p++; while (*p && *p != q) { if (*p == '\\' && p[1]) p++; p++; } if (*p) p++; kind = 'q'; }
        else if (isalnum((unsigned char)*p) || *p == '_' || *p == '$') { int up = isupper((unsigned char)*p) || *p == '_'; while (isalnum((unsigned char)*p) || *p == '_' || *p == '$') p++; kind = up ? 'V' : 'w'; }
        else if (p[0] == '!' && p[1] == '=') { p += 2; kind = 'p'; }
        else { p++; kind = 'p'; }
        if (NTK == CTK) { CTK = CTK ? CTK * 2 : 4096; TK = xrealloc(TK, CTK * sizeof(tok)); }
        TK[NTK].s = strndup(st, p - st); TK[NTK].kind = kind; NTK++;
    }
}
static int at(const char *s) { return TI < NTK && !strcmp(TK[TI].s, s); }
static void expect(const char *s) { if (!at(s)) { OUT_OF_CLASS = 1; WHY = "syntax"; } else TI++; }
static char *CVN[MAXV]; static int CNV;
static int term_p(void) {
    if (TI >= NTK) { OUT_OF_CLASS = 1; WHY = "syntax"; return mkvar(0); }
    tok *k = &TK[TI++];
    if (k->kind == 'V') {
        for (int i = 0; i < CNV; i++) if (!strcmp(CVN[i], k->s)) return mkvar(i);
        if (CNV == MAXV) die("clause has too many variables");
        CVN[CNV] = k->s; return mkvar(CNV++);
    }
    int a[64], n = 0;
    if (at("(")) { TI++; do { if (n == 64) die("arity above 64"); a[n++] = term_p(); } while (at(",") && ++TI); expect(")"); }
    return mk(sym_of(k->s, n), n, a);
}
static char *readall(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) return NULL;
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = xmalloc(n + 1); if (fread(b, 1, n, f) != (size_t)n) die("read"); b[n] = 0; fclose(f); return b;
}
static void parse_file(const char *path, const char *root, char **sel, int nsel);
static void parse_toks(const char *root, char **sel, int nsel) {
    while (TI < NTK && !OUT_OF_CLASS) {
        char *kw = TK[TI++].s;
        if (!strcmp(kw, "include")) {
            expect("("); char *fn = TK[TI++].s; char *sub[4096]; int ns = 0, has = 0;
            if (at(",")) { TI++; expect("["); has = 1; while (TI < NTK && !at("]")) { if (!at(",")) { if (ns < 4096) sub[ns++] = TK[TI].s; } TI++; } expect("]"); }
            expect(")"); expect(".");
            char name[4096]; size_t L = strlen(fn); snprintf(name, sizeof name, "%s/%.*s", root, (int)(L - 2), fn + 1);
            int savTI = TI, savN = NTK; tok *savT = TK; int savC = CTK; TK = NULL; NTK = CTK = 0;
            parse_file(name, root, has ? sub : NULL, has ? ns : -1);
            TK = savT; NTK = savN; CTK = savC; TI = savTI;
            continue;
        }
        if (strcmp(kw, "cnf")) { OUT_OF_CLASS = 1; WHY = "non-CNF formula"; return; }
        expect("("); char *name = TK[TI++].s; expect(","); TI++; expect(",");
        int keep = 1; if (nsel >= 0) { keep = 0; for (int i = 0; i < nsel; i++) if (!strcmp(sel[i], name)) keep = 1; }
        CNV = 0; int lits[1024], neg[1024], nl = 0, taut = 0, depth = 0;
        while (TI < NTK) {
            if (at("(")) { depth++; TI++; continue; }
            if (at(")")) { if (depth == 0) break; depth--; TI++; continue; }
            if (at("|")) { TI++; continue; }
            if (at(",")) break;
            int ng = 0; if (at("~")) { ng = 1; TI++; }
            int t = term_p();
            if (at("=") || at("!=")) {   /* an equation is the atom =(l, r); != negates it */
                int ne = at("!="); TI++; int t2 = term_p(); if (EQ < 0) EQ = sym_of("=", 2);
                int a2[2] = { t, t2 }; t = mk(EQ, 2, a2); if (ne) ng = !ng; HAS_EQ = 1;
            }
            const char *pn = SY[T[t].f].name;
            if (!strcmp(pn, "$true")) { if (!ng) taut = 1; continue; }
            if (!strcmp(pn, "$false")) { if (ng) taut = 1; continue; }
            if (nl == 1024) die("clause too long");
            lits[nl] = t; neg[nl] = ng; nl++;
        }
        int depth2 = 0; while (TI < NTK && !(at(".") && depth2 <= 0)) { if (at("(")) depth2++; if (at(")")) depth2--; TI++; }
        TI++;
        if (!keep || taut) continue;
        int npos = 0, head = -1; for (int i = 0; i < nl; i++) if (!neg[i]) { npos++; head = lits[i]; }
        if (npos > 1) { OUT_OF_CLASS = 1; WHY = "non-Horn clause"; return; }
        if (NR == CR) { CR = CR ? CR * 2 : 256; R = xrealloc(R, CR * sizeof(rule)); }
        rule *r = &R[NR++]; r->head = head; r->nb = nl - npos; r->body = xmalloc((r->nb + 1) * sizeof(int)); r->nv = CNV; r->name = sym_of(name, -1); r->orig = NR - 1; r->guard = 0;
        int k = 0; for (int i = 0; i < nl; i++) if (neg[i]) r->body[k++] = lits[i];
        if (r->nb + 1 >= MAXB - 3) { OUT_OF_CLASS = 1; WHY = "rule body too long"; return; }
    }
}
static void parse_file(const char *path, const char *root, char **sel, int nsel) {
    char *b = readall(path); if (!b) { OUT_OF_CLASS = 1; WHY = "cannot open an included file"; return; }
    lex(b); free(b); parse_toks(root, sel, nsel);
}

/* ---------------- magic sets: hyperresolution that only derives what the goal can use.
   Each rule H <- B1..Bn becomes H <- m(H), B1..Bn, with m(Bi) <- m(H), B1..B(i-1); a goal
   <- G1..Gm adds m(Gi) <- G1..G(i-1). The m predicates are fresh, so reading every m atom as true
   turns each new clause into a problem clause or a tautology: a refutation of the new set is a
   refutation of the problem. Arguments are kept whole, so m atoms are subgoals with variables and
   the loop runs as tabled top-down resolution. Proofs drop the m steps and m parents; a kept step
   is then an instance of what the problem clause gives, which the checker accepts. */
static int magic_of(int a) { int n = T[a].n; int args[64]; for (int i = 0; i < n; i++) args[i] = ARG(a, i); char nm[4096]; snprintf(nm, sizeof nm, "$m_%s", SY[T[a].f].name); return mk(sym_of(nm, n), n, args); }
static int is_magic(int a) { return !strncmp(SY[T[a].f].name, "$m_", 3); }
static void add_rule(int head, int nb, const int *body, int nv, int name, int orig, int guard) {
    if (NR == CR) { CR = CR ? CR * 2 : 256; R = xrealloc(R, CR * sizeof(rule)); }
    rule *r = &R[NR++]; r->head = head; r->nb = nb; r->body = xmalloc((nb + 1) * sizeof(int)); memcpy(r->body, body, nb * sizeof(int));
    r->nv = nv; r->name = name; r->orig = orig; r->guard = guard;
}
static void magic_transform(void) {
    int n0 = NR; rule *old = R; R = NULL; NR = CR = 0;
    for (int r = 0; r < n0; r++) {
        rule *o = &old[r]; int b[MAXB];
        if (o->nb == 0) { add_rule(o->head, 0, NULL, o->nv, o->name, r, 0); continue; }
        if (o->head >= 0) {
            b[0] = magic_of(o->head); memcpy(b + 1, o->body, o->nb * sizeof(int));
            add_rule(o->head, o->nb + 1, b, o->nv, o->name, r, 1);
            for (int i = 0; i < o->nb; i++) add_rule(magic_of(o->body[i]), i + 1, b, o->nv, o->name, -1, 0);
        } else {
            add_rule(-1, o->nb, o->body, o->nv, o->name, r, 0);
            for (int i = 0; i < o->nb; i++) add_rule(magic_of(o->body[i]), i, o->body, o->nv, o->name, -1, 0);
        }
    }
}

/* ---------------- given-clause loop */
static long AGE, KEPTN, GIVEN, GENERATED, SUBS_FWD, SUBS_BWD;
static int REF_RULE = -1, REF_PAR[MAXB];
static int *HW, *HA; static long NHW, NHA, CHW, CHA;   /* heaps by weight and by age */
static int lessw(int a, int b) { return U[a].w < U[b].w || (U[a].w == U[b].w && U[a].age < U[b].age); }
static int lessa(int a, int b) { return U[a].age < U[b].age; }
static void hpush(int **h, long *n, long *c, int x, int (*lt)(int, int)) {
    if (*n == *c) { *c = *c ? *c * 2 : 1024; *h = xrealloc(*h, *c * sizeof(int)); }
    long i = (*n)++; (*h)[i] = x;
    while (i > 0) { long p = (i - 1) / 2; if (!lt((*h)[i], (*h)[p])) break; int t = (*h)[i]; (*h)[i] = (*h)[p]; (*h)[p] = t; i = p; }
}
static int hpop(int *h, long *n, int (*lt)(int, int)) {
    if (!*n) return -1;
    int top = h[0]; h[0] = h[--(*n)]; long i = 0;
    for (;;) { long l = 2 * i + 1, r = l + 1, m = i; if (l < *n && lt(h[l], h[m])) m = l; if (r < *n && lt(h[r], h[m])) m = r; if (m == i) break; int t = h[i]; h[i] = h[m]; h[m] = t; i = m; }
    return top;
}
/* DISCOUNT loop: only active units simplify. A new unit is dropped if it is a variant of any kept
   unit (variants are one hash-consed term) or an active unit subsumes it; a picked unit is checked
   again, and retires the active units it subsumes, before it becomes active itself. */
static char *SEEN; static long CSEEN;
static int seen(int a) { if (a >= CSEEN) { long n = CSEEN ? CSEEN : 1 << 16; while (n <= a) n *= 2; SEEN = xrealloc(SEEN, n); memset(SEEN + CSEEN, 0, n - CSEEN); CSEEN = n; } return SEEN[a]; }
static int subsumed(int a) {   /* forward: a live active unit matches onto a */
    flatten(a); NCAND = 0; dt_gen(&ACT, 0, 0);
    for (long i = 0; i < NCAND; i++) { int c = CAND[i]; if (U[c].st == 2) continue; int m = NTR; int ok = match(U[c].atom, a); undo_to(m); if (ok) return 1; }
    return 0;
}
static int CH[MAXB];
static int add_unit(int a, int r, int np, const int *par) {
    if (NU == CU) { CU = CU ? CU * 2 : 4096; U = xrealloc(U, CU * sizeof(unit)); }
    int id = NU++; unit *u = &U[id]; u->atom = a; u->rule = r; u->np = np; u->par0 = (int)NPAR; u->w = T[a].w; u->age = AGE++; u->st = 0;
    if (NPAR + np > CPAR) { while (NPAR + np > CPAR) CPAR = CPAR ? CPAR * 2 : 4096; PAR = xrealloc(PAR, CPAR * sizeof(int)); }
    memcpy(PAR + NPAR, par, np * sizeof(int)); NPAR += np;
    seen(a); SEEN[a] = 1; KEPTN++;
    hpush(&HW, &NHW, &CHW, id, lessw); hpush(&HA, &NHA, &CHA, id, lessa);
    /* a one-literal goal that unifies refutes at once */
    for (int g = 0; g < NR && REF_RULE < 0; g++) if (R[g].head < 0 && R[g].nb == 1) {
        int m = NTR; if (unify(R[g].body[0], MAXB - 2, a, MAXB - 3)) { REF_RULE = g; REF_PAR[0] = id; } undo_to(m);   /* own banks: a rule's bindings may be live */
    }
    return id;
}
static int GU, GJ;
static double DEADLINE; static long TICK;
static void conclude(int r) {
    GENERATED++;
    rule *ru = &R[r];
    if (ru->head < 0) { REF_RULE = r; for (int k = 0; k < ru->nb; k++) REF_PAR[k] = CH[k]; return; }
    int a = inst(ru->head, 0, NULL);
    if (MAXW && T[a].w > MAXW) { DROPPED = 1; return; }   /* weight bound: incomplete, like Otter's max_weight */
    if (seen(a) || subsumed(a)) { SUBS_FWD++; return; }
    add_unit(a, r, ru->nb, CH);
}
static void extend(int r, int k) {
    if (REF_RULE >= 0) return;
    if ((++TICK & 1023) == 0 && now_s() > DEADLINE) return;
    rule *ru = &R[r];
    if (k == ru->nb) { conclude(r); return; }
    if (k == GJ) { extend(r, k + 1); return; }
    flatten_b(ru->body[k], 0); NCAND = 0; dt_unif(&ACT, 0, 0);
    long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
    for (long i = 0; i < n && REF_RULE < 0; i++) {
        int c = cs[i]; if (U[c].st != 1) continue; if (k < GJ && c == GU) continue;
        int m = NTR;
        if (unify(ru->body[k], 0, U[c].atom, k + 1)) { CH[k] = c; extend(r, k + 1); }
        undo_to(m);
    }
    free(cs);
}
static void give(int u) {
    int a = U[u].atom;
    if (subsumed(a)) { U[u].st = 2; SUBS_FWD++; return; }
    flatten(a); NCAND = 0; dt_inst(&ACT, 0, 0);
    for (long i = 0; i < NCAND; i++) { int c = CAND[i]; if (U[c].st != 1) continue; int m = NTR; int ok = match(a, U[c].atom); undo_to(m); if (ok) { U[c].st = 2; SUBS_BWD++; } }
    U[u].st = 1; dt_insert(&ACT, a, u); GIVEN++;
    for (int r = 0; r < NR && REF_RULE < 0; r++) for (int j = 0; j < R[r].nb && REF_RULE < 0; j++) {
        int m = NTR;
        if (unify(R[r].body[j], 0, U[u].atom, j + 1)) { GU = u; GJ = j; CH[j] = u; extend(r, 0); }
        undo_to(m);
    }
}

/* ---------------- proof output */
static void put_str(FILE *f, const char *s) { fputc('"', f); for (; *s; s++) { if (*s == '"' || *s == '\\') fputc('\\', f); fputc(*s, f); } fputc('"', f); }
static void put_term(FILE *f, int t) {
    if (ISVAR(t)) { fprintf(f, "\"?%d\"", VNO(t)); return; }
    fputc('[', f); put_str(f, SY[T[t].f].name);
    for (int i = 0; i < T[t].n; i++) { fputc(',', f); put_term(f, ARG(t, i)); }
    fputc(']', f);
}
static char *NEED;
static void need(int u) { if (NEED[u]) return; NEED[u] = 1; for (int i = 0; i < U[u].np; i++) need(PAR[U[u].par0 + i]); }
static long proof(FILE *f) {
    NEED = xmalloc(NU + 1); memset(NEED, 0, NU + 1);
    for (int k = 0; k < R[REF_RULE].nb; k++) need(REF_PAR[k]);
    long n = 0; if (f) fputc('[', f);
    for (int u = 0; u < NU; u++) if (NEED[u] && !is_magic(U[u].atom)) {   /* magic steps and magic parents are left out */
        int g = R[U[u].rule].guard;
        if (f) { if (n) fputs(",\n", f); fprintf(f, "{\"id\":%d,\"atom\":", u); put_term(f, U[u].atom); fputs(",\"rule\":", f); put_str(f, SY[R[U[u].rule].name].name);
            fputs(",\"parents\":[", f); for (int i = g; i < U[u].np; i++) fprintf(f, "%s%d", i > g ? "," : "", PAR[U[u].par0 + i]); fputs("]}", f); }
        n++;
    }
    if (f) { if (n) fputs(",\n", f); fputs("{\"atom\":null,\"rule\":", f); put_str(f, SY[R[REF_RULE].name].name); fputs(",\"parents\":[", f);
        for (int k = 0; k < R[REF_RULE].nb; k++) fprintf(f, "%s%d", k ? "," : "", REF_PAR[k]);
        fputs("]}]\n", f); }
    return n + 1;
}

/* ---------------- ordered resolution over Horn clauses (--res): rules compose into lemmas.
   Binary resolution of a head with a body literal, restricted to literals that are maximal in
   their clause under a Knuth-Bendix order (all symbols weight 1, precedence by arity then symbol
   number), in a DISCOUNT given-clause loop with clause subsumption. Ordered resolution is
   refutation complete for Horn clauses. */
#define KGT 1
#define KLT 2
#define KEQ 3
#define KINC 0
static int VC[1 << 14]; static int VT[1 << 14], NVT;
static void vcount(int t, int d) {
    if (ISVAR(t)) { int v = VNO(t); if (!VC[v]) VT[NVT++] = v; VC[v] += d; if (!VC[v]) VC[v] = 0; return; }
    for (int i = 0; i < T[t].n; i++) vcount(ARG(t, i), d);
}
static int prec_gt(int f, int g) { return SY[f].arity != SY[g].arity ? SY[f].arity > SY[g].arity : f > g; }
static int kbo_rec(int s, int t) {   /* lexicographic part, both sides already weighed */
    if (s == t) return KEQ;
    if (ISVAR(s) || ISVAR(t)) return KINC;
    int ws = T[s].w, wt = T[t].w;
    if (ws != wt) return ws > wt ? KGT : KLT;
    if (T[s].f != T[t].f) return prec_gt(T[s].f, T[t].f) ? KGT : KLT;
    for (int i = 0; i < T[s].n; i++) { int r = kbo_rec(ARG(s, i), ARG(t, i)); if (r != KEQ) return r; }
    return KEQ;
}
static int kbo(int s, int t) {
    if (s == t) return KEQ;
    NVT = 0; vcount(s, 1); vcount(t, -1);
    int ge = 1, le = 1; for (int i = 0; i < NVT; i++) { int v = VT[i]; if (VC[v] < 0) ge = 0; if (VC[v] > 0) le = 0; VC[v] = 0; }
    int r = kbo_rec(s, t);
    /* a weight or precedence decision counts only if the variable condition agrees */
    if (r == KGT) return ge ? KGT : KINC;
    if (r == KLT) return le ? KLT : KINC;
    return r;
}
typedef struct { int head, nb, b0, w, p1, p2, lit, src, pp0, plen; long age; char st, eh, kind, dir; uint64_t eb; } clause;   /* src: problem clause for an input; kind 0 resolution, 1 superposition (dir, path), 2 equality resolution */
static clause *C; static int NC, CC;
static int FW = 2, VW = 1, LP = 0; static double HM = 1.0;   /* clause weight: symbols FW, variables VW, head times HM, LP per body literal */
static int lwt(int t) { return FW * (T[t].w - T[t].vo) + VW * T[t].vo; }
static int *CB; static long NCB, CCB;
static dtree RH, RB, SH, SU, SG;   /* SH: heads of active non-units, SU: active units */   /* active: eligible heads, eligible body literals; subsumption: heads, first literal of headless */
static int *QW, *QA, *QS2; static long NQW, NQA, CQW, CQA, NQS, CQS;   /* by weight, by age, goal clauses (no head) by weight */
static int clw(int a, int b) { return C[a].w < C[b].w || (C[a].w == C[b].w && C[a].age < C[b].age); }
static int cla(int a, int b) { return C[a].age < C[b].age; }
static int RREF = -1; static int GOAL1[256], NGOAL1;   /* input goal clauses with one literal */
#define LIT(c, k) (CB[C[c].b0 + (k)])
/* literal selection: a Horn clause whose head is its unique maximal literal resolves on the head;
   any other clause selects its heaviest body literal (the first among equals) and resolves on that
   alone. Selecting a body literal in every clause that has one keeps ordered resolution complete. */
static void eligible(int c) {
    clause *x = &C[c]; x->eh = 0; x->eb = 0;
    if (x->head >= 0) {
        int top = 1; for (int i = 0; i < x->nb && top; i++) if (kbo(x->head, LIT(c, i)) != KGT) top = 0;
        if (top) { x->eh = 1; return; }
        if (SELMODE == 4) {   /* no selection while the head is maximal: every maximal literal is eligible */
            int dom = 0; for (int i = 0; i < x->nb && !dom; i++) if (kbo(LIT(c, i), x->head) == KGT) dom = 1;
            if (!dom) {
                x->eh = 1;
                for (int i = 0; i < x->nb; i++) { int m = 1; if (kbo(x->head, LIT(c, i)) == KGT) m = 0;
                    for (int j = 0; j < x->nb && m; j++) if (j != i && kbo(LIT(c, j), LIT(c, i)) == KGT) m = 0;
                    if (m) x->eb |= 1ULL << i; }
                return;
            }
        }
    }
    if (!x->nb) { x->eh = 1; return; }
    int best = 0;
    for (int i = 1; i < x->nb; i++) { int a = LIT(c, i), b = LIT(c, best);
        int better = SELMODE == 1 ? T[a].w < T[b].w : SELMODE == 2 ? (T[a].w - 2 * T[a].vo) > (T[b].w - 2 * T[b].vo) : SELMODE == 3 ? (T[a].gr && !T[b].gr) || (T[a].gr == T[b].gr && T[a].w > T[b].w) : T[a].w > T[b].w;
        if (better) best = i; }
    x->eb = 1ULL << best;
}
/* subsumption of clause d by clause s: one substitution sends s's head to d's head and every body literal of s to some body literal of d */
static int sub_body(int s, int k, int d, uint64_t used) {   /* multiset: distinct literals of d */
    if (k == C[s].nb) return 1;
    int a = LIT(s, k);
    for (int j = 0; j < C[d].nb; j++) { if (used >> j & 1) continue; int b = LIT(d, j); if (T[b].f != T[a].f || T[b].w < T[a].w) continue;
        int m = NTR; if (match(a, b) && sub_body(s, k + 1, d, used | 1ULL << j)) { undo_to(m); return 1; } undo_to(m); }
    return 0;
}
static int subsumes(int s, int d) {
    if (C[s].nb > C[d].nb || C[s].w > C[d].w) return 0;   /* an instance is never lighter */
    if ((C[s].head >= 0) != 0 && C[d].head < 0) return 0;
    int m = NTR; int ok = 1;
    if (C[s].head >= 0) ok = match(C[s].head, C[d].head);
    if (ok) ok = sub_body(s, 0, d, 0);
    undo_to(m); return ok;
}
static int csubsumed(int d) {
    if (C[d].head >= 0) {
        flatten(C[d].head);
        NCAND = 0; dt_gen(&SU, 0, 0); for (long i = 0; i < NCAND; i++) { int s = CAND[i]; if (s != d && C[s].st == 1) { int m = NTR; int ok = match(C[s].head, C[d].head); undo_to(m); if (ok) return 1; } }
    }
    /* clauses with a body are indexed by their heaviest body literal, which must match one of d's */
    for (int j = 0; j < C[d].nb; j++) { flatten(LIT(d, j)); NCAND = 0; dt_gen(&SG, 0, 0);
        for (long i = 0; i < NCAND; i++) { int s = CAND[i]; if (s == d || C[s].st != 1 || C[s].nb > C[d].nb || C[s].w > C[d].w) continue; if (subsumes(s, d)) return 1; } }
    return 0;
}
/* build a clause from literals under bindings, renaming variables jointly; -1 if a tautology */
/* the replacement for a superposition: literal REP_I of the list (-2 the head, -3 none) has the
   subterm at REP_PATH replaced by REP_T under bank REP_B */
static int REP_I = -3, REP_LEN, REP_T, REP_B; static const int *REP_PATH;
static int inst_replace(int t, int b, const int *path, int len) {
    if (len == 0) return inst_rec(REP_T, REP_B);
    deref(&t, &b);
    int a[64]; for (int i = 0; i < T[t].n; i++) a[i] = i == path[0] ? inst_replace(ARG(t, i), b, path + 1, len - 1) : inst_rec(ARG(t, i), b);
    return mk(T[t].f, T[t].n, a);
}
static int new_clause(int hd, int hb, int *lits, int *banks, int n, int p1, int p2, int lit, int src) {
    RMN = 0; int h = hd >= 0 ? (REP_I == -2 ? inst_replace(hd, hb, REP_PATH, REP_LEN) : inst_rec(hd, hb)) : -1; int b[1024], nb = 0;
    if (n > 1000) return -1;
    if (h >= 0 && T[h].f == EQ && ARG(h, 0) == ARG(h, 1)) return -1;   /* t = t holds */
    for (int i = 0; i < n; i++) { int a = i == REP_I ? inst_replace(lits[i], banks[i], REP_PATH, REP_LEN) : inst_rec(lits[i], banks[i]); int dup = 0; for (int j = 0; j < nb; j++) if (b[j] == a) dup = 1; if (!dup) b[nb++] = a; if (a == h) return -1; }
    if (nb > 62) return -1;
    if (NC == CC) { CC = CC ? CC * 2 : 4096; C = xrealloc(C, CC * sizeof(clause)); }
    if (NCB + nb > CCB) { while (NCB + nb > CCB) CCB = CCB ? CCB * 2 : 1 << 16; CB = xrealloc(CB, CCB * sizeof(int)); }
    int c = NC++; clause *x = &C[c]; x->head = h; x->nb = nb; x->b0 = (int)NCB; memcpy(CB + NCB, b, nb * sizeof(int)); NCB += nb;
    x->w = h >= 0 ? (int)(HM * lwt(h)) : 0; for (int i = 0; i < nb; i++) x->w += lwt(b[i]); x->w += LP * nb;
    x->p1 = p1; x->p2 = p2; x->lit = lit; x->src = src; x->age = AGE++; x->st = 0; x->kind = 0; x->dir = 0; x->pp0 = 0; x->plen = 0;
    return c;
}
static void keep_clause(int c) {
    if (C[c].head < 0 && C[c].nb == 0) { RREF = c; return; }
    hpush(&QW, &NQW, &CQW, c, clw); hpush(&QA, &NQA, &CQA, c, cla); if (C[c].head < 0) hpush(&QS2, &NQS, &CQS, c, clw); KEPTN++;
}
static void finish(int c);
static void resolvent(int hc, int bc, int k) {   /* head of hc (bank 1) against body literal k of bc (bank 2), unified already */
    GENERATED++;
    int lits[1024], banks[1024], n = 0;
    for (int i = 0; i < C[bc].nb && n < 1000; i++) if (i != k) { lits[n] = LIT(bc, i); banks[n++] = 2; }
    for (int i = 0; i < C[hc].nb && n < 1000; i++) { lits[n] = LIT(hc, i); banks[n++] = 1; }
    int c = new_clause(C[bc].head, 2, lits, banks, n, hc, bc, k, -1);
    if (c < 0) return;
    finish(c);
}
/* ---------------- equality: superposition and equality resolution (--res with = in the input).
   From an eligible positive equation l = r (l not smaller than r, l not a variable) into a
   non-variable subterm of an eligible literal of another clause: replace it by r under the
   unifier and add the equation's body. Equality resolution removes an eligible negative
   equation s = t whose sides unify. With resolution this is complete for Horn clauses. */
typedef struct { int c, slot, pp0, plen; } spos;   /* slot -1 the head, k body literal k */
static spos *SP; static int NSP, CSP;
static int *PB; static long NPB, CPB;
static dtree RSUB, RHE, RALL;   /* RALL: every position of every active clause, for backward demodulation */
static dtree *POS_TREE;
static int PTMP[512];
static int lit_of(int c, int slot) { return slot < 0 ? C[c].head : LIT(c, slot); }
static int sub_at(int t, const int *path, int len) { for (int i = 0; i < len; i++) t = ARG(t, path[i]); return t; }
static int savepath(const int *p, int len) {
    if (NPB + len > CPB) { while (NPB + len > CPB) CPB = CPB ? CPB * 2 : 1 << 16; PB = xrealloc(PB, CPB * sizeof(int)); }
    memcpy(PB + NPB, p, len * sizeof(int)); NPB += len; return (int)(NPB - len);
}
static void pos_rec(int c, int slot, int t, int depth) {
    if (ISVAR(t) || depth > 500) return;
    if (NSP == CSP) { CSP = CSP ? CSP * 2 : 4096; SP = xrealloc(SP, CSP * sizeof(spos)); }
    int id = NSP++; SP[id].c = c; SP[id].slot = slot; SP[id].plen = depth; SP[id].pp0 = savepath(PTMP, depth);
    dt_insert(POS_TREE, t, id);
    for (int j = 0; j < T[t].n; j++) { PTMP[depth] = j; pos_rec(c, slot, ARG(t, j), depth + 1); }
}
static void add_positions_to(dtree *d, int c, int slot) { POS_TREE = d; int a = lit_of(c, slot); for (int i = 0; i < T[a].n; i++) { PTMP[0] = i; pos_rec(c, slot, ARG(a, i), 1); } }
static void add_positions(int c, int slot) { add_positions_to(&RSUB, c, slot); }
static void superpose(int fc, int dir, int rec) {   /* fc in bank 1, the target in bank 2, unified already */
    GENERATED++;
    int ic = SP[rec].c, slot = SP[rec].slot, len = SP[rec].plen; int path[512]; memcpy(path, PB + SP[rec].pp0, len * sizeof(int));   /* PB may move */
    int lits[1024], banks[1024], n = 0;
    for (int i = 0; i < C[ic].nb && n < 1000; i++) { lits[n] = LIT(ic, i); banks[n++] = 2; }
    for (int i = 0; i < C[fc].nb && n < 1000; i++) { lits[n] = LIT(fc, i); banks[n++] = 1; }
    REP_I = slot < 0 ? -2 : slot; REP_PATH = path; REP_LEN = len; REP_T = ARG(C[fc].head, 1 - dir); REP_B = 1;
    int c = new_clause(C[ic].head, 2, lits, banks, n, fc, ic, slot, -1);
    REP_I = -3;
    if (c < 0) return;
    C[c].kind = 1; C[c].dir = dir; C[c].pp0 = savepath(path, len); C[c].plen = len;
    finish(c);
}
static void eq_resolve(int g, int k) {   /* sides of body literal k unified in bank 1 */
    GENERATED++;
    int lits[1024], banks[1024], n = 0;
    for (int i = 0; i < C[g].nb; i++) if (i != k) { lits[n] = LIT(g, i); banks[n++] = 1; }
    int c = new_clause(C[g].head, 1, lits, banks, n, g, -1, k, -1);
    if (c < 0) return;
    C[c].kind = 2;
    finish(c);
}
/* forward demodulation by active oriented unit equations l = r (l > r in the order, so every
   instance is oriented too): each rewrite is recorded as a superposition step with that unit */
static dtree RDEM;
static int dem_find(int t, int depth, int *u, int *d) {   /* outermost first; PTMP holds the path */
    if (ISVAR(t) || depth > 500) return -1;
    flatten(t); NCAND = 0; dt_gen(&RDEM, 0, 0);
    for (long i = 0; i < NCAND; i++) { int c = CAND[i] / 2, dd = CAND[i] % 2; if (C[c].st != 1) continue;
        int m = NTR; if (match(ARG(C[c].head, dd), t)) { *u = c; *d = dd; return depth; } undo_to(m); }
    for (int j = 0; j < T[t].n; j++) { PTMP[depth] = j; int r = dem_find(ARG(t, j), depth + 1, u, d); if (r >= 0) return r; }
    return -1;
}
static int demod(int c) {
    int start_nc = NC; long start_cb = NCB; (void)start_nc; (void)start_cb;
    for (int steps = 0; steps < 1000; steps++) {
        int slot = -2, u = -1, d = 0, len = -1, m = NTR;
        MATCH_BANK = 3;
        if (C[c].head >= 0) { int a = C[c].head; for (int i = 0; i < T[a].n && len < 0; i++) { PTMP[0] = i; len = dem_find(ARG(a, i), 1, &u, &d); } if (len >= 0) slot = -1; }
        for (int k = 0; k < C[c].nb && len < 0; k++) { int a = LIT(c, k); for (int i = 0; i < T[a].n && len < 0; i++) { PTMP[0] = i; len = dem_find(ARG(a, i), 1, &u, &d); } if (len >= 0) slot = k; }
        MATCH_BANK = 0;
        if (len < 0) { undo_to(m); return c; }
        int path[512]; memcpy(path, PTMP, len * sizeof(int));
        int lits[64], banks[64], n = C[c].nb; for (int i = 0; i < n; i++) { lits[i] = LIT(c, i); banks[i] = 3; }
        REP_I = slot < 0 ? -2 : slot; REP_PATH = path; REP_LEN = len; REP_T = ARG(C[u].head, 1 - d); REP_B = MB;
        int c2 = new_clause(C[c].head, 3, lits, banks, n, u, c, slot, -1);
        REP_I = -3; undo_to(m);
        if (c2 < 0) return -1;   /* became a tautology */
        C[c2].kind = 1; C[c2].dir = d; C[c2].pp0 = savepath(path, len); C[c2].plen = len; C[c2].st = 3;   /* 3: a step on the way */
        c = c2;
    }
    return c;
}
/* the ordering side conditions of superposition, on the instances: r must not exceed l, and a
   target equation is entered on a side the other side does not exceed */
static int inst_free(int t, int b) { RMN = 0; return inst_rec(t, b); }
static int sup_ok(int fc, int dir, int rec) {
    int h = C[fc].head; int l = inst_free(ARG(h, dir), 1), r = inst_free(ARG(h, 1 - dir), 1);
    if (kbo(r, l) == KGT) return 0;
    spos *q = &SP[rec]; int tl = lit_of(q->c, q->slot);
    if (T[tl].f == EQ) { int side = PB[q->pp0]; int a = inst_free(ARG(tl, side), 2), o = inst_free(ARG(tl, 1 - side), 2); if (kbo(o, a) == KGT) return 0; }
    return 1;
}
/* every new clause ends here: refutation, weight bound, demodulation, subsumption, kept */
static void finish(int c) {
    if (C[c].head < 0 && C[c].nb == 0) { RREF = c; return; }
    if (HAS_EQ) { int c2 = demod(c); if (c2 < 0) return; c = c2; C[c].st = 0;
        if (C[c].head < 0 && C[c].nb == 0) { RREF = c; return; }
        for (int k = 0; k < C[c].nb; k++) { int a = LIT(c, k); if (T[a].f == EQ && ARG(a, 0) == ARG(a, 1)) { /* t != t: equality resolution with no unifier needed */ } } }
    if (MAXW && C[c].w > MAXW) { DROPPED = 1; return; }
    if (csubsumed(c)) { SUBS_FWD++; return; }
    keep_clause(c);
    /* a positive unit that unifies with a one-literal goal refutes at once */
    if (C[c].head >= 0 && C[c].nb == 0)
        for (int i = 0; i < NGOAL1 && RREF < 0; i++) { int g = GOAL1[i]; int m = NTR;
            if (unify(C[c].head, 4, LIT(g, 0), 5)) { int e = new_clause(-1, 0, NULL, NULL, 0, c, g, 0, -1); if (e >= 0) RREF = e; }
            undo_to(m); }
}
/* backward demodulation: active clauses with an instance of l are retired and come back rewritten */
static void back_demod(int u, int l) {
    flatten(l); NCAND = 0; dt_inst(&RALL, 0, 0);
    long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
    for (long i = 0; i < n && RREF < 0; i++) { spos *q = &SP[cs[i]]; int c = q->c; if (c == u || C[c].st != 1) continue;
        int sub = sub_at(lit_of(c, q->slot), PB + q->pp0, q->plen);
        int m = NTR; int ok = match(l, sub); undo_to(m); if (!ok) continue;
        C[c].st = 2; SUBS_BWD++;
        int c2 = demod(c); if (c2 < 0 || c2 == c) continue;
        C[c2].st = 0; finish(c2);
    }
    free(cs);
}
static void eq_give(int g) {
    /* index g: its eligible literals' positions, and its eligible equation sides */
    if (C[g].eh) add_positions(g, -1);
    for (int k = 0; k < C[g].nb; k++) if (C[g].eb >> k & 1) add_positions(g, k);
    if (C[g].head >= 0) add_positions_to(&RALL, g, -1);
    for (int k = 0; k < C[g].nb; k++) add_positions_to(&RALL, g, k);
    int h = C[g].head;
    if (C[g].eh && h >= 0 && T[h].f == EQ)
        for (int d = 0; d < 2; d++) { int l = ARG(h, d), r = ARG(h, 1 - d); if (!ISVAR(l) && kbo(r, l) != KGT) dt_insert(&RHE, l, g * 2 + d);
            if (!C[g].nb && kbo(l, r) == KGT) { dt_insert(&RDEM, l, g * 2 + d); back_demod(g, l); } }
    /* from g into active positions (g's own included) */
    if (C[g].eh && h >= 0 && T[h].f == EQ)
        for (int d = 0; d < 2 && RREF < 0; d++) {
            int l = ARG(h, d), r = ARG(h, 1 - d); if (ISVAR(l) || kbo(r, l) == KGT) continue;
            flatten(l); NCAND = 0; dt_unif(&RSUB, 0, 0);
            long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
            for (long i = 0; i < n && RREF < 0; i++) { spos *q = &SP[cs[i]]; if (C[q->c].st != 1) continue;
                int sub = sub_at(lit_of(q->c, q->slot), PB + q->pp0, q->plen);
                int m = NTR; if (unify(l, 1, sub, 2) && sup_ok(g, d, cs[i])) superpose(g, d, cs[i]); undo_to(m); }
            free(cs);
        }
    /* from active equations into g's positions */
    for (int rec = 0; rec < NSP && RREF < 0; rec++) { if (SP[rec].c != g) continue;
        int sub = sub_at(lit_of(g, SP[rec].slot), PB + SP[rec].pp0, SP[rec].plen);
        flatten(sub); NCAND = 0; dt_unif(&RHE, 0, 0);
        long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
        for (long i = 0; i < n && RREF < 0; i++) { int fc = cs[i] / 2, d = cs[i] % 2; if (fc == g || C[fc].st != 1) continue;
            int m = NTR; if (unify(ARG(C[fc].head, d), 1, sub, 2) && sup_ok(fc, d, rec)) superpose(fc, d, rec); undo_to(m); }
        free(cs);
    }
    /* equality resolution on g's eligible negative equations */
    for (int k = 0; k < C[g].nb && RREF < 0; k++) if ((C[g].eb >> k & 1) && T[LIT(g, k)].f == EQ) {
        int a = LIT(g, k); int m = NTR; if (unify(ARG(a, 0), 1, ARG(a, 1), 1)) eq_resolve(g, k); undo_to(m);
    }
}
static void res_give(int g) {
    if (HAS_EQ) { int g2 = demod(g); if (g2 < 0) { C[g].st = 2; return; } if (g2 != g) { C[g].st = 2; g = g2; C[g].st = 0; if (C[g].head < 0 && C[g].nb == 0) { RREF = g; return; } } }
    if (csubsumed(g)) { C[g].st = 2; SUBS_FWD++; return; }
    eligible(g);
    /* backward subsumption among active clauses */
    if (C[g].head >= 0) { flatten(C[g].head); NCAND = 0; dt_inst(&SH, 0, 0); if (!C[g].nb) dt_inst(&SU, 0, 0); for (long i = 0; i < NCAND; i++) { int s = CAND[i]; if (s != g && C[s].st == 1 && subsumes(g, s)) { C[s].st = 2; SUBS_BWD++; } } }
    C[g].st = 1; GIVEN++;
    if (C[g].head >= 0) dt_insert(C[g].nb ? &SH : &SU, C[g].head, g);   /* SH serves backward subsumption */
    if (C[g].nb) { int key = 0; for (int k = 1; k < C[g].nb; k++) if (T[LIT(g, k)].w > T[LIT(g, key)].w) key = k; dt_insert(&SG, LIT(g, key), g); }
    if (C[g].eh) dt_insert(&RH, C[g].head, g);
    for (int k = 0; k < C[g].nb; k++) if (C[g].eb >> k & 1) dt_insert(&RB, LIT(g, k), g * 64 + k);
    /* g's eligible body literals against active eligible heads */
    for (int k = 0; k < C[g].nb && RREF < 0; k++) if (C[g].eb >> k & 1) {
        flatten(LIT(g, k)); NCAND = 0; dt_unif(&RH, 0, 0);
        long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
        for (long i = 0; i < n && RREF < 0; i++) { int h = cs[i]; if (C[h].st != 1) continue; int m = NTR; if (unify(C[h].head, 1, LIT(g, k), 2)) resolvent(h, g, k); undo_to(m); if (C[g].st != 1) break; }
        free(cs);
    }
    /* g's eligible head against active eligible body literals */
    if (C[g].eh && RREF < 0) {
        flatten(C[g].head); NCAND = 0; dt_unif(&RB, 0, 0);
        long n = NCAND; int *cs = xmalloc((n + 1) * sizeof(int)); memcpy(cs, CAND, n * sizeof(int));
        for (long i = 0; i < n && RREF < 0; i++) { int b = cs[i] / 64, k = cs[i] % 64; if (C[b].st != 1 || b == g) continue; int m = NTR; if (unify(C[g].head, 1, LIT(b, k), 2)) resolvent(g, b, k); undo_to(m); }
        free(cs);
    }
    if (HAS_EQ && RREF < 0 && C[g].st == 1) eq_give(g);
}
static void put_clause(FILE *f, int c) {
    fprintf(f, "{\"id\":%d,\"head\":", c); if (C[c].head >= 0) put_term(f, C[c].head); else fputs("null", f);
    fputs(",\"body\":[", f); for (int i = 0; i < C[c].nb; i++) { if (i) fputc(',', f); put_term(f, LIT(c, i)); } fputc(']', f);
    if (C[c].src >= 0) { fputs(",\"input\":", f); put_str(f, SY[R[C[c].src].name].name); }
    else if (C[c].kind == 1) { fprintf(f, ",\"rule\":\"sup\",\"from\":[%d,%d,%d],\"dir\":%d,\"path\":[", C[c].p1, C[c].p2, C[c].lit, C[c].dir);
        for (int i = 0; i < C[c].plen; i++) fprintf(f, "%s%d", i ? "," : "", PB[C[c].pp0 + i]);
        fputc(']', f); }
    else if (C[c].kind == 2) fprintf(f, ",\"rule\":\"eqres\",\"from\":[%d,%d]", C[c].p1, C[c].lit);
    else fprintf(f, ",\"from\":[%d,%d,%d]", C[c].p1, C[c].p2, C[c].lit);
    fputc('}', f);
}
static char *CNEED;
static void cneed(int c) { if (CNEED[c]) return; CNEED[c] = 1; if (C[c].src < 0) { cneed(C[c].p1); if (C[c].kind != 2) cneed(C[c].p2); } }
static long res_proof(FILE *f) {
    CNEED = xmalloc(NC + 1); memset(CNEED, 0, NC + 1); cneed(RREF);
    long n = 0; if (f) fputc('[', f);
    for (int c = 0; c < NC; c++) if (CNEED[c]) { if (f) { if (n) fputs(",\n", f); put_clause(f, c); } n++; }
    if (f) fputs("]\n", f);
    return n;
}
static int CYCLE[64] = { 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, CYCLE_N = 20;   /* goal, weight, goal, then weight: picking by weight alone is fair, since finitely many clauses up to renaming have a given weight, and age picks drag in heavy clauses */
static int res_run(double ratio) {
    (void)ratio;
    for (int r = 0; r < NR && RREF < 0; r++) { int banks[MAXB]; for (int i = 0; i < R[r].nb; i++) banks[i] = 0; int c = new_clause(R[r].head, 0, R[r].body, banks, R[r].nb, -1, -1, -1, r); if (c >= 0) keep_clause(c); }
    long picks = 0;
    int ninput = NC;
    for (int c = 0; c < ninput; c++) if (C[c].head < 0 && C[c].nb == 1 && NGOAL1 < 256) GOAL1[NGOAL1++] = c;
    for (int c = 0; c < ninput && RREF < 0; c++) if (C[c].st == 0) res_give(c);   /* the input clauses first, as E does */
    while (RREF < 0) {
        if (now_s() > DEADLINE) return 0;
        int g = -1;
        while (g < 0) {
            /* a cycle of picks: goal clauses (backward from the conjecture), lightest, oldest */
            int slot = picks % CYCLE_N, q = CYCLE[slot];
            int x = q == 2 ? hpop(QS2, &NQS, clw) : q == 1 ? hpop(QA, &NQA, cla) : hpop(QW, &NQW, clw);
            if (x < 0) x = hpop(QW, &NQW, clw);
            if (x < 0) { x = hpop(QA, &NQA, cla); if (x < 0) break; }
            if (C[x].st == 0) g = x; else if (q == 2 && x >= 0) { picks++; }
        }
        if (g < 0) return DROPPED ? 0 : -1;
        picks++; res_give(g);
    }
    return 1;
}

static void set_cycle(const char *c) { CYCLE_N = 0; for (; *c && CYCLE_N < 64; c++) CYCLE[CYCLE_N++] = *c == 'g' ? 2 : *c == 'a' ? 1 : 0; }
static double T0;
/* one attempt with the configuration in the globals; prints only a refutation unless loud */
static int attempt(double limit, int ratio, const char *base, const char *pj, int loud) {
    DEADLINE = now_s() + limit;
    if (MAGIC) magic_transform();
    if (RES) {
        dt_init(&RH); dt_init(&RB); dt_init(&SH); dt_init(&SU); dt_init(&SG); dt_init(&RSUB); dt_init(&RHE); dt_init(&RDEM); dt_init(&RALL);
        int st = res_run(ratio); double secs = now_s() - T0;
        if (st > 0) {
            printf("%% SZS status Unsatisfiable for %s\n", base);
            FILE *o = pj ? fopen(pj, "w") : NULL; if (pj && !o) die("cannot write proof");
            long ps = res_proof(o); if (o) fclose(o);
            printf("%% engine res\n%% secs %.4f given %ld kept %ld generated %ld proof_steps %ld\n", secs, GIVEN, KEPTN, GENERATED, ps);
        } else if (loud && st < 0) printf("%% SZS status Satisfiable for %s\n%% secs %.4f given %ld kept %ld\n", base, secs, GIVEN, KEPTN);
        else if (loud) printf("%% SZS status Timeout for %s\n%% secs %.4f given %ld kept %ld generated %ld\n", base, secs, GIVEN, KEPTN, GENERATED);
        return st;
    }
    for (int r = 0; r < NR && REF_RULE < 0; r++) if (R[r].nb == 0 && R[r].head >= 0) { int a = inst(R[r].head, 0, NULL); if (!seen(a)) add_unit(a, r, 0, NULL); }
    long picks = 0; int sat = 0;
    while (REF_RULE < 0) {
        if (now_s() > DEADLINE) break;
        int u = -1;
        while (u < 0) {
            int byage = ratio > 0 && picks % ratio == ratio - 1;
            int x = byage ? hpop(HA, &NHA, lessa) : hpop(HW, &NHW, lessw);
            if (x < 0) { x = byage ? hpop(HW, &NHW, lessw) : hpop(HA, &NHA, lessa); if (x < 0) break; }
            if (U[x].st == 0) u = x;
        }
        if (u < 0) { sat = !DROPPED; if (DROPPED) DEADLINE = 0; break; }
        picks++; give(u);
    }
    double secs = now_s() - T0;
    if (REF_RULE >= 0) {
        printf("%% SZS status Unsatisfiable for %s\n", base);
        FILE *o = pj ? fopen(pj, "w") : NULL; if (pj && !o) die("cannot write proof");
        long ps = proof(o); if (o) fclose(o);
        printf("%% engine hyper\n%% secs %.4f given %ld kept %ld generated %ld proof_steps %ld\n", secs, GIVEN, KEPTN, GENERATED, ps);
        return 1;
    }
    if (loud && sat) printf("%% SZS status Satisfiable for %s\n%% secs %.4f given %ld kept %ld\n", base, secs, GIVEN, KEPTN);
    else if (loud) printf("%% SZS status Timeout for %s\n%% secs %.4f given %ld kept %ld generated %ld\n", base, secs, GIVEN, KEPTN, GENERATED);
    return sat ? -1 : 0;
}
/* the strategy schedule: every configuration in turn, in a fresh child process, with a time slice
   that doubles each round; the first refutation wins. A configuration that saturates proves the
   input satisfiable (each is complete for Horn clauses), and the schedule stops. */
typedef struct { const char *args; double secs; } config;
/* (filled from the training-half sweep by bench/make_schedule.py) */
static const config SCHED[] = {
    { "--res --wt 1,1,1,0", 0.5 },
    { "--single", 0.5 },
    { "--magic", 0.5 },
    { "--res --wt 2,1,1,3", 0.5 },
};
static void apply_args(const char *a) {   /* a setting is a string of the command-line options */
    char buf[512]; snprintf(buf, sizeof buf, "%s", a); char *tok[32]; int n = 0;
    for (char *t = strtok(buf, " "); t && n < 32; t = strtok(NULL, " ")) tok[n++] = t;
    MAGIC = RES = 0; MAXW = 0; FW = 2; VW = 1; HM = 1.0; LP = 0; SELMODE = 0;
    for (int i = 0; i < n; i++) {
        if (!strcmp(tok[i], "--magic")) MAGIC = 1;
        else if (!strcmp(tok[i], "--res")) RES = 1;
        else if (!strcmp(tok[i], "--maxw") && i + 1 < n) MAXW = atoi(tok[++i]);
        else if (!strcmp(tok[i], "--ratio") && i + 1 < n) SCHED_RATIO = atoi(tok[++i]);
        else if (!strcmp(tok[i], "--wt") && i + 1 < n) sscanf(tok[++i], "%d,%d,%lf,%d", &FW, &VW, &HM, &LP);
        else if (!strcmp(tok[i], "--cycle") && i + 1 < n) set_cycle(tok[++i]);
        else if (!strcmp(tok[i], "--sel") && i + 1 < n) SELMODE = atoi(tok[++i]);
    }
}
#include <sys/wait.h>
#include <unistd.h>
static int run_child(int k, double lim, const char *base, const char *pj) {
    pid_t pid = fork();
    if (pid < 0) die("fork");
    if (pid == 0) {
        SCHED_RATIO = 5; apply_args(SCHED[k].args);
        int st = attempt(lim, SCHED_RATIO, base, pj, 0);
        fflush(stdout); _exit(st > 0 ? 10 : st < 0 ? 20 : 0);
    }
    int ws; waitpid(pid, &ws, 0);
    if (WIFEXITED(ws) && WEXITSTATUS(ws) == 10) return 1;
    if (WIFEXITED(ws) && WEXITSTATUS(ws) == 20) return -1;
    return 0;
}
static int schedule(double limit, const char *base, const char *pj) {
    int n = sizeof SCHED / sizeof SCHED[0]; double top = 0;
    fflush(stdout);
    for (int k = 0; k < n; k++) {   /* the fitted schedule */
        double left = T0 + limit - now_s(); if (left <= 0.005) return 0;
        double lim = SCHED[k].secs < left ? SCHED[k].secs : left; if (SCHED[k].secs > top) top = SCHED[k].secs;
        int st = run_child(k, lim, base, pj); if (st) return st;
    }
    for (double slice = 2 * top;; slice *= 2)   /* then every setting again, with doubling slices */
        for (int k = 0; k < n; k++) {
            double left = T0 + limit - now_s(); if (left <= 0.005) return 0;
            int st = run_child(k, slice < left ? slice : left, base, pj); if (st) return st;
        }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: hyper PROBLEM.p [--root DIR] [--limit S] [--proof-json FILE]\n"); return 2; }
    const char *path = argv[1], *pj = NULL; char root[4096]; double limit = 30; int ratio = 5;
    { const char *q = strstr(path, "Problems/"); if (q) snprintf(root, sizeof root, "%.*s", (int)(q - path), path); else strcpy(root, "."); if (!root[0]) strcpy(root, "."); }
    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "--root") && i + 1 < argc) snprintf(root, sizeof root, "%s", argv[++i]);
        else if (!strcmp(argv[i], "--limit") && i + 1 < argc) limit = atof(argv[++i]);
        else if (!strcmp(argv[i], "--proof-json") && i + 1 < argc) pj = argv[++i];
        else if (!strcmp(argv[i], "--ratio") && i + 1 < argc) ratio = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--magic")) MAGIC = SINGLE = 1;
        else if (!strcmp(argv[i], "--res")) RES = SINGLE = 1;
        else if (!strcmp(argv[i], "--single")) SINGLE = 1;
        else if (!strcmp(argv[i], "--sel") && i + 1 < argc) SELMODE = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--maxw") && i + 1 < argc) MAXW = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--wt") && i + 1 < argc) { sscanf(argv[++i], "%d,%d,%lf,%d", &FW, &VW, &HM, &LP); }
        else if (!strcmp(argv[i], "--cycle") && i + 1 < argc) set_cycle(argv[++i]);
    }
    T0 = now_s();
    for (int b = 0; b < MAXB; b++) for (int v = 0; v < MAXV; v++) BT[b][v] = -1;
    dt_init(&KEPT); dt_init(&ACT);
    parse_file(path, root, NULL, -1);
    const char *base = strrchr(path, '/'); base = base ? base + 1 : path;
    if (getenv("HYPER_DUMP")) for (int r = 0; r < NR; r++) { fprintf(stderr, "%s: head %d nb %d nv %d\n", SY[R[r].name].name, R[r].head, R[r].nb, R[r].nv); }
    if (OUT_OF_CLASS) { printf("%% SZS status GaveUp for %s\n%% reason %s\n", base, WHY); return 0; }
    if (SINGLE) { attempt(limit, ratio, base, pj, 1); return 0; }
    int st = schedule(limit, base, pj);
    if (st < 0) printf("%% SZS status Satisfiable for %s\n%% secs %.4f\n", base, now_s() - T0);
    else if (st == 0) printf("%% SZS status Timeout for %s\n%% secs %.4f\n", base, now_s() - T0);
    return 0;
}
