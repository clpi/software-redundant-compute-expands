/* core.c: two more engines that run in time slices beside forward chaining (included by horn.c).
   ORD  ordered resolution with literal selection over flat Horn clauses: a given-clause loop with
        forward subsumption. Rule bodies resolve against rule heads, so it composes rules into
        lemmas (a 2^30-step counter becomes about 500 resolutions).
   EQB  equivalence rewriting with bidirectional search, for rules with one state literal plus side
        literals over fact-only predicates. A pair of rules a->b and b->a is used to rewrite every
        state to a normal form, which quotients the state space; states grow forward from the
        facts and goals grow backward from the negated conjecture until one matches the other.
   Both report only refutations. Only forward chaining, which saturates, reports Satisfiable. */

static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }
#define UNB INT32_MIN
#define MAXV 256

/* ---------------- shared helpers on flat atoms: int[1 + arity] = pred, args; var v is -(v+1) */
static int alen(const int *a) { return 1 + PAR[a[0]]; }
static int *adup(const int *a) { int n = alen(a); int *b = xmalloc(n * sizeof(int)); memcpy(b, a, n * sizeof(int)); return b; }
static int walkt(int t, const int *B) { while (t < 0 && B[-t - 1] != UNB) t = B[-t - 1]; return t; }
static int unify_at(const int *a, const int *b, int *B, int *trail, int *nt) {
    if (a[0] != b[0]) return 0;
    for (int k = 1; k <= PAR[a[0]]; k++) {
        int x = walkt(a[k], B), y = walkt(b[k], B);
        if (x == y) continue;
        if (x < 0) { B[-x - 1] = y; trail[(*nt)++] = -x - 1; }
        else if (y < 0) { B[-y - 1] = x; trail[(*nt)++] = -y - 1; }
        else return 0;
    }
    return 1;
}
/* one-way: pattern a (vars bound in M) onto target b (b's vars are opaque values) */
static int match_at(const int *a, const int *b, int *M, int *trail, int *nt) {
    if (a[0] != b[0]) return 0;
    for (int k = 1; k <= PAR[a[0]]; k++) {
        int x = a[k], y = b[k];
        if (x < 0) { if (M[-x - 1] == UNB) { M[-x - 1] = y; trail[(*nt)++] = -x - 1; } else if (M[-x - 1] != y) return 0; }
        else if (x != y) return 0;
    }
    return 1;
}
static void undo(int *B, const int *trail, int from, int *nt) { while (*nt > from) B[trail[--(*nt)]] = UNB; }
static uint64_t hatoms(int hh, int nb, int *const *at) {
    uint64_t h = (uint64_t)(hh * 2 + 1) * 0x9E3779B97F4A7C15ULL ^ (uint64_t)nb;
    for (int i = 0; i < nb + hh; i++) { const int *a = at[i]; for (int k = 0; k < alen(a); k++) h = (h ^ (uint64_t)(unsigned)a[k]) * 1099511628211ULL; }
    return h;
}

/* ---------------- ORD */
typedef struct { int nb, hh, sel, w, nv; int **lit; int p1, p2, rule; uint64_t h; } ocl;   /* lit[0] head if hh, then body */
typedef struct { int w; long age; int c; } hent;
typedef struct {
    int dir, done, refuted, nvin;
    ocl *C; int NC, CC;
    hent *H; long NH, CH, AGE;
    int *HT; long HTC, HTN;          /* dedup over every clause made */
    ivec *BYH, *BYS; int NP;         /* active clauses by eligible head pred / selected literal pred */
    ivec *SK; long SKC;              /* subsumption buckets over active clauses, hashed key */
    long given, res;
    int B[2 * MAXV], M[MAXV], trail[4 * MAXV], mtr[4 * MAXV];
} ord;

static int ord_gt(const ord *o, const int *a, const int *b) {
    if (a[0] != b[0]) return 0;
    int n = PAR[a[0]];
    int ca[MAXV] = {0}, cb[MAXV] = {0};
    for (int k = 1; k <= n; k++) { if (a[k] < 0 && -a[k] - 1 < MAXV) ca[-a[k] - 1]++; if (b[k] < 0 && -b[k] - 1 < MAXV) cb[-b[k] - 1]++; }
    for (int v = 0; v < MAXV; v++) if (cb[v] > ca[v]) return 0;
    for (int j = 0; j < n; j++) {
        int k = o->dir > 0 ? 1 + j : n - j;
        int x = a[k], y = b[k];
        if (x == y) continue;
        if (x < 0 || y < 0) return 0;
        return x > y;    /* precedence: symbol id order, which is first-occurrence order */
    }
    return 0;
}
/* index of the eligible literal: a maximal body literal (selected), or -1 for the head */
static int ord_elig(const ord *o, int hh, int nb, int **lit) {
    for (int i = 0; i < nb; i++) {
        const int *l = lit[hh + i]; int dom = 0;
        for (int j = 0; j < nb + hh && !dom; j++) if (j != hh + i && ord_gt(o, lit[j], l)) dom = 1;
        if (!dom) return i;
    }
    return -1;
}
/* canonical copy of (hh, nb, lit) under substitution B: vars renumbered by first occurrence */
static int ord_canon(int hh, int nb, int **lit, const int *B, int **out, int *nvout) {
    int map[2 * MAXV]; for (int i = 0; i < 2 * MAXV; i++) map[i] = 0;
    int nv = 0;
    for (int i = 0; i < nb + hh; i++) {
        const int *a = lit[i]; int n = alen(a); int *b = xmalloc(n * sizeof(int)); b[0] = a[0];
        for (int k = 1; k < n; k++) {
            int t = B ? walkt(a[k], B) : a[k];
            if (t < 0) { int v = -t - 1; if (!map[v]) { if (nv >= MAXV / 2 - 1) { for (int j = 0; j <= i; j++) free(out[j]); return 0; } map[v] = ++nv; } t = -map[v]; }
            b[k] = t;
        }
        out[i] = b;
    }
    *nvout = nv; return 1;
}
static void ord_heap_push(ord *o, int w, int c) {
    if (o->NH == o->CH) { o->CH = o->CH ? o->CH * 2 : 1024; o->H = xrealloc(o->H, o->CH * sizeof(hent)); }
    long i = o->NH++; hent e = { w, o->AGE++, c };
    while (i > 0) { long p = (i - 1) / 2; if (o->H[p].w < e.w || (o->H[p].w == e.w && o->H[p].age < e.age)) break; o->H[i] = o->H[p]; i = p; }
    o->H[i] = e;
}
static hent ord_heap_pop(ord *o) {
    hent top = o->H[0], e = o->H[--o->NH]; long i = 0;
    for (;;) { long l = 2 * i + 1, r = l + 1, m = i; hent best = e;
        if (l < o->NH && (o->H[l].w < best.w || (o->H[l].w == best.w && o->H[l].age < best.age))) { m = l; best = o->H[l]; }
        if (r < o->NH && (o->H[r].w < best.w || (o->H[r].w == best.w && o->H[r].age < best.age))) { m = r; best = o->H[r]; }
        if (m == i) break; o->H[i] = o->H[m]; i = m; }
    if (o->NH) o->H[i] = e;
    return top;
}
static int ord_same(const ocl *a, int hh, int nb, int **lit) {
    if (a->hh != hh || a->nb != nb) return 0;
    for (int i = 0; i < nb + hh; i++) if (memcmp(a->lit[i], lit[i], alen(lit[i]) * sizeof(int))) return 0;
    return 1;
}
static long ord_skey(int hh, int nb, int **lit, long cap) {
    uint64_t k = ((uint64_t)(hh ? lit[0][0] + 1 : 0) * 1000003ULL + (uint64_t)nb) * 1000003ULL + (uint64_t)(nb ? lit[hh][0] + 1 : 0);
    return (long)(k % (uint64_t)cap);
}
static int ord_subsumes_rec(ord *o, const ocl *c, int i, const ocl *d, int *nt) {
    if (i == c->nb) return 1;
    const int *a = c->lit[c->hh + i];
    for (int j = 0; j < d->nb; j++) {
        int from = *nt;
        if (match_at(a, d->lit[d->hh + j], o->M, o->mtr, nt) && ord_subsumes_rec(o, c, i + 1, d, nt)) { undo(o->M, o->mtr, from, nt); return 1; }
        undo(o->M, o->mtr, from, nt);
    }
    return 0;
}
static int ord_subsumes(ord *o, const ocl *c, const ocl *d) {
    if (c->hh != d->hh || c->nb > d->nb) return 0;
    int nt = 0, r = 1;
    if (c->hh && !match_at(c->lit[0], d->lit[0], o->M, o->mtr, &nt)) r = 0;
    if (r) r = ord_subsumes_rec(o, c, 0, d, &nt);
    undo(o->M, o->mtr, 0, &nt);
    return r;
}
static int ord_subsumed(ord *o, const ocl *d, int self) {
    ivec *v = &o->SK[ord_skey(d->hh, d->nb, d->lit, o->SKC)];
    for (int i = 0; i < v->n; i++) if (v->a[i] != self && ord_subsumes(o, &o->C[v->a[i]], d)) return 1;
    return 0;
}
/* add the clause (hh, nb, lit under B) unless a variant exists or an active clause subsumes it */
static void ord_add(ord *o, int hh, int nb, int **lit, const int *B, int p1, int p2, int rule) {
    int *t1[130], *t2[130], nv;
    if (nb + hh > 128) return;
    if (!ord_canon(hh, nb, lit, B, t1, &nv)) return;
    int **use = t1;
    int sel = nb ? ord_elig(o, hh, nb, t1) : -1;
    if (sel > 0) {
        int *tmp[130]; int j = 0; if (hh) tmp[j++] = t1[0];
        tmp[j++] = t1[hh + sel]; for (int i = 0; i < nb; i++) if (i != sel) tmp[j++] = t1[hh + i];
        if (!ord_canon(hh, nb, tmp, NULL, t2, &nv)) { for (int i = 0; i < nb + hh; i++) free(t1[i]); return; }
        for (int i = 0; i < nb + hh; i++) free(t1[i]);
        use = t2; sel = 0;
    }
    uint64_t h = hatoms(hh, nb, use);
    long slot = (long)(h % (uint64_t)o->HTC);
    while (o->HT[slot] >= 0) { if (o->C[o->HT[slot]].h == h && ord_same(&o->C[o->HT[slot]], hh, nb, use)) { for (int i = 0; i < nb + hh; i++) free(use[i]); return; } slot = (slot + 1) % o->HTC; }
    ocl c = { nb, hh, sel, 0, nv, NULL, p1, p2, rule, h };
    c.lit = xmalloc((nb + hh + 1) * sizeof(int *)); memcpy(c.lit, use, (nb + hh) * sizeof(int *));
    if (ord_subsumed(o, &c, -1)) { for (int i = 0; i < nb + hh; i++) free(use[i]); free(c.lit); return; }
    int w = nb;
    for (int i = 0; i < nb + hh; i++) for (int k = 1; k < alen(use[i]); k++) if (use[i][k] >= 0) w++;
    c.w = w;
    if (o->NC == o->CC) { o->CC = o->CC ? o->CC * 2 : 1024; o->C = xrealloc(o->C, o->CC * sizeof(ocl)); }
    int id = o->NC++; o->C[id] = c;
    o->HT[slot] = id; o->HTN++;
    if (o->HTN * 2 > o->HTC) {   /* grow the dedup table */
        long nc = o->HTC * 2; int *nt = xmalloc(nc * sizeof(int)); for (long i = 0; i < nc; i++) nt[i] = -1;
        for (int i = 0; i < o->NC; i++) { long s = (long)(o->C[i].h % (uint64_t)nc); while (nt[s] >= 0) s = (s + 1) % nc; nt[s] = i; }
        free(o->HT); o->HT = nt; o->HTC = nc;
    }
    ord_heap_push(o, w, id);
}
static void ord_init(ord *o, int dir) {
    memset(o, 0, sizeof *o); o->dir = dir;
    o->HTC = 1 << 12; o->HT = xmalloc(o->HTC * sizeof(int)); for (long i = 0; i < o->HTC; i++) o->HT[i] = -1;
    o->SKC = 4099; o->SK = xmalloc(o->SKC * sizeof(ivec)); memset(o->SK, 0, o->SKC * sizeof(ivec));
    o->NP = NPAR; o->BYH = xmalloc((o->NP + 1) * sizeof(ivec)); o->BYS = xmalloc((o->NP + 1) * sizeof(ivec));
    memset(o->BYH, 0, (o->NP + 1) * sizeof(ivec)); memset(o->BYS, 0, (o->NP + 1) * sizeof(ivec));
    for (int i = 0; i < 2 * MAXV; i++) o->B[i] = UNB;
    for (int i = 0; i < MAXV; i++) o->M[i] = UNB;
    o->refuted = -1;
    for (int r = 0; r < NR; r++) {
        rule *ru = &R[r]; int j = 0;
        if (ru->nb + ru->has_head > 128 || ru->nvars > MAXV / 2 - 1) { o->done = 1; return; }
        int *tmp[130];
        if (ru->has_head) { int *a = xmalloc((1 + ru->head.ar) * sizeof(int)); a[0] = ru->head.pred; memcpy(a + 1, ru->head.args, ru->head.ar * sizeof(int)); tmp[j++] = a; }
        for (int i = 0; i < ru->nb; i++) { int *a = xmalloc((1 + ru->body[i].ar) * sizeof(int)); a[0] = ru->body[i].pred; memcpy(a + 1, ru->body[i].args, ru->body[i].ar * sizeof(int)); tmp[j++] = a; }
        ord_add(o, ru->has_head, ru->nb, tmp, NULL, -1, -1, r);
        for (int i = 0; i < j; i++) free(tmp[i]);
    }
}
/* rename clause d's vars by +off into fresh copies */
static void ord_ren(const ocl *d, int off, int **out) {
    for (int i = 0; i < d->nb + d->hh; i++) { out[i] = adup(d->lit[i]); for (int k = 1; k < alen(out[i]); k++) if (out[i][k] < 0) out[i][k] -= off; }
}
static void ord_resolve(ord *o, int gi, int xi, int head_side) {
    /* head_side: the given clause gi supplies the eligible head, xi the selected literal; else reverse */
    int hc = head_side ? gi : xi, sc = head_side ? xi : gi;
    ocl *H = &o->C[hc], *S = &o->C[sc];
    int *hl[130], *sl[130], nh = H->nb + H->hh, ns = S->nb + S->hh;
    ord_ren(H, 0, hl); ord_ren(S, MAXV / 2, sl);
    int nt = 0;
    if (unify_at(hl[0], sl[S->hh], o->B, o->trail, &nt)) {
        o->res++;
        int *lit[260]; int j = 0, hh = S->hh, nb = H->nb + S->nb - 1;
        if (hh) lit[j++] = sl[0];
        for (int i = 0; i < H->nb; i++) lit[j++] = hl[1 + i];
        for (int i = 1; i < S->nb; i++) lit[j++] = sl[S->hh + i];
        ord_add(o, hh, nb, lit, o->B, hc, sc, -1);
    }
    undo(o->B, o->trail, 0, &nt);
    for (int i = 0; i < nh; i++) free(hl[i]);
    for (int i = 0; i < ns; i++) free(sl[i]);
}
static void ord_run(ord *o, double deadline) {
    long it = 0;
    while (!o->done && o->refuted < 0) {
        if (!o->NH) { o->done = 1; break; }
        if ((++it & 15) == 0 && now_s() > deadline) return;
        hent e = ord_heap_pop(o); int g = e.c; ocl *G = &o->C[g];
        if (!G->nb && !G->hh) { o->refuted = g; return; }
        if (ord_subsumed(o, G, g)) continue;
        ipush(&o->SK[ord_skey(G->hh, G->nb, G->lit, o->SKC)], g);
        o->given++;
        if (G->sel < 0) {
            int p = G->lit[0][0]; int n = o->BYS[p].n;
            for (int i = 0; i < n && o->refuted < 0; i++) ord_resolve(o, g, o->BYS[p].a[i], 1);
            ipush(&o->BYH[p], g);
        } else {
            int p = G->lit[G->hh][0]; int n = o->BYH[p].n;
            for (int i = 0; i < n && o->refuted < 0; i++) ord_resolve(o, g, o->BYH[p].a[i], 0);
            ipush(&o->BYS[p], g);
        }
        if (o->NC > 4000000) { o->done = 1; return; }
    }
}
static void put_atom_json(FILE *f, const int *a) {
    fputc('[', f); put_json_str(f, SY.s[a[0]]);
    for (int k = 1; k < alen(a); k++) { fputc(',', f); if (a[k] >= 0) put_json_str(f, SY.s[a[k]]); else fprintf(f, "\"X%d\"", -a[k] - 1); }
    fputc(']', f);
}
/* resolution proof: every clause the refutation rests on, premises before conclusions */
static long ord_proof(ord *o, FILE *f) {
    char *need = xmalloc(o->NC); memset(need, 0, o->NC);
    int *st = xmalloc((o->NC + 1) * sizeof(int)); int sp = 0; st[sp++] = o->refuted; need[o->refuted] = 1;
    while (sp) { int c = st[--sp]; int ps[2] = { o->C[c].p1, o->C[c].p2 }; for (int k = 0; k < 2; k++) if (ps[k] >= 0 && !need[ps[k]]) { need[ps[k]] = 1; st[sp++] = ps[k]; } }
    long n = 0;
    if (f) fputc('[', f);
    for (int c = 0; c < o->NC; c++) if (need[c]) {   /* ids grow with derivation order */
        ocl *C = &o->C[c];
        if (f) {
            if (n) fputc(',', f);
            fprintf(f, "{\"id\":%d,\"head\":", c);
            if (C->hh) put_atom_json(f, C->lit[0]); else fputs("null", f);
            fputs(",\"body\":[", f);
            for (int i = 0; i < C->nb; i++) { if (i) fputc(',', f); put_atom_json(f, C->lit[C->hh + i]); }
            fputs("],", f);
            if (C->rule >= 0) { fputs("\"input\":", f); put_json_str(f, SY.s[R[C->rule].name]); }
            else fprintf(f, "\"from\":[%d,%d]", C->p1, C->p2);
            fputc('}', f);
        }
        n++;
    }
    if (f) fputs("]\n", f);
    free(need); free(st);
    return n;
}

/* ---------------- EQB */
typedef struct { int *a; int rule; int np; int **prem; } sfact;            /* side fact with provenance */
typedef struct { int *st; int ns; int **side; int *head; int rule; } srule;
typedef struct { int *l, *r; int rule, back; } rwr;                       /* l -> r is rule `rule`; r -> l is rule `back` */
typedef struct { int *a; int parent; int rule; int np; int **prem; } fnode; /* forward state; prem = side facts */
typedef struct { int *nf; int *raw; int parent; int rule; int np; int **prem; int nrw; int *rw; int goalclause; } gnode;
typedef struct { uint64_t mask; int *tab; long cap, n; } mgroup;
typedef struct {
    int on, done, orient, refuted_f, refuted_g, meet_ok;
    char *isS;
    sfact *E; int NE, CE; int *EH; long EHC;        /* side facts and their hash set */
    srule *SR; int NSR;
    rwr *RW; int NRW;
    fnode *FN; int NFN, CFN; int *FH; long FHC, FHN;  /* forward nodes; hash over normalized states */
    gnode *GN; int NGN, CGN; int *GH; long GHC, GHN;
    mgroup *MG; int NMG;
    int *ff; long nff; int *gf; long ngf;            /* frontiers */
    int B[2 * MAXV], M[MAXV], trail[4 * MAXV], mtr[4 * MAXV];
    long steps; int tnt; ivec *EP; srule *SRR; int *allst; long nall; long fcur, gcur; int *nfr; long nnfr;
} eqb;

static uint64_t hatom(const int *a) { uint64_t h = 1469598103934665603ULL; for (int k = 0; k < alen(a); k++) h = (h ^ (uint64_t)(unsigned)a[k]) * 1099511628211ULL; return h; }
static int aeq(const int *a, const int *b) { return a[0] == b[0] && !memcmp(a, b, alen(a) * sizeof(int)); }
static int aground(const int *a) { for (int k = 1; k < alen(a); k++) if (a[k] < 0) return 0; return 1; }
/* generic open-addressing set of ids keyed by an atom getter */
static int hs_find(int *tab, long cap, const int *a, int *(*get)(void *, int), void *ctx, long *slot) {
    long s = (long)(hatom(a) % (uint64_t)cap);
    while (tab[s] >= 0) { if (aeq(get(ctx, tab[s]), a)) { *slot = s; return tab[s]; } s = (s + 1) % cap; }
    *slot = s; return -1;
}
static int *get_e(void *c, int i) { return ((eqb *)c)->E[i].a; }
static int *get_f(void *c, int i) { return ((eqb *)c)->FN[i].a; }
static int *get_g(void *c, int i) { return ((eqb *)c)->GN[i].nf; }
static int *hs_grow(int *tab, long *cap, long n, int *(*get)(void *, int), void *ctx, int total) {
    if (n * 2 <= *cap) return tab;
    long nc = *cap * 2; int *nt = xmalloc(nc * sizeof(int)); for (long i = 0; i < nc; i++) nt[i] = -1;
    for (long i = 0; i < *cap; i++) if (tab[i] >= 0) { const int *a = get(ctx, tab[i]); long s = (long)(hatom(a) % (uint64_t)nc); while (nt[s] >= 0) s = (s + 1) % nc; nt[s] = tab[i]; }
    (void)total; free(tab); *cap = nc; return nt;
}
static int *atom_of(const atom *x) { int *a = xmalloc((1 + x->ar) * sizeof(int)); a[0] = x->pred; memcpy(a + 1, x->args, x->ar * sizeof(int)); return a; }
static int *subst(const int *a, const int *B) { int *b = adup(a); for (int k = 1; k < alen(b); k++) b[k] = walkt(b[k], B); return b; }
static int *canon1(const int *a) { int map[2 * MAXV]; memset(map, 0, sizeof map); int nv = 0; int *b = adup(a);
    for (int k = 1; k < alen(b); k++) if (b[k] < 0) { int v = -b[k] - 1; if (!map[v]) map[v] = ++nv; b[k] = -map[v]; } return b; }
static int *renoff(const int *a, int off) { int *b = adup(a); for (int k = 1; k < alen(b); k++) if (b[k] < 0) b[k] -= off; return b; }

static int eqb_add_side(eqb *q, int *a, int rule, int np, int **prem) {
    long slot; if (hs_find(q->EH, q->EHC, a, get_e, q, &slot) >= 0) { free(a); return 0; }
    if (q->NE == q->CE) { q->CE = q->CE ? q->CE * 2 : 256; q->E = xrealloc(q->E, q->CE * sizeof(sfact)); }
    int id = q->NE++; q->E[id].a = a; q->E[id].rule = rule; q->E[id].np = np;
    q->E[id].prem = np ? xmalloc(np * sizeof(int *)) : NULL; if (np) memcpy(q->E[id].prem, prem, np * sizeof(int *));
    q->EH[slot] = id; q->EH = hs_grow(q->EH, &q->EHC, q->NE, get_e, q, q->NE);
    ipush(&q->EP[a[0]], id);
    return 1;
}
/* enumerate side facts for side[i..] under B; calls cb for each complete binding */
typedef void (*side_cb)(eqb *, void *, int **);
static void eqb_sides(eqb *q, int **side, int ns, int i, int **chosen, side_cb cb, void *ctx) {
    if (i == ns) { cb(q, ctx, chosen); return; }
    int *pat = side[i];
    ivec *v = &q->EP[pat[0]];
    for (int j = 0; j < v->n; j++) {
        int e = v->a[j]; int from = q->tnt;
        if (unify_at(pat, q->E[e].a, q->B, q->trail, &q->tnt)) { chosen[i] = q->E[e].a; eqb_sides(q, side, ns, i + 1, chosen, cb, ctx); }
        undo(q->B, q->trail, from, &q->tnt);
    }
}
static void canon2(const int *a, const int *b, int **oa, int **ob) {
    int map[2 * MAXV]; memset(map, 0, sizeof map); int nv = 0;
    int *x = adup(a), *y = adup(b);
    int *both[2] = { x, y };
    for (int i = 0; i < 2; i++) for (int k = 1; k < alen(both[i]); k++) if (both[i][k] < 0) { int v = -both[i][k] - 1; if (!map[v]) map[v] = ++nv; both[i][k] = -map[v]; }
    *oa = x; *ob = y;
}
static int samevars(const int *a, const int *b) {
    for (int k = 1; k < alen(a); k++) if (a[k] < 0) { int f = 0; for (int j = 1; j < alen(b); j++) if (b[j] == a[k]) f = 1; if (!f) return 0; }
    for (int k = 1; k < alen(b); k++) if (b[k] < 0) { int f = 0; for (int j = 1; j < alen(a); j++) if (a[j] == b[k]) f = 1; if (!f) return 0; }
    return 1;
}
/* rewrite to normal form; records the rewrite rules used (into rec, up to cap) */
static int *eqb_norm(eqb *q, const int *a0, int *rec, int *nrec, int cap) {
    int *a = adup(a0); *nrec = 0;
    for (int step = 0; step < 100000; step++) {
        int hit = -1;
        for (int i = 0; i < q->NRW && hit < 0; i++) {
            int nt = 0;
            if (match_at(q->RW[i].l, a, q->M, q->mtr, &nt)) {
                int *b = adup(q->RW[i].r); for (int k = 1; k < alen(b); k++) if (b[k] < 0) b[k] = q->M[-b[k] - 1];
                undo(q->M, q->mtr, 0, &nt);
                if (aeq(a, b)) { free(b); continue; }
                free(a); a = b; hit = i;
            } else undo(q->M, q->mtr, 0, &nt);
        }
        if (hit < 0) break;
        if (*nrec < cap) rec[(*nrec)++] = hit; else break;
    }
    return a;
}
static int eqb_fnode(eqb *q, int *a, int parent, int rule, int np, int **prem) {
    if (q->NFN == q->CFN) { q->CFN = q->CFN ? q->CFN * 2 : 1024; q->FN = xrealloc(q->FN, q->CFN * sizeof(fnode)); }
    int id = q->NFN++; q->FN[id].a = a; q->FN[id].parent = parent; q->FN[id].rule = rule; q->FN[id].np = np;
    q->FN[id].prem = np ? xmalloc(np * sizeof(int *)) : NULL; if (np) memcpy(q->FN[id].prem, prem, np * sizeof(int *));
    return id;
}
static long eqb_mkey(const int *a, uint64_t mask) {
    uint64_t h = (uint64_t)a[0] * 0x9E3779B97F4A7C15ULL;
    for (int k = 1; k < alen(a); k++) if (!(mask >> ((k - 1) & 63) & 1)) h = (h ^ (uint64_t)(unsigned)a[k]) * 1099511628211ULL;
    return (long)(h >> 1);
}
static void eqb_meet_index(eqb *q, int g) {
    const int *a = q->GN[g].nf; uint64_t m = 0;
    for (int k = 1; k < alen(a); k++) if (a[k] < 0) m |= 1ULL << ((k - 1) & 63);
    mgroup *G = NULL;
    for (int i = 0; i < q->NMG; i++) if (q->MG[i].mask == m) G = &q->MG[i];
    if (!G) { q->MG = xrealloc(q->MG, (q->NMG + 1) * sizeof(mgroup)); G = &q->MG[q->NMG++]; G->mask = m; G->cap = 64; G->n = 0; G->tab = xmalloc(64 * sizeof(int)); for (int i = 0; i < 64; i++) G->tab[i] = -1; }
    if ((G->n + 1) * 2 > G->cap) {
        long nc = G->cap * 2; int *nt = xmalloc(nc * sizeof(int)); for (long i = 0; i < nc; i++) nt[i] = -1;
        for (long i = 0; i < G->cap; i++) if (G->tab[i] >= 0) { long s = eqb_mkey(q->GN[G->tab[i]].nf, m) % nc; while (nt[s] >= 0) s = (s + 1) % nc; nt[s] = G->tab[i]; }
        free(G->tab); G->tab = nt; G->cap = nc;
    }
    long s = eqb_mkey(a, m) % G->cap; while (G->tab[s] >= 0) s = (s + 1) % G->cap; G->tab[s] = g; G->n++;
}
/* goal matching the ground state, or -1 */
static int eqb_meet_fact(eqb *q, const int *f) {
    for (int i = 0; i < q->NMG; i++) {
        mgroup *G = &q->MG[i]; long s = eqb_mkey(f, G->mask) % G->cap;
        while (G->tab[s] >= 0) { int g = G->tab[s]; int nt = 0;
            int ok = match_at(q->GN[g].nf, f, q->M, q->mtr, &nt); undo(q->M, q->mtr, 0, &nt);
            if (ok) return g; s = (s + 1) % G->cap; }
    }
    return -1;
}
static int eqb_add_goal(eqb *q, int *raw, int parent, int rule, int np, int **prem, int gc) {
    int rec[4096], nrec; int *n0 = eqb_norm(q, raw, rec, &nrec, 4096); int *nf = canon1(n0); free(n0);
    long slot; if (hs_find(q->GH, q->GHC, nf, get_g, q, &slot) >= 0) { free(nf); free(raw); return -1; }
    if (q->NGN == q->CGN) { q->CGN = q->CGN ? q->CGN * 2 : 1024; q->GN = xrealloc(q->GN, q->CGN * sizeof(gnode)); }
    int id = q->NGN++; gnode *g = &q->GN[id];
    g->nf = nf; g->raw = raw; g->parent = parent; g->rule = rule; g->np = np; g->goalclause = gc;
    g->prem = np ? xmalloc(np * sizeof(int *)) : NULL; if (np) memcpy(g->prem, prem, np * sizeof(int *));
    g->nrw = nrec; g->rw = nrec ? xmalloc(nrec * sizeof(int)) : NULL; if (nrec) memcpy(g->rw, rec, nrec * sizeof(int));
    q->GH[slot] = id; q->GHN++; q->GH = hs_grow(q->GH, &q->GHC, q->GHN, get_g, q, q->NGN);
    eqb_meet_index(q, id);
    if (aground(nf)) {   /* a ground goal meets a state only if that very state was reached */
        long s2; int f = hs_find(q->FH, q->FHC, nf, get_f, q, &s2);
        if (f >= 0 && q->refuted_g < 0) { q->refuted_f = f; q->refuted_g = id; }
    } else
    for (long i = 0; i < q->nall && q->refuted_g < 0; i++) {     /* against every state seen so far */
        int f = q->allst[i];
        int nt = 0; int ok = match_at(nf, q->FN[f].a, q->M, q->mtr, &nt); undo(q->M, q->mtr, 0, &nt);
        if (ok) { q->refuted_f = f; q->refuted_g = id; }
    }
    q->gf = xrealloc(q->gf, (q->ngf + 1) * sizeof(int)); q->gf[q->ngf++] = id;
    return id;
}
/* new ground state: node chain for the raw head and each rewrite, kept only if its normal form is new */
static void eqb_add_state(eqb *q, int *raw, int parent, int rule, int np, int **prem) {
    int rec[4096], nrec; int *nf = eqb_norm(q, raw, rec, &nrec, 4096);
    long slot; if (hs_find(q->FH, q->FHC, nf, get_f, q, &slot) >= 0) { free(nf); free(raw); return; }
    int id = eqb_fnode(q, raw, parent, rule, np, prem);
    int *cur = adup(raw);
    for (int i = 0; i < nrec; i++) {   /* replay the rewrites as rule applications */
        rwr *w = &q->RW[rec[i]]; int nt = 0;
        match_at(w->l, cur, q->M, q->mtr, &nt);
        int *b = adup(w->r); for (int k = 1; k < alen(b); k++) if (b[k] < 0) b[k] = q->M[-b[k] - 1];
        undo(q->M, q->mtr, 0, &nt);
        free(cur); cur = b;
        id = eqb_fnode(q, adup(cur), id, w->rule, 0, NULL);
    }
    free(cur);
    free(q->FN[id].a); q->FN[id].a = nf;
    q->FH[slot] = id; q->FHN++; q->FH = hs_grow(q->FH, &q->FHC, q->FHN, get_f, q, q->NFN);
    q->ff = xrealloc(q->ff, (q->nff + 1) * sizeof(int)); q->ff[q->nff++] = id;
    q->allst = xrealloc(q->allst, (q->nall + 1) * sizeof(int)); q->allst[q->nall++] = id;
    if (q->refuted_g < 0) { int g = eqb_meet_fact(q, nf); if (g >= 0) { q->refuted_f = id; q->refuted_g = g; } }
}
typedef struct { int parent, rule, ns; const srule *r; int gc; } ectx;
static void fwd_cb(eqb *q, void *c, int **chosen) {
    ectx *x = c; int *h = subst(x->r->head, q->B);
    if (!aground(h)) { free(h); return; }
    eqb_add_state(q, h, x->parent, x->rule, x->ns, chosen);
}
static void bwd_cb(eqb *q, void *c, int **chosen) {
    ectx *x = c; int *st = (int *)x->r->st;   /* renamed copy passed via r */
    int *raw0 = subst(st, q->B); int *raw = canon1(raw0); free(raw0);
    int r = eqb_add_goal(q, raw, x->parent, x->rule, x->ns, chosen, x->gc);
}
static void sidesat_cb(eqb *q, void *c, int **chosen) {
    ectx *x = c; int *h = subst(x->r->head, q->B);
    if (!aground(h)) { free(h); return; }
    if (eqb_add_side(q, h, x->rule, x->ns, chosen)) q->steps++;
}
static void root_cb(eqb *q, void *c, int **chosen) {
    ectx *x = c; int *raw0 = subst(x->r->st, q->B); int *raw = canon1(raw0); free(raw0);
    eqb_add_goal(q, raw, -1, -1, x->ns, chosen, x->gc);
}
static void eqb_init(eqb *q, int orient) {
    memset(q, 0, sizeof *q); q->orient = orient; q->refuted_f = q->refuted_g = -1;
    for (int i = 0; i < 2 * MAXV; i++) q->B[i] = UNB;
    for (int i = 0; i < MAXV; i++) q->M[i] = UNB;
    q->EHC = q->FHC = q->GHC = 1024;
    q->EH = xmalloc(q->EHC * sizeof(int)); q->FH = xmalloc(q->FHC * sizeof(int)); q->GH = xmalloc(q->GHC * sizeof(int));
    for (long i = 0; i < 1024; i++) q->EH[i] = q->FH[i] = q->GH[i] = -1;
    q->EP = xmalloc((NPAR + 1) * sizeof(ivec)); memset(q->EP, 0, (NPAR + 1) * sizeof(ivec));
    char *rec = xmalloc(NPAR + 1); memset(rec, 0, NPAR + 1);
    q->isS = xmalloc(NPAR + 1); memset(q->isS, 0, NPAR + 1);
    for (int r = 0; r < NR; r++) if (R[r].has_head) for (int i = 0; i < R[r].nb; i++) if (R[r].body[i].pred == R[r].head.pred) rec[R[r].head.pred] = 1;
    for (int r = 0; r < NR; r++) if (!R[r].has_head) for (int i = 0; i < R[r].nb; i++) if (rec[R[r].body[i].pred]) q->isS[R[r].body[i].pred] = 1;
    int grow = 1;
    while (grow) { grow = 0;
        for (int r = 0; r < NR; r++) if (R[r].has_head && !q->isS[R[r].head.pred]) for (int i = 0; i < R[r].nb; i++) if (q->isS[R[r].body[i].pred]) { q->isS[R[r].head.pred] = 1; grow = 1; break; } }
    free(rec);
    int anyS = 0; for (int p = 0; p < NPAR; p++) if (q->isS[p]) anyS = 1;
    if (!anyS) { q->done = 1; return; }
    /* side facts and their closure under side rules */
    for (int r = 0; r < NR; r++) if (R[r].has_head && R[r].nb == 0 && !q->isS[R[r].head.pred]) {
        int *a = atom_of(&R[r].head); if (!aground(a)) { free(a); q->done = 1; return; }
        eqb_add_side(q, a, r, 0, NULL);
    }
    srule *side = NULL; int nside = 0;
    for (int r = 0; r < NR; r++) if (R[r].has_head && R[r].nb > 0 && !q->isS[R[r].head.pred]) {
        side = xrealloc(side, (nside + 1) * sizeof(srule)); srule *x = &side[nside++];
        x->rule = r; x->head = atom_of(&R[r].head); x->ns = R[r].nb; x->side = xmalloc(R[r].nb * sizeof(int *)); x->st = NULL;
        for (int i = 0; i < R[r].nb; i++) x->side[i] = atom_of(&R[r].body[i]);
    }
    for (int round = 0; round < 1000; round++) {
        long before = q->NE;
        for (int i = 0; i < nside; i++) { int *ch[64]; ectx c = { -1, side[i].rule, side[i].ns, &side[i], -1 }; if (side[i].ns > 64) { q->done = 1; return; } eqb_sides(q, side[i].side, side[i].ns, 0, ch, sidesat_cb, &c); }
        if (q->NE == before) break;
        if (q->NE > 1000000) { q->done = 1; return; }
    }
    /* state rules: exactly one state literal in the body */
    for (int r = 0; r < NR; r++) if (R[r].has_head && q->isS[R[r].head.pred]) {
        if (R[r].nb == 0) continue;
        int nst = 0; for (int i = 0; i < R[r].nb; i++) if (q->isS[R[r].body[i].pred]) nst++;
        if (nst != 1 || R[r].nvars > MAXV / 2 - 1 || R[r].nb > 64) { q->done = 1; return; }
        q->SR = xrealloc(q->SR, (q->NSR + 1) * sizeof(srule)); srule *x = &q->SR[q->NSR++];
        x->rule = r; x->head = atom_of(&R[r].head); x->side = xmalloc(R[r].nb * sizeof(int *)); x->ns = 0;
        for (int i = 0; i < R[r].nb; i++) { if (q->isS[R[r].body[i].pred]) x->st = atom_of(&R[r].body[i]); else x->side[x->ns++] = atom_of(&R[r].body[i]); }
    }
    q->SRR = xmalloc((q->NSR + 1) * sizeof(srule));
    for (int i = 0; i < q->NSR; i++) {
        srule *x = &q->SR[i], *y = &q->SRR[i]; *y = *x;
        y->st = renoff(x->st, MAXV / 2); y->head = renoff(x->head, MAXV / 2);
        y->side = xmalloc((x->ns + 1) * sizeof(int *)); for (int k = 0; k < x->ns; k++) y->side[k] = renoff(x->side[k], MAXV / 2);
    }
    /* equivalence pairs among side-free state rules */
    for (int i = 0; i < q->NSR; i++) if (!q->SR[i].ns) for (int j = i + 1; j < q->NSR; j++) if (!q->SR[j].ns) {
        int *a1, *b1, *a2, *b2;
        canon2(q->SR[i].st, q->SR[i].head, &a1, &b1); canon2(q->SR[j].head, q->SR[j].st, &a2, &b2);
        int v = aeq(a1, a2) && aeq(b1, b2) && samevars(q->SR[i].st, q->SR[i].head);
        free(a1); free(b1); free(a2); free(b2);
        if (!v || !orient) continue;
        q->RW = xrealloc(q->RW, (q->NRW + 1) * sizeof(rwr)); rwr *w = &q->RW[q->NRW++];
        if (orient > 0) { w->l = q->SR[i].st; w->r = q->SR[i].head; w->rule = q->SR[i].rule; w->back = q->SR[j].rule; }
        else { w->l = q->SR[j].st; w->r = q->SR[j].head; w->rule = q->SR[j].rule; w->back = q->SR[i].rule; }
    }
    /* goals with exactly one state literal */
    for (int r = 0; r < NR; r++) if (!R[r].has_head) {
        int nst = 0; for (int i = 0; i < R[r].nb; i++) if (q->isS[R[r].body[i].pred]) nst++;
        if (nst == 0) continue;
        if (nst != 1 || R[r].nb > 64) { q->done = 1; return; }
        srule x; x.rule = r; x.head = NULL; x.ns = 0; x.side = xmalloc(R[r].nb * sizeof(int *));
        for (int i = 0; i < R[r].nb; i++) { if (q->isS[R[r].body[i].pred]) x.st = atom_of(&R[r].body[i]); else x.side[x.ns++] = atom_of(&R[r].body[i]); }
        int *ch[64]; ectx c = { -1, -1, x.ns, &x, r };
        eqb_sides(q, x.side, x.ns, 0, ch, root_cb, &c);
    }
    /* state facts */
    for (int r = 0; r < NR && q->refuted_g < 0; r++) if (R[r].has_head && R[r].nb == 0 && q->isS[R[r].head.pred]) {
        int *a = atom_of(&R[r].head); if (!aground(a)) { free(a); q->done = 1; return; }
        eqb_add_state(q, a, -1, r, 0, NULL);
    }
    q->on = 1;
}
/* one bounded slice of layered bidirectional search: expand the smaller frontier layer */
static void eqb_run(eqb *q, double deadline) {
    long it = 0;
    while (!q->done && q->refuted_g < 0) {
        if (q->fcur == 0 && q->gcur == 0 && q->nnfr == 0) {
            /* choose a direction for this layer: frontier arrays are snapshots */
        }
        int fwd = q->nff && (q->nff <= q->ngf || !q->ngf);
        if (!q->nff && !q->ngf) { q->done = 1; break; }
        if (fwd) {
            int *layer = q->ff; long n = q->nff; q->ff = NULL; q->nff = 0;
            for (long i = 0; i < n && q->refuted_g < 0; i++) {
                if ((++it & 63) == 0 && now_s() > deadline) {   /* put the rest back for the next slice */
                    int *rest = xmalloc((n - i + q->nff + 1) * sizeof(int)); memcpy(rest, layer + i, (n - i) * sizeof(int));
                    memcpy(rest + (n - i), q->ff, q->nff * sizeof(int)); free(q->ff); q->ff = rest; q->nff += n - i; free(layer); return;
                }
                int f = layer[i]; const int *a = q->FN[f].a;
                for (int s = 0; s < q->NSR && q->refuted_g < 0; s++) {
                    srule *x = &q->SR[s]; int from = q->tnt;
                    if (unify_at(x->st, a, q->B, q->trail, &q->tnt)) { int *ch[64]; ectx c = { f, x->rule, x->ns, x, -1 }; eqb_sides(q, x->side, x->ns, 0, ch, fwd_cb, &c); }
                    undo(q->B, q->trail, from, &q->tnt);
                }
            }
            free(layer);
        } else {
            int *layer = q->gf; long n = q->ngf; q->gf = NULL; q->ngf = 0;
            for (long i = 0; i < n && q->refuted_g < 0; i++) {
                if ((++it & 63) == 0 && now_s() > deadline) {
                    int *rest = xmalloc((n - i + q->ngf + 1) * sizeof(int)); memcpy(rest, layer + i, (n - i) * sizeof(int));
                    memcpy(rest + (n - i), q->gf, q->ngf * sizeof(int)); free(q->gf); q->gf = rest; q->ngf += n - i; free(layer); return;
                }
                int g = layer[i];
                for (int s = 0; s < q->NSR && q->refuted_g < 0; s++) {
                    srule *x = &q->SRR[s]; int from = q->tnt;
                    if (unify_at(x->head, q->GN[g].nf, q->B, q->trail, &q->tnt)) { int *ch[64]; ectx c = { g, x->rule, x->ns, x, -1 }; eqb_sides(q, x->side, x->ns, 0, ch, bwd_cb, &c); }
                    undo(q->B, q->trail, from, &q->tnt);
                }
            }
            free(layer);
        }
        q->steps++;
        if (q->NFN > 20000000 || q->NGN > 20000000) { q->done = 1; return; }
    }
}
/* ---------------- EQB proof: ground steps in the format check.py reads */
static long PSTEPS;
static void put_ground(FILE *f, const int *a) {
    fputc('[', f); put_json_str(f, SY.s[a[0]]); fputs(",[", f);
    for (int k = 1; k < alen(a); k++) { if (k > 1) fputc(',', f); put_json_str(f, SY.s[a[k]]); }
    fputs("]]", f);
}
static void put_step(FILE *f, const int *a, int rule, const int *first, int np, int **prem) {
    if (f) {
        if (PSTEPS) fputc(',', f);
        fputc('[', f);
        if (a) put_ground(f, a); else fputs("[\"$false\",[]]", f);
        fputc(',', f); put_json_str(f, SY.s[R[rule].name]); fputs(",[", f);
        int c = 0;
        if (first) { put_ground(f, first); c++; }
        for (int i = 0; i < np; i++) { if (c++) fputc(',', f); put_ground(f, prem[i]); }
        fputs("]]", f);
    }
    PSTEPS++;
}
static void eqb_emit_side(eqb *q, char *em, const int *a, FILE *f) {
    long slot; int e = hs_find(q->EH, q->EHC, a, get_e, q, &slot);
    if (e < 0 || em[e]) return;
    for (int i = 0; i < q->E[e].np; i++) eqb_emit_side(q, em, q->E[e].prem[i], f);
    put_step(f, q->E[e].a, q->E[e].rule, NULL, q->E[e].np, q->E[e].prem);
    em[e] = 1;
}
static int *ground_head(const int *h, const int *B) {
    int *a = subst(h, B); int c0 = CONSTS.n ? CONSTS.a[0] : intern("c0");
    for (int k = 1; k < alen(a); k++) if (a[k] < 0) a[k] = c0;
    return a;
}
static long eqb_proof(eqb *q, FILE *f) {
    PSTEPS = 0; if (f) fputc('[', f);
    char *em = xmalloc(q->NE + 1); memset(em, 0, q->NE + 1);
    int *chain = xmalloc((q->NFN + 1) * sizeof(int)); int nc = 0;
    for (int x = q->refuted_f; x >= 0; x = q->FN[x].parent) chain[nc++] = x;
    for (int i = nc - 1; i >= 0; i--) {
        fnode *n = &q->FN[chain[i]];
        for (int k = 0; k < n->np; k++) eqb_emit_side(q, em, n->prem[k], f);
        /* the stored atom of a chain end is its normal form, which equals the replayed atom */
        put_step(f, n->a, n->rule, n->parent >= 0 ? q->FN[n->parent].a : NULL, n->np, n->prem);
    }
    free(chain);
    int *Y = adup(q->FN[q->refuted_f].a);
    int g = q->refuted_g;
    for (;;) {
        gnode *G = &q->GN[g];
        for (int i = G->nrw - 1; i >= 0; i--) {
            rule *rb = &R[q->RW[G->rw[i]].back]; int nt = 0;
            int *body = atom_of(&rb->body[0]); int *head = atom_of(&rb->head);
            match_at(body, Y, q->M, q->mtr, &nt);
            int *h2 = adup(head); for (int k = 1; k < alen(h2); k++) if (h2[k] < 0) h2[k] = q->M[-h2[k] - 1] == UNB ? (CONSTS.n ? CONSTS.a[0] : 0) : q->M[-h2[k] - 1];
            undo(q->M, q->mtr, 0, &nt);
            put_step(f, h2, q->RW[G->rw[i]].back, Y, 0, NULL);
            free(body); free(head); free(Y); Y = h2;
        }
        for (int k = 0; k < G->np; k++) eqb_emit_side(q, em, G->prem[k], f);
        if (G->parent < 0) { put_step(f, NULL, G->goalclause, Y, G->np, G->prem); break; }
        srule *s = NULL; for (int i = 0; i < q->NSR; i++) if (q->SR[i].rule == G->rule) s = &q->SR[i];
        int from = q->tnt;
        unify_at(s->st, Y, q->B, q->trail, &q->tnt);
        for (int k = 0; k < s->ns; k++) unify_at(s->side[k], G->prem[k], q->B, q->trail, &q->tnt);
        int *h = ground_head(s->head, q->B);
        undo(q->B, q->trail, from, &q->tnt);
        put_step(f, h, s->rule, Y, G->np, G->prem);
        free(Y); Y = h; g = G->parent;
    }
    free(Y); free(em);
    if (f) fputs("]\n", f);
    return PSTEPS;
}
