/* N=4 (and N=3 verification) C4-bite census, fan-in-2 monotone model.
 *
 * Exact same semantics as census_c4bite.py (the shipped N=3 census):
 *   - states: (avail-set of masks, junk-flag); avail = the set of monotone
 *     functions computed on some wire; each gate = AND or OR of exactly two
 *     available masks (pairs only: copies/constants never shorten a circuit);
 *   - flag turns true when an AND candidate fires at an edge-free assignment
 *     of the relation (cand & efmask != 0);
 *   - min = min depth with f in avail; min_junk = min depth with f in avail
 *     and flag; junk-at-min iff min_junk <= min.
 *
 * The avail-set graph is relation-independent: built ONCE, then each relation
 * runs a (setid, flag) BFS over it with epoch-stamped visited marks.  Cached
 * transitions carry (child set id, candidate mask id, isand) so the
 * per-relation loop is tight.
 *
 * Relations are processed in popcount order (1-edge relations first: the
 * risky class where junk comes closest to min), sharded by argv.
 *
 * Usage: census_n4 <N> <MAXD> <lo> <hi>      relation indices in popcount order
 *        census_n4 <N> <MAXD> list           print the relation order
 * Env:   CENSUS_NOBREAK=1  disable the early counterexample break
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int N, MAXD;
#define W4 4
typedef struct { uint64_t w[W4]; } M;

static M m_and(M a, M b){ M r; for (int i=0;i<W4;i++) r.w[i]=a.w[i]&b.w[i]; return r; }
static M m_or(M a, M b){ M r; for (int i=0;i<W4;i++) r.w[i]=a.w[i]|b.w[i]; return r; }
static int m_is0(M a){ return (a.w[0]|a.w[1]|a.w[2]|a.w[3])==0; }
static int m_eq(M a, M b){ return a.w[0]==b.w[0]&&a.w[1]==b.w[1]&&a.w[2]==b.w[2]&&a.w[3]==b.w[3]; }
static uint64_t m_hash(M a){ uint64_t h=1469598103934665603ULL; for (int i=0;i<W4;i++){ h^=a.w[i]; h*=1099511628211ULL; } return h; }

/* ---------- mask interning ---------- */
#define MASK_CAP  (1u<<22)
#define MASK_HT   (1u<<22)
static M        *masks;
static uint32_t mask_id[MASK_HT];   /* id+1, 0 empty */
static uint32_t nmask = 0;

static uint32_t m_intern(M a){
    uint64_t pos = (m_hash(a) * 0x9E3779B97F4A7C15ULL >> 41) & (MASK_HT-1);
    for (;;){
        uint32_t e = mask_id[pos];
        if (e == 0){ if (nmask >= MASK_CAP){ fprintf(stderr,"mask cap\n"); exit(3);} masks[nmask]=a; mask_id[pos]=nmask+1; return nmask++; }
        if (m_eq(masks[e-1], a)) return e-1;
        pos = (pos+1) & (MASK_HT-1);
    }
}

/* ---------- set interning (the avail-set graph) ---------- */
#define MAXW 14                    /* n + MAXD = 8 + 4 = 12, + slack */
#define SET_CAP  (1u<<23)
#define SET_HT   (1u<<24)
typedef struct { uint8_t len; uint32_t id[MAXW]; } SSet;
static SSet     *sets;
static uint32_t nset = 0;
static uint32_t set_ht[SET_HT];     /* id+1, 0 empty */
static uint32_t set_depth[SET_CAP];
static uint64_t set_xh[SET_CAP];    /* XOR of member mask hashes */

static uint32_t ss_intern(const uint32_t *ids, int len, uint8_t depth, uint64_t xh){
    uint64_t pos = (xh * 0x9E3779B97F4A7C15ULL >> 40) & (SET_HT-1);
    for (;;){
        uint32_t e = set_ht[pos];
        if (e == 0){
            if (nset >= SET_CAP){ fprintf(stderr,"set cap %u\n", nset); exit(4); }
            sets[nset].len=(uint8_t)len; memcpy(sets[nset].id, ids, sizeof(uint32_t)*(size_t)len);
            set_depth[nset]=depth; set_xh[nset]=xh; set_ht[pos]=nset+1; return nset++;
        }
        SSet *s = &sets[e-1];
        if (s->len==len){
            int same=1; for (int i=0;i<len;i++) if (s->id[i]!=ids[i]){ same=0; break; }
            if (same) return e-1;
        }
        pos = (pos+1) & (SET_HT-1);
    }
}
static uint32_t ss_find(const uint32_t *ids, int len, uint64_t xh){
    uint64_t pos = (xh * 0x9E3779B97F4A7C15ULL >> 40) & (SET_HT-1);
    for (;;){
        uint32_t e = set_ht[pos];
        if (e == 0) return UINT32_MAX;
        SSet *s = &sets[e-1];
        if (s->len==len){
            int same=1; for (int i=0;i<len;i++) if (s->id[i]!=ids[i]){ same=0; break; }
            if (same) return e-1;
        }
        pos = (pos+1) & (SET_HT-1);
    }
}

/* ---------- cached transitions ---------- */
typedef struct { uint32_t child; uint32_t cm; } TEnt;  /* cm = candmaskid*2 + isand */
typedef struct { uint32_t n; TEnt *ent; } Tran;
static Tran *trans;

/* ---------- graph-build queue (growable) ---------- */
typedef struct { uint32_t sid; uint8_t depth; } GEnt;
static GEnt *gq = 0; static size_t gqh, gqt, gqcap;

/* ---------- per-relation BFS queue ---------- */
typedef struct { uint32_t sid; uint8_t flag; uint8_t depth; } QEnt;
#define QCAP (1u<<22)
static QEnt *queue;

#define VHT (1u<<24)
static uint32_t v_epoch[VHT];
static uint32_t v_key[VHT];
static uint32_t cur_epoch = 0;

static int visited_mark(uint32_t sid, uint8_t flag){
    uint32_t key = sid*2 + flag;
    uint64_t pos = (((uint64_t)key)*0x9E3779B97F4A7C15ULL >> 40) & (VHT-1);
    for (;;){
        if (v_epoch[pos] != cur_epoch){ v_epoch[pos]=cur_epoch; v_key[pos]=key; return 1; }
        if (v_key[pos]==key) return 0;
        pos = (pos+1) & (VHT-1);
    }
}

static uint64_t mask_hash_id(uint32_t mid){ return m_hash(masks[mid]); }

/* ---------- relation helpers ---------- */
static M imask[8];
static M fmask_of(uint32_t bits, int *c4){
    M f; memset(&f,0,sizeof f);
    if (c4) *c4 = 0;
    for (int p=0;p<N;p++) for (int l=0;l<N;l++)
        if (bits & (1u << (p*N+l))) f = m_or(f, m_and(imask[p], imask[N+l]));
    if (c4) for (int p=0;p<N && !*c4;p++) for (int p2=p+1;p2<N && !*c4;p2++)
        for (int l=0;l<N && !*c4;l++) for (int l2=l+1;l2<N;l2++){
            int b1=(bits>>(p*N+l))&1, b2=(bits>>(p*N+l2))&1, b3=(bits>>(p2*N+l))&1, b4=(bits>>(p2*N+l2))&1;
            if (b1&&b2&&b3&&b4){ *c4=1; break; }
        }
    return f;
}
static M efmask_of(uint32_t bits){
    M e = fmask_of(bits, (int*)0);
    M r; for (int i=0;i<W4;i++) r.w[i] = ~e.w[i];
    if (N==3){ r.w[1]=0; r.w[2]=0; r.w[3]=0; }
    return r;
}

/* ---------- build the set graph once ---------- */
static void build_graph(void){
    uint32_t ids0[8];
    for (int i=0;i<2*N;i++) ids0[i] = m_intern(imask[i]);
    for (int i=0;i<2*N;i++) for (int j=i+1;j<2*N;j++) if (ids0[j]<ids0[i]){ uint32_t t=ids0[i];ids0[i]=ids0[j];ids0[j]=t; }
    uint64_t xh0=0; for (int i=0;i<2*N;i++) xh0 ^= mask_hash_id(ids0[i]);
    uint32_t s0 = ss_intern(ids0, 2*N, 0, xh0);
    gqcap = 1<<16; gq = malloc(sizeof(GEnt)*gqcap); gqh=gqt=0;
    gq[gqt++] = (GEnt){ s0, 0 };
    while (gqh < gqt){
        if (gqt + 4096 >= gqcap){ gqcap*=2; gq = realloc(gq, sizeof(GEnt)*gqcap); if(!gq){fprintf(stderr,"oom gq\n");exit(9);} }
        GEnt e = gq[gqh++];
        if (e.depth >= MAXD) continue;
        SSet *s = &sets[e.sid];
        uint32_t cand[13*13]; int nc = 0;
        for (int i=0;i<s->len;i++) for (int j=i+1;j<s->len;j++){
            uint32_t i1 = m_intern(m_and(masks[s->id[i]], masks[s->id[j]]));
            uint32_t i2 = m_intern(m_or (masks[s->id[i]], masks[s->id[j]]));
            cand[nc++] = i1*2+1; cand[nc++] = i2*2+0;
        }
        TEnt ent[13*13]; int nt = 0;
        for (int c=0;c<nc;c++){
            uint32_t mid = cand[c]>>1; int in=0;
            for (int i=0;i<s->len;i++) if (s->id[i]==mid){ in=1; break; }
            if (in) continue;
            uint32_t ids[MAXW]; int len = s->len+1, pos=0, placed=0;
            for (int i=0;i<s->len;i++){ while (!placed && mid < s->id[i]){ ids[pos++]=mid; placed=1; } ids[pos++]=s->id[i]; }
            if (!placed) ids[pos++]=mid;
            uint64_t xh = set_xh[e.sid] ^ mask_hash_id(mid);
            uint32_t ns = ss_find(ids, len, xh);
            if (ns == UINT32_MAX){
                ns = ss_intern(ids, len, e.depth+1, xh);
                gq[gqt++] = (GEnt){ ns, e.depth+1 };
            }
            ent[nt].child = ns; ent[nt].cm = mid*2 + (cand[c]&1); nt++;
        }
        trans[e.sid].n = nt;
        trans[e.sid].ent = malloc(sizeof(TEnt)*(size_t)(nt?nt:1));
        memcpy(trans[e.sid].ent, ent, sizeof(TEnt)*(size_t)nt);
    }
    size_t shallow=0; for (uint32_t i=0;i<nset;i++) if (set_depth[i] < MAXD) shallow++;
    fprintf(stderr,"# graph: %u sets, %u masks, expandable(depth<%d)=%zu\n", nset, nmask, MAXD, shallow);
}

/* ---------- per-relation BFS over the cached graph ---------- */
static int best_any, best_junk, nobreak;

static int set_contains(uint32_t sid, uint32_t mid){
    SSet *s = &sets[sid];
    uint32_t lo=0, hi=s->len;
    while (lo < hi){ uint32_t m=(lo+hi)>>1; if (s->id[m]==mid) return 1; if (s->id[m]<mid) lo=m+1; else hi=m; }
    return 0;
}

static void run_relation(uint32_t bits){
    int c4; M f = fmask_of(bits, &c4);
    M ef = efmask_of(bits);
    uint32_t fmaskid = m_intern(f);
    cur_epoch++;
    best_any = -1; best_junk = -1;
    size_t qh=0, qt=0;
    queue[qt++] = (QEnt){ 0, 0, 0 };
    visited_mark(0, 0);
    int found = 0;
    while (qh < qt){
        QEnt e = queue[qh++];
        Tran *t = &trans[e.sid];
        for (uint32_t c=0;c<t->n;c++){
            TEnt te = t->ent[c];
            uint8_t nflag = e.flag;
            if ((te.cm & 1u) && !m_is0(m_and(masks[te.cm >> 1], ef))) nflag = 1;
            if (visited_mark(te.child, nflag)){
                if (set_contains(te.child, fmaskid)){
                    uint8_t d = e.depth + 1;
                    if (best_any < 0 || d < best_any) best_any = d;
                    if (nflag && (best_junk < 0 || d < best_junk)) best_junk = d;
                }
                if (!nobreak && best_junk >= 0 && best_any >= 0 && best_junk <= best_any){ found=1; break; }
                if (e.depth + 1 < (uint8_t)MAXD){
                    queue[qt++] = (QEnt){ te.child, nflag, e.depth+1 };
                }
            }
        }
        if (found) break;
    }
    const char *tag = (best_junk>=0 && best_any>=0 && best_junk<=best_any) ? " JUNK-AT-MIN" : "";
    printf("relbits=%u c4=%d min=%d junk=%d%s\n", bits, c4, best_any, best_junk, tag);
    fflush(stdout);
}

/* ---------- relation order (popcount asc, then value) ---------- */
static int popc(uint32_t x){ int c=0; while(x){ c += x&1; x>>=1; } return c; }
static int cmp_rel(const void *a, const void *b){
    uint32_t x = *(const uint32_t*)a, y = *(const uint32_t*)b;
    int px = popc(x), py = popc(y);
    if (px!=py) return px<py?-1:1;
    return x<y?-1:1;
}

int main(int argc, char **argv){
    if (argc < 3){ fprintf(stderr,"usage: census_n4 N MAXD [lo hi|list]\n"); return 1; }
    N = atoi(argv[1]); MAXD = atoi(argv[2]);
    if (N != 3 && N != 4){ fprintf(stderr,"N must be 3 or 4\n"); return 1; }
    nobreak = getenv("CENSUS_NOBREAK") != 0;
    masks = malloc(sizeof(M)*MASK_CAP);
    sets  = malloc(sizeof(SSet)*SET_CAP);
    trans = calloc(SET_CAP, sizeof(Tran));
    queue = malloc(sizeof(QEnt)*QCAP);
    if(!masks||!sets||!trans||!queue){ fprintf(stderr,"oom\n"); return 2; }
    for (int i=0;i<2*N;i++){
        M m; memset(&m,0,sizeof m);
        for (uint32_t k=0;k<(1u<<(2*N));k++) if ((k>>i)&1) m.w[k/64] |= 1ULL<<(k%64);
        imask[i] = m;
    }
    build_graph();
    uint32_t nrel = 1u<<(N*N);
    uint32_t *order = malloc(sizeof(uint32_t)*nrel);
    for (uint32_t i=0;i<nrel;i++) order[i]=i;
    qsort(order, nrel, sizeof(uint32_t), cmp_rel);
    if (argc>=4 && strcmp(argv[3],"list")==0){
        for (uint32_t i=0;i<nrel;i++) printf("%u %u\n", i, order[i]);
        return 0;
    }
    uint32_t lo = argc>=5 ? (uint32_t)strtoul(argv[3],0,10) : 0;
    uint32_t hi = argc>=5 ? (uint32_t)strtoul(argv[4],0,10) : nrel;
    for (uint32_t i=lo;i<hi;i++) run_relation(order[i]);
    fprintf(stderr,"# done %u..%u\n", lo, hi);
    return 0;
}