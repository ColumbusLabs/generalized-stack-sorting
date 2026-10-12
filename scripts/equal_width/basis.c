/* Exhaustive basis computation for the class of inputs sortable by one
   generalized (r,s)-stack (top first; push next input at slot < r and <= height;
   pop slot < s; no bypass; unbounded capacity unless CAP given).
   For n = 1..N: S_n = sortable perms of length n (bitset by lexicographic rank),
   B_n = perms not in S_n all of whose one-point deletions (standardized) are in S_{n-1}.
   Usage: basis r s N [cap] [outprefix] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>

static int R, S, N, CAP;
static uint64_t fact[21];

/* ---------- sortability with forced pops, dead-state pruning, failure memo ---------- */
#define HBITS 18
#define HSIZE (1u<<HBITS)
typedef struct { uint64_t key[HSIZE]; uint32_t gen[HSIZE]; uint32_t cur; } Memo;

static inline uint64_t hmix(uint64_t x){ x ^= x>>33; x *= 0xff51afd7ed558ccdULL; x ^= x>>33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x>>33; return x; }
static inline int memo_has(Memo *m, uint64_t k){ uint32_t h = (uint32_t)hmix(k) & (HSIZE-1);
  for(int t=0;t<64;t++){ uint32_t j=(h+t)&(HSIZE-1); if(m->gen[j]!=m->cur) return 0; if(m->key[j]==k) return 1; } return 0; }
static inline void memo_add(Memo *m, uint64_t k){ uint32_t h = (uint32_t)hmix(k) & (HSIZE-1);
  for(int t=0;t<64;t++){ uint32_t j=(h+t)&(HSIZE-1); if(m->gen[j]!=m->cur){ m->gen[j]=m->cur; m->key[j]=k; return; } if(m->key[j]==k) return; } }

typedef struct { const int *p; int n; Memo *m; } Ctx;

/* stack st[0..h-1], st[0] = top. values 1..n. i = next input index. */
static int visit(Ctx *c, int i, int *st, int h){
  int out = i - h + 1;
  /* forced pops of the next required output */
  int again = 1; int buf[32]; memcpy(buf, st, sizeof(int)*h); st = buf;
  while(again){ again = 0;
    for(int k=0;k<h && k<S;k++) if(st[k]==out){ memmove(st+k, st+k+1, sizeof(int)*(h-k-1)); h--; out++; again=1; break; } }
  if(i==c->n && h==0) return 1;
  if(i==c->n) return 0;
  if(CAP && h>=CAP) return 0;
  uint64_t key = (uint64_t)i;
  for(int k=0;k<h;k++) key = (key<<4) | (uint64_t)st[k];
  key = (key<<4) | (uint64_t)h;   /* h <= 15 assumed (n <= 15) */
  if(memo_has(c->m, key)) return 0;
  int x = c->p[i];
  int lim = h < R-1 ? h : R-1;
  int ns[32];
  for(int j=0;j<=lim;j++){
    /* dead check: tokens below slot j (st[j..h-1]) smaller than x gain a larger token above */
    int dead = 0;
    for(int k=j;k<h && !dead;k++){ if(st[k] < x){ int cnt=1; for(int t=0;t<k;t++) if(st[t]>st[k]) cnt++; if(cnt>=S) dead=1; } }
    if(dead) continue;
    memcpy(ns, st, sizeof(int)*j); ns[j]=x; memcpy(ns+j+1, st+j, sizeof(int)*(h-j));
    if(visit(c, i+1, ns, h+1)) return 1;
  }
  memo_add(c->m, key);
  return 0;
}

static int sortable(const int *p, int n, Memo *m){
  m->cur++; if(m->cur==0){ memset(m->gen,0,sizeof(m->gen)); m->cur=1; }
  Ctx c = {p, n, m}; int st[1];
  return visit(&c, 0, st, 0);
}

/* ---------- ranks ---------- */
static uint64_t rank_of(const int *p, int n){ /* values 1..n, lexicographic rank */
  uint64_t r=0; for(int i=0;i<n;i++){ int c=0; for(int j=i+1;j<n;j++) if(p[j]<p[i]) c++; r += c*fact[n-1-i]; } return r; }

static void unrank(uint64_t r, int n, int *p){
  int used[32]={0};
  for(int i=0;i<n;i++){ uint64_t f=fact[n-1-i]; int c=(int)(r/f); r%=f;
    for(int v=1;v<=n;v++) if(!used[v]){ if(c==0){ p[i]=v; used[v]=1; break; } c--; } }
}

static int next_perm(int *a, int n){
  int i=n-2; while(i>=0 && a[i]>a[i+1]) i--; if(i<0) return 0;
  int j=n-1; while(a[j]<a[i]) j--; int t=a[i]; a[i]=a[j]; a[j]=t;
  for(int l=i+1,rr=n-1;l<rr;l++,rr--){ t=a[l]; a[l]=a[rr]; a[rr]=t; } return 1;
}

static inline int bit_get(const uint64_t *b, uint64_t i){ return (b[i>>6]>>(i&63))&1; }
static inline void bit_set(uint64_t *b, uint64_t i){ __atomic_fetch_or(&b[i>>6], 1ULL<<(i&63), __ATOMIC_RELAXED); }

int main(int argc, char **argv){
  if(argc<4){ fprintf(stderr,"usage: basis r s N [cap] [outprefix]\n"); return 2; }
  R=atoi(argv[1]); S=atoi(argv[2]); N=atoi(argv[3]); CAP = argc>4 ? atoi(argv[4]) : 0;
  const char *pref = argc>5 ? argv[5] : NULL;
  if(N>14){ fprintf(stderr,"N too large\n"); return 2; }
  fact[0]=1; for(int i=1;i<=20;i++) fact[i]=fact[i-1]*i;
  uint64_t *prev = calloc(1,8); prev[0]=1; /* S_0 = {empty} */
  printf("# (r,s)=(%d,%d) cap=%d N=%d threads=%d\n", R,S,CAP,N,omp_get_max_threads());
  for(int n=1;n<=N;n++){
    double t0=omp_get_wtime();
    uint64_t total=fact[n], words=(total+63)/64;
    uint64_t *cur = calloc(words,8);
    if(!cur){ fprintf(stderr,"alloc failed\n"); return 3; }
    uint64_t cls=0, bas=0, cand=0;
    FILE *bf=NULL; char fn[512];
    if(pref){ snprintf(fn,sizeof fn,"%s-r%ds%d-n%d.txt",pref,R,S,n); bf=fopen(fn,"w"); }
    /* chunk by first two entries for load balance */
    int chunks = n>=2 ? n*(n-1) : 1;
    #pragma omp parallel reduction(+:cls,bas,cand)
    {
      Memo *m = calloc(1,sizeof(Memo));
      #pragma omp for schedule(dynamic,1)
      for(int ch=0; ch<chunks; ch++){
        int p[32], q[32], code[32];
        uint64_t start, count;
        if(n>=2){ int a=ch/(n-1), b=ch%(n-1); start = a*fact[n-1] + b*fact[n-2]; count = fact[n-2]; }
        else { start=0; count=1; }
        unrank(start,n,p);
        for(uint64_t t=0;t<count;t++){
          uint64_t rk = start+t;
          /* Lehmer code */
          for(int i=0;i<n;i++){ int c=0; for(int j=i+1;j<n;j++) if(p[j]<p[i]) c++; code[i]=c; }
          int ok=1;
          for(int d=0; d<n && ok; d++){
            int v=p[d]; uint64_t r2=0; int idx=0;
            for(int i=0;i<n;i++){ if(i==d) continue; int c=code[i] - (i<d && v<p[i] ? 1:0); r2 += (uint64_t)c*fact[n-2-idx]; idx++; }
            if(!bit_get(prev,r2)) ok=0;
          }
          if(ok){
            cand++;
            if(sortable(p,n,m)){ bit_set(cur,rk); cls++; }
            else { bas++;
              if(bf){
                #pragma omp critical
                { for(int i=0;i<n;i++) fprintf(bf,"%d%s",p[i],i<n-1?" ":"\n"); }
              }
            }
          }
          next_perm(p,n);
        }
      }
      free(m);
    }
    if(bf) fclose(bf);
    printf("n=%d class=%llu basis=%llu candidates=%llu time=%.2fs\n", n,(unsigned long long)cls,(unsigned long long)bas,(unsigned long long)cand, omp_get_wtime()-t0);
    fflush(stdout);
    free(prev); prev=cur;
  }
  return 0;
}
