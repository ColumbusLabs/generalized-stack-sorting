/* Check candidate generated-side basis elements of the (r,s)-stack.
   stdin: lines of a permutation p of 1..n (generated orientation).
   For pi = inverse(p): report whether pi is sortable and whether every
   one-point deletion (standardized) is sortable. Exact memo keys.
   Inputs must be permutations of 1..n with n <= MAXN-1 = 127; anything else
   is rejected with exit status 2 (no buffer is ever indexed past MAXN).
   Usage: check r s [cap] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int R,S,CAP;
#define MAXN 128
typedef struct { uint8_t len, i; uint8_t st[MAXN]; } Key;
static __thread Key *tab; static __thread uint8_t *used; static size_t tsize=1<<20; static __thread size_t tcount;
static uint64_t hk(const Key *k){ uint64_t h=1469598103934665603ULL^k->i^((uint64_t)k->len<<8);
  for(int j=0;j<k->len;j++){ h^=k->st[j]; h*=1099511628211ULL; } return h; }
static int keq(const Key *a,const Key *b){ return a->len==b->len && a->i==b->i && !memcmp(a->st,b->st,a->len); }
static void reset(void){ memset(used,0,tsize); tcount=0; }
static int has(const Key *k){ size_t j=hk(k)&(tsize-1); while(used[j]){ if(keq(&tab[j],k)) return 1; j=(j+1)&(tsize-1);} return 0; }
static void add(const Key *k){ if(tcount*2>tsize) return; size_t j=hk(k)&(tsize-1); while(used[j]){ if(keq(&tab[j],k)) return; j=(j+1)&(tsize-1);} used[j]=1; tab[j]=*k; tcount++; }
static __thread const int *P; static __thread int N;
static __thread long long nodes;
static int visit(int i, const int *st0, int h){
  int st[MAXN]; memcpy(st,st0,sizeof(int)*h); nodes++;
  int out=i-h+1, again=1;
  while(again){ again=0; for(int k=0;k<h&&k<S;k++) if(st[k]==out){ memmove(st+k,st+k+1,sizeof(int)*(h-k-1)); h--; out++; again=1; break; } }
  if(i==N) return h==0;
  if(CAP && h>=CAP) return 0;
  Key key; key.len=h; key.i=i; for(int k=0;k<h;k++) key.st[k]=st[k];
  if(has(&key)) return 0;
  int x=P[i], lim=h<R-1?h:R-1, ns[MAXN];
  for(int j=0;j<=lim;j++){
    int dead=0;
    for(int k=j;k<h&&!dead;k++) if(st[k]<x){ int c=1; for(int t=0;t<k;t++) if(st[t]>st[k]) c++; if(c>=S) dead=1; }
    if(dead) continue;
    memcpy(ns,st,sizeof(int)*j); ns[j]=x; memcpy(ns+j+1,st+j,sizeof(int)*(h-j));
    if(visit(i+1,ns,h+1)) return 1;
  }
  add(&key); return 0;
}
static int sortable(const int *p,int n){ P=p; N=n; reset(); int st[1]; return visit(0,st,0); }

#include <omp.h>
static int next_perm(int *a, int n){
  int i=n-2; while(i>=0 && a[i]>a[i+1]) i--; if(i<0) return 0;
  int j=n-1; while(a[j]<a[i]) j--; int t=a[i]; a[i]=a[j]; a[j]=t;
  for(int l=i+1,rr=n-1;l<rr;l++,rr--){ t=a[l]; a[l]=a[rr]; a[rr]=t; } return 1; }
static int is_basis(const int *p, int n){
  int pi[MAXN]; for(int i=0;i<n;i++) pi[p[i]-1]=i+1;
  if(sortable(pi,n)) return 0;
  for(int d=0; d<n; d++){ int q[MAXN], m=0, v=pi[p[d]-1];
    for(int i=0;i<n;i++) if(i!=p[d]-1) q[m++]= pi[i]>v ? pi[i]-1 : pi[i];
    if(!sortable(q,m)) return 0; }
  return 1; }
int main(int argc,char**argv){
  /* usage: psearch r s n v1,v2,...  (prefix of generated-side perm) */
  if(argc<5){ fprintf(stderr,"usage: psearch r s n v1,v2,...\n"); return 2; }
  R=atoi(argv[1]); S=atoi(argv[2]); int n=atoi(argv[3]); CAP=0;
  if(n<1 || n>MAXN-1){ fprintf(stderr,"n must be in 1..%d\n",MAXN-1); return 2; }
  int pre[MAXN], k=0; char *s=argv[4];
  while(*s){ char *e; long v=strtol(s,&e,10);
    if(e==s || k>=n || v<1 || v>n){ fprintf(stderr,"bad prefix\n"); return 2; }
    pre[k++]=(int)v; s=e; if(*s==',') s++; }
  int rest[MAXN], m=0, usedv[MAXN]={0};
  for(int i=0;i<k;i++){ if(usedv[pre[i]]){ fprintf(stderr,"repeated prefix value\n"); return 2; } usedv[pre[i]]=1; }
  for(int v=1; v<=n; v++) if(!usedv[v]) rest[m++]=v;
  long long found=0, tested=0;
  #pragma omp parallel reduction(+:found,tested)
  { tab=malloc(sizeof(Key)*tsize); used=malloc(tsize);
    #pragma omp for schedule(dynamic,1)
    for(int f=0; f<m; f++){
      int tail[MAXN], t=0; tail[t++]=rest[f]; for(int i=0;i<m;i++) if(i!=f) tail[t++]=rest[i];
      /* tail[1..] sorted ascending already */
      int p[MAXN]; for(int i=0;i<k;i++) p[i]=pre[i];
      do { for(int i=0;i<m;i++) p[k+i]=tail[i]; tested++;
           if(is_basis(p,n)){ found++;
             #pragma omp critical
             { for(int i=0;i<n;i++) printf("%d%c",p[i],i<n-1?' ':'\n'); fflush(stdout);} }
      } while(next_perm(tail+1,m-1));
    }
    free(tab); free(used); }
  fprintf(stderr,"tested=%lld found=%lld\n",tested,found);
  return 0; }
