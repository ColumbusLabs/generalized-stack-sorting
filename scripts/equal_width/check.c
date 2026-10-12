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
static Key *tab; static uint8_t *used; static size_t tsize; static size_t tcount;
static uint64_t hk(const Key *k){ uint64_t h=1469598103934665603ULL^k->i^((uint64_t)k->len<<8);
  for(int j=0;j<k->len;j++){ h^=k->st[j]; h*=1099511628211ULL; } return h; }
static int keq(const Key *a,const Key *b){ return a->len==b->len && a->i==b->i && !memcmp(a->st,b->st,a->len); }
static void reset(void){ memset(used,0,tsize); tcount=0; }
static int has(const Key *k){ size_t j=hk(k)&(tsize-1); while(used[j]){ if(keq(&tab[j],k)) return 1; j=(j+1)&(tsize-1);} return 0; }
static void add(const Key *k){ if(tcount*2>tsize) return; size_t j=hk(k)&(tsize-1); while(used[j]){ if(keq(&tab[j],k)) return; j=(j+1)&(tsize-1);} used[j]=1; tab[j]=*k; tcount++; }
static const int *P; static int N;
static long long nodes;
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
int main(int argc,char**argv){
  R=atoi(argv[1]); S=atoi(argv[2]); CAP=argc>3?atoi(argv[3]):0;
  tsize=1<<21; tab=malloc(sizeof(Key)*tsize); used=malloc(tsize);
  char line[8192];
  while(fgets(line,sizeof line,stdin)){
    if(!strchr(line,'\n') && !feof(stdin)){ fprintf(stderr,"input line too long\n"); return 2; }
    int p[MAXN], n=0; char *s=line, *e;
    while(1){ long v=strtol(s,&e,10); if(s==e) break;
      if(n>=MAXN-1){ fprintf(stderr,"permutation longer than %d\n",MAXN-1); return 2; }
      p[n++]=(int)v; s=e; }
    if(n==0) continue;
    { int seen[MAXN]={0};
      for(int i=0;i<n;i++){ if(p[i]<1||p[i]>n||seen[p[i]]){ fprintf(stderr,"not a permutation of 1..%d\n",n); return 2; } seen[p[i]]=1; } }
    int pi[MAXN]; for(int i=0;i<n;i++) pi[p[i]-1]=i+1;   /* pi = inverse(p) */
    nodes=0;
    int full=sortable(pi,n);
    int bad=-1;
    for(int d=0; d<n && bad<0; d++){ /* delete value p[d] from p  <=> delete position p[d]-1 from pi */
      int q[MAXN], m=0, v=pi[p[d]-1];
      for(int i=0;i<n;i++) if(i!=p[d]-1) q[m++]= pi[i]>v ? pi[i]-1 : pi[i];
      if(!sortable(q,m)) bad=d;
    }
    for(int i=0;i<n;i++) printf("%d ",p[i]);
    if(full) printf("| SORTABLE(generated)\n");
    else if(bad>=0) printf("| rejected, NOT minimal (deleting value %d still rejected)\n", p[bad]);
    else printf("| BASIS ELEMENT\n");
    fflush(stdout);
  }
  return 0;
}
