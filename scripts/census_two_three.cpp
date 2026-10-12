// Independent array implementation of the repository's proved composition transitions.
// Still relies on that theorem; this is not an independent physical-machine proof.
#include <algorithm>
#include <array>
#include <chrono>
#include <iostream>
#include <cstdlib>
using namespace std;
struct Failure {int index=-1,height=-1;};
bool accepts(const int*p,int n,Failure*failure=nullptr){
 int comp[40],parts=0,maximum=0,height=0;unsigned held=0;
 for(int i=0;i<n;i++){
  int v=p[i];
  if(v>maximum){int add=v-maximum-1;if(parts)comp[0]+=add;else if(add)comp[parts++]=add;
   for(int a=maximum+1;a<v;a++)held|=(1u<<a);
   height+=add;maximum=v;continue;}
  int rank=__builtin_popcount(held&((1u<<v)-1))+1;
  int above=0,j=0;for(;j<parts;j++){int below=height-above-comp[j];if(below<rank&&rank<=below+comp[j])break;above+=comp[j];}
  if(above>=3){if(failure)*failure={i,height};return false;}
  int a=comp[j],below=height-above-a,k=rank-below,t=min(3-above,a);
  int next[40],cnt=0;for(int z=0;z<j;z++)next[cnt++]=comp[z];
  if(k>a-t+1){if(a>1)next[cnt++]=a-1;}
  else {if(t>1)next[cnt++]=t-1;for(int z=0;z<a-t-k+1;z++)next[cnt++]=1;if(k>1)next[cnt++]=k-1;}
  for(int z=j+1;z<parts;z++)next[cnt++]=comp[z];
  copy(next,next+cnt,comp);parts=cnt;height--;held&=~(1u<<v);
 }
 return parts==0;
}
int main(int argc,char**argv){
 int n=argc>1?atoi(argv[1]):10;if(n<1||n>12)return 2;
 int p[40],q[40];for(int i=0;i<n;i++)p[i]=i+1;
 unsigned long long accepted=0,basis=0,checked=0;auto start=chrono::steady_clock::now();
 do{
  checked++;Failure f;if(accepts(p,n,&f)){accepted++;continue;}
  bool minimal=true;
  for(int d=0;d<n&&minimal;d++){int z=0;for(int j=0;j<n;j++)if(j!=d)q[z++]=p[j]-(p[j]>p[d]);if(!accepts(q,n-1))minimal=false;}
  if(minimal){basis++;cout<<"BASIS ";for(int i=0;i<n;i++)cout<<p[i]<<",";cout<<" failure_index="<<f.index<<" height="<<f.height<<" suffix="<<n-f.index-1<<"\n";}
 }while(next_permutation(p,p+n));
 double sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();
 cout<<"SUMMARY n="<<n<<" checked="<<checked<<" accepted="<<accepted<<" basis="<<basis<<" seconds="<<sec<<"\n";
}
