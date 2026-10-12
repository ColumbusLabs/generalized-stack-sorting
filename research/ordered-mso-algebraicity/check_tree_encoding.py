"""Finite tests of the finite-port encoder and same-node round trip.
Does not implement BP's logical transduction or prove its canonization.
"""
import itertools,random,json,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20))
BASE=Path(__file__).parent;rng=random.Random(3517)
def diagram(p):
 events=[];M=0;ins={};rem={}
 for v in p:
  if v>M:
   for u in range(M+1,v+1):ins[u]=len(events);events.append(('I',u))
   M=v
  rem[v]=len(events);events.append(('R',v))
 N=len(events);succ={(i,i+1) for i in range(N-1)};match={tuple(sorted((ins[v],rem[v]))) for v in p}
 adj=[set() for _ in range(N)]
 for u,v in succ|match:adj[u].add(v);adj[v].add(u)
 return events,succ,match,adj,ins,rem

def elimination(adj,priority):
 rank={v:i for i,v in enumerate(priority)};parent={};desc={};children={v:[] for v in range(len(adj))}
 def rec(U,par):
  v=min(U,key=rank.get);parent[v]=par;desc[v]=set(U);U=set(U)-{v}
  while U:
   w=next(iter(U));C={w};todo=[w];U.remove(w)
   while todo:
    u=todo.pop();more=adj[u]&U;U-=more;C|=more;todo.extend(more)
   child=rec(C,v);children[v].append(child)
  children[v].sort();return v
 root=rec(set(range(len(adj))),None)
 for u in range(len(adj)):
  for v in adj[u]:assert v in desc[u] or u in desc[v]
 return root,parent,children,desc

def encode(events,succ,match,adj,F):
 root,parent,children,desc=F;bags={};labels={};width=0
 for v in sorted(parent,key=lambda v:-len(desc[v])):
  anc=[];u=parent[v]
  while u is not None:
   if adj[u]&desc[v]:anc.append(u)
   u=parent[u]
  bag=[v]+sorted(anc);bags[v]=bag;width=max(width,len(anc))
  ports=() if parent[v] is None else tuple(bags[parent[v]].index(u) for u in bag[1:])
  flags=tuple((1 if (v,u) in succ else 0)|(2 if (u,v) in succ else 0)|(4 if tuple(sorted((v,u))) in match else 0) for u in bag[1:])
  labels[v]=(events[v][0],len(anc),ports,flags)
 def forest(vs):
  if not vs:return None
  v=vs[0];return (labels[v],forest(children[v]),forest(vs[1:]))
 return forest([root]),width

def decode(T):
 events=[];succ=set();match=set();parents={};bags={};children={}
 def read(T,par):
  if T is None:return
  label,L,R=T;color,d,mapping,flags=label;v=len(events);events.append((color,None));parents[v]=par;children[v]=[]
  if par is not None:children[par].append(v)
  assert len(mapping)==d and len(flags)==d and len(set(mapping))==d
  if par is None:assert d==0 and R is None;bag=[v]
  else:
   assert all(0<=i<len(bags[par]) for i in mapping);bag=[v]+[bags[par][i] for i in mapping]
  assert len(set(bag))==len(bag);bags[v]=bag
  for u,flag in zip(bag[1:],flags):
   if flag&1:succ.add((v,u))
   if flag&2:succ.add((u,v))
   if flag&4:match.add(tuple(sorted((u,v))))
  read(L,v);read(R,par)
 read(T,None);N=len(events);adj=[set() for _ in events]
 for u,v in succ|match:adj[u].add(v);adj[v].add(u)
 nextv={u:v for u,v in succ};assert len(nextv)==len(succ)==N-1
 starts=set(range(N))-{v for _,v in succ};assert len(starts)==1
 order=[];v=next(iter(starts))
 while True:
  assert v not in order;order.append(v)
  if v not in nextv:break
  v=nextv[v]
 assert len(order)==N;timeidx={v:i for i,v in enumerate(order)}
 # Verify canonical port order and sibling order under reconstructed time.
 for v,bag in bags.items():assert bag[1:]==sorted(bag[1:],key=timeidx.get)
 for ch in children.values():assert ch==sorted(ch,key=timeidx.get)
 # Exact, not oversized, bags.
 desc={}
 def subtree(v):
  out={v}
  for w in children[v]:out|=subtree(w)
  desc[v]=out;return out
 root=next(v for v,p in parents.items() if p is None);subtree(root)
 for v,bag in bags.items():
  exact={v};u=parents[v]
  while u is not None:
   if adj[u]&desc[v]:exact.add(u)
   u=parents[u]
  assert exact==set(bag)
 # Recover matching permutation.
 labels={};mate={}
 for u,v in match:
  assert u not in mate and v not in mate;mate[u]=v;mate[v]=u
 assert len(mate)==N
 p=[];j=0
 for v in order:
  if events[v][0]=='I':j+=1;labels[v]=j;assert timeidx[v]<timeidx[mate[v]]
  else:assert events[mate[v]][0]=='I';p.append(labels[mate[v]])
 # Recode after transporting node IDs back to event order.
 E=[events[v] for v in order];S={(timeidx[u],timeidx[v]) for u,v in succ};M={tuple(sorted((timeidx[u],timeidx[v]))) for u,v in match};A=[set() for _ in order]
 for u,v in S|M:A[u].add(v);A[v].add(u)
 F=(timeidx[root],{timeidx[v]:None if p is None else timeidx[p] for v,p in parents.items()},{timeidx[v]:[timeidx[w] for w in children[v]] for v in children},{timeidx[v]:{timeidx[w] for w in vs} for v,vs in desc.items()})
 back,_=encode(E,S,M,A,F);assert back==T
 return p

def subset_peeling(p,explicit):
 E,S,M,A,ins,rem=diagram(p);labels=list(p)
 def eligible(U,v):return sum(ins[u]<ins[v]<rem[u] for u in U)<3 and sum(ins[u]<rem[v]<rem[u] for u in U)<3
 U=set(labels)
 while U:
  es=[v for v in U if eligible(U,v)]
  if not es:break
  U.remove(min(es))
 greedy=not U
 if explicit:
  universal=True
  for bits in range(1,1<<len(labels)):
   V={labels[i] for i in range(len(labels)) if bits>>i&1}
   if not any(eligible(V,v) for v in V):universal=False;break
  assert universal==greedy
 return greedy

if __name__=='__main__':
 start=time.time();permutations=encodings=subset_checks=ambiguous_examples=0;maximum_width=0
 for n in range(1,8):
  for p in itertools.permutations(range(1,n+1)):
   permutations+=1;explicit=n<=6 or rng.randrange(20)==0;subset_checks+=explicit
   subset_peeling(p,explicit)
   events,succ,match,adj,_,_=diagram(p);seen={};codes=set()
   for rep in range(3):
    order=list(range(2*n));rng.shuffle(order);F=elimination(adj,order);T,w=encode(events,succ,match,adj,F)
    assert decode(T)==list(p);encodings+=1;maximum_width=max(maximum_width,w)
    key=tuple(F[1][v] for v in range(2*n))
    if key in seen:assert seen[key]==T
    seen[key]=T;codes.add(T)
   ambiguous_examples+=len(codes)>1
 out={'status':'PASS','permutations_checked':permutations,'tree_round_trips':encodings,'exact_subset_formula_checks':subset_checks,'maximum_experimental_bag_width':maximum_width,'diagrams_with_multiple_valid_noncanonical_tree_encodings':ambiguous_examples,'scope':'Checks decoder/encoder and finite subset formula only. Does not implement or verify the BP transduction, lex selector, or MSO tree-recognition theorem.','elapsed_seconds':time.time()-start}
 (BASE/'tree-encoding-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
