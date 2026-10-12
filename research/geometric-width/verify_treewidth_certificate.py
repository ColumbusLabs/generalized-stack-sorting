"""Independent-of-search, stdlib-only exact replay of the frozen width-five witness."""
import hashlib,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(256<<20,256<<20))
BASE=Path(__file__).parent
raw=(BASE/'treewidth-five-certificate.json').read_bytes(); C=json.loads(raw)
p=C['permutation']; n=len(p); assert sorted(p)==list(range(1,n+1))
stack=[]; inserted=[]; output=[]; start={};end={};events=[]
for t,(op,v,slot) in enumerate(C['legal_lazy_history']):
 assert type(slot) is int and 0<=slot<3
 if op=='insert':
  assert v==len(inserted)+1 and slot<=len(stack)
  inserted.append(v);start[v]=t;stack.insert(slot,v)
 else:
  assert op=='remove' and slot<len(stack) and stack[slot]==v
  output.append(v);end[v]=t;stack.pop(slot)
 events.append((op,v))
assert not stack and output==p and inserted==list(range(1,n+1))
# Exact lazy normalization, derived directly from p rather than trusting the history.
lazy=[]; maximum=0
for v in p:
 if v>maximum:
  lazy += [('insert',u) for u in range(maximum+1,v+1)];maximum=v
 lazy.append(('remove',v))
assert events==lazy
edges=set()
for u in range(1,n+1):
 for v in range(u+1,n+1):
  if start[u]<start[v]<end[u]<end[v] or start[v]<start[u]<end[v]<end[u]:edges.add((u-1,v-1))
assert edges==set(map(tuple,C['edges']))
adj={v:set() for v in range(n)}
for u,v in edges:adj[u].add(v);adj[v].add(u)
# A disjoint connected branch-set certificate gives an actual graph minor.
bs=list(map(set,C['lower_bound_certificate']['branch_sets']));used=set()
for S in bs:
 assert S and all(0<=v<n for v in S) and not(used&S);used|=S
 reached={next(iter(S))}
 while True:
  more=set().union(*(adj[v] for v in reached))&S
  if more<=reached:break
  reached|=more
 assert reached==S
medges=[]; degrees=[0]*len(bs)
for i,S in enumerate(bs):
 for j in range(i+1,len(bs)):
  if any(adj[v]&bs[j] for v in S):medges.append([i,j]);degrees[i]+=1;degrees[j]+=1
assert min(degrees)>=5
assert min(degrees)==C['lower_bound_certificate']['min_degree']
# Filled elimination gives a treewidth upper bound; no heuristic trusted here.
a={v:set(ws) for v,ws in adj.items()};order=C['upper_bound_certificate']['elimination_order']; assert sorted(order)==list(range(n))
width=0
for v in order:
 ns=a[v];width=max(width,len(ns))
 for w in ns:a[w]|=ns-{w};a[w].discard(v)
 del a[v]
assert width==C['upper_bound_certificate']['width']==5
# Check the common total order and every geometric endpoint crossing count.
bottom=C['bottom_peeling_order'];assert sorted(bottom)==list(range(1,n+1));depth={v:i+1 for i,v in enumerate(reversed(bottom))}
held=[]; stem_crossings=[]; geometric_pairs=set()
for t,(op,v,slot) in enumerate(C['legal_lazy_history']):
 expected=sorted(held,key=depth.get);assert held==expected
 if op=='insert':
  assert slot==sum(depth[u]<depth[v] for u in held);held.insert(slot,v)
 else:assert held.index(v)==slot;held.pop(slot)
 upper=[u for u in range(1,n+1) if start[u]<t<end[u] and depth[u]<depth[v]]
 assert len(upper)==slot and len(upper)<=2
 stem_crossings.append(len(upper))
 for u in upper:geometric_pairs.add(tuple(sorted((u-1,v-1))))
assert edges<=geometric_pairs
result={'status':'PASS','certificate_sha256':hashlib.sha256(raw).hexdigest(),'permutation':p,'legal_events':len(events),'proper_overlap_edges':len(edges),'minor_branch_sets':len(bs),'minor_edges':len(medges),'minor_min_degree':min(degrees),'minor_is_K6':len(bs)==6 and len(medges)==15,'filled_elimination_width':width,'exact_treewidth':5,'maximum_stem_crossings':max(stem_crossings),'geometric_intersection_pairs':len(geometric_pairs),'covers_all_proper_overlaps':True,'scope':'Finite certificate validation, not a proof of the general width theorem or algebraicity.'}
(BASE/'verification-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
