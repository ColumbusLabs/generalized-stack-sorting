"""Exact single-production substitution and polynomial bisimulation quotient."""
from collections import Counter, defaultdict, deque
from pathlib import Path
import json
import time
import resource


def inline_single(polynomials, root, certificate=None):
    single = {i: terms[0] for i,terms in enumerate(polynomials) if len(terms)==1}
    core = [i for i in range(len(polynomials)) if i not in single]
    core_ids = {old:new for new,old in enumerate(core)}
    resolved = {v:(1,0,0,(core_ids[v],)) for v in core}
    missing = {}
    reverse = defaultdict(list)
    todo = deque()
    for v,(coefficient,x,y,children) in single.items():
        dependencies = set(children) & single.keys()
        missing[v] = len(dependencies)
        for child in dependencies:
            reverse[child].append(v)
        if not dependencies:
            todo.append(v)
    def monomial(term):
        coefficient,x,y,children=term
        factors=[]
        for child in children:
            c,a,b,word=resolved[child]
            coefficient*=c;x+=a;y+=b;factors.extend(word)
        return coefficient,x,y,tuple(sorted(factors))
    elimination_order=[]
    while todo:
        v=todo.popleft()
        elimination_order.append(v)
        resolved[v]=monomial(single[v])
        for parent in reverse[v]:
            missing[parent]-=1
            if not missing[parent]:todo.append(parent)
    assert len(resolved)==len(polynomials), 'productive single-production cycle'
    result=[]
    for v in core:
        terms=Counter()
        for term in polynomials[v]:
            c,x,y,children=monomial(term)
            terms[x,y,children]+=c
        result.append([(c,x,y,children) for (x,y,children),c in sorted(terms.items())])
    root=monomial(root)
    if certificate is not None:
        certificate.update(core_variables=core, single_topological_order=elimination_order)
    return result,root,len(single)


def bisimulation(polynomials, root, certificate=None):
    blocks=[0]*len(polynomials)
    rounds=[]
    while True:
        signatures={};updated=[]
        for old,terms in enumerate(polynomials):
            polynomial=Counter()
            for c,x,y,children in terms:
                polynomial[x,y,tuple(sorted(blocks[child] for child in children))]+=c
            signature=(blocks[old],tuple(sorted(polynomial.items())))
            if signature not in signatures:signatures[signature]=len(signatures)
            updated.append(signatures[signature])
        rounds.append(len(signatures))
        old_count=len(set(blocks))
        blocks=updated
        if len(signatures)==old_count:break
    representatives={}
    for i,b in enumerate(blocks):representatives.setdefault(b,i)
    result=[]
    for b in range(len(representatives)):
        polynomial=Counter()
        for c,x,y,children in polynomials[representatives[b]]:
            polynomial[x,y,tuple(sorted(blocks[child] for child in children))]+=c
        result.append([(c,x,y,children) for (x,y,children),c in sorted(polynomial.items())])
    c,x,y,children=root
    if certificate is not None:
        certificate['partition_blocks']=blocks
    return result,(c,x,y,tuple(sorted(blocks[child] for child in children))),rounds


def reduce(specialize_y=False, certificate=None):
    started=time.monotonic()
    data=json.loads(Path('d4-start-system.json').read_text())
    count=len(data['variables']);polynomials=[None]*count
    for eq in data['equations']:
        polynomials[eq['lhs']]=[(1,int(w=='x'),int(w=='y' and not specialize_y),tuple(children)) for w,children in eq['terms']]
    root=(1,0,0,(data['start'],))
    del data
    history=[]
    while True:
        before=len(polynomials)
        step={} if certificate is not None else None
        polynomials,root,removed=inline_single(polynomials,root,step)
        polynomials,root,rounds=bisimulation(polynomials,root,step)
        if certificate is not None:certificate.append(step)
        history.append({'before':before,'single_production_eliminated':removed,'partition_sizes':rounds,'after':len(polynomials)})
        if len(polynomials)==before:break
    metadata={'status':'PASS exact algebraic reductions','held_weight_specialized_to_one':specialize_y,
              'variables':len(polynomials),'monomials':sum(map(len,polynomials)),
              'max_auxiliary_variable_degree':max((len(ch) for terms in polynomials for c,x,y,ch in terms),default=0),
              'max_total_degree_including_weights':max((x+y+len(ch) for terms in polynomials for c,x,y,ch in terms),default=0),
              'root_monomial':root,'history':history,'seconds':time.monotonic()-started,
              'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'scope':'Exact single-production substitution and polynomial bisimulation preserve the least counting-series solution.'}
    return metadata,polynomials,root


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--specialize-y',action='store_true');parser.add_argument('--certificate',action='store_true');args=parser.parse_args()
    certificate=[] if args.certificate else None
    metadata,polynomials,root=reduce(args.specialize_y,certificate)
    name='d4-univariate-system' if args.specialize_y else 'd4-bivariate-system'
    Path(name+'-reduction-stats.json').write_text(json.dumps(metadata,indent=2)+'\n')
    stable_metadata={k:v for k,v in metadata.items() if k not in ('seconds','peak_rss_kib')}
    Path(name+'.json').write_text(json.dumps({'metadata':stable_metadata,'root':root,'equations':polynomials},separators=(',',':'))+'\n')
    if certificate is not None:
        import hashlib
        source=Path('d4-start-system.json')
        Path(name+'-reduction-certificate.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'system_sha256':hashlib.sha256(Path(name+'.json').read_bytes()).hexdigest(),'steps':certificate},separators=(',',':'))+'\n')
    print(json.dumps(metadata,indent=2))
