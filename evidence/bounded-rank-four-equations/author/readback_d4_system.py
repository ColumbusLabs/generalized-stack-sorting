"""Read coefficients from the explicit polynomial system, without stack counting."""
from collections import Counter, defaultdict, deque
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import resource
import time


def readback(max_degree=13, certificate_path=None):
    started=time.monotonic();source=Path('d4-univariate-system.json')
    data=json.loads(source.read_text());equations=data['equations'];size=len(equations)
    assert all(y==0 for terms in equations for c,x,y,ch in terms)
    constants=[0]*size;rounds=0
    while True:
        changed=[]
        for terms in equations:
            value=0
            for c,x,y,children in terms:
                if x:continue
                for child in children:c*=constants[child]
                value+=c
            changed.append(value)
        rounds+=1
        if changed==constants:break
        constants=changed
        assert rounds<1000, 'constant fixed point failed to stabilize'
    dependencies=[];reverse=defaultdict(list);indegrees=[]
    for i,terms in enumerate(equations):
        derivative=Counter()
        for c,x,y,children in terms:
            if x:continue
            for pos,child in enumerate(children):
                value=c
                for j,other in enumerate(children):
                    if j!=pos:value*=constants[other]
                if value:derivative[child]+=value
        dependencies.append(dict(derivative));indegrees.append(len(derivative))
        for child in derivative:reverse[child].append(i)
    queue=deque(i for i,n in enumerate(indegrees) if n==0);topological=[]
    while queue:
        child=queue.popleft();topological.append(child)
        for parent in reverse[child]:
            indegrees[parent]-=1
            if not indegrees[parent]:queue.append(parent)
    assert len(topological)==size, 'zero-size Jacobian is cyclic'
    if certificate_path is not None:
        Path(certificate_path).write_text(json.dumps({'system_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'constants':constants,'jacobian_topological_order':topological},separators=(',',':'))+'\n')
    series=[[c] for c in constants]
    for degree in range(1,max_degree+1):
        for row in series:row.append(0)
        @lru_cache(None)
        def monomial(children):
            if not children:return (1,)+(0,)*degree
            if len(children)==1:return tuple(series[children[0]])
            left=monomial(children[:-1]);right=series[children[-1]];out=[0]*(degree+1)
            for a,av in enumerate(left):
                if not av:continue
                for b,bv in enumerate(right[:degree-a+1]):
                    if bv:out[a+b]+=av*bv
            return tuple(out)
        known=[0]*size
        for i,terms in enumerate(equations):
            for c,x,y,children in terms:
                if x<=degree:known[i]+=c*monomial(tuple(children))[degree-x]
        for i in topological:
            series[i][degree]=known[i]+sum(c*series[j][degree] for j,c in dependencies[i].items())
        monomial.cache_clear()
    c,x,y,children=data['root'];answer=[0]*(max_degree+1);answer[0]=c
    for child in children:
        out=[0]*(max_degree+1)
        for i,a in enumerate(answer):
            for j,b in enumerate(series[child][:max_degree-i+1]):out[i+j]+=a*b
        answer=out
    answer=([0]*x+answer)[:max_degree+1]
    expected=[1,1,2,6,24,120,696,4434,29994,211248,1531326,11343804,85470360,652838112]
    assert answer[:len(expected)]==expected[:len(answer)],(answer,expected)
    return {'status':'PASS polynomial-system coefficient readback','coefficients':answer,
            'variables':size,'constant_fixed_point_rounds':rounds,
            'maximum_constant':max(constants),'zero_size_jacobian_edges':sum(map(len,dependencies)),
            'zero_size_jacobian_acyclic':True,
            'system_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'seconds':time.monotonic()-started,
            'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


if __name__=='__main__':
    result=readback(certificate_path='d4-system-branch-certificate.json');Path('d4-system-coefficient-readback.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
