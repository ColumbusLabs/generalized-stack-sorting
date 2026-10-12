"""Strong labelled-control bisimulation, with an explicit bisimulation certificate.

This preserves whole labelled pushdown runs, not merely sampled counts. Labels
and pushed words are retained in each signature. No different labels are merged.
"""
from collections import defaultdict


def quotient(states,transitions,labels):
    n=len(states);outgoing=defaultdict(list)
    for t,label in zip(transitions,labels):outgoing[t[0]].append((t,label))
    blocks=[int(p==2) for p in range(n)];rounds=[]
    while True:
        signatures={};updated=[]
        for p in range(n):
            row=tuple(sorted((a,blocks[r],word,w,label) for (_,a,r,word,w),label in outgoing[p]))
            signature=(blocks[p],row)
            if signature not in signatures:signatures[signature]=len(signatures)
            updated.append(signatures[signature])
        rounds.append(len(signatures));old_count=len(set(blocks));blocks=updated
        if len(signatures)==old_count:break
    assert blocks[:3]==[0,1,2]
    representatives={}
    for p,b in enumerate(blocks):representatives.setdefault(b,p)
    changed=[];changed_labels=[];rows={}
    for b in range(len(representatives)):
        row=sorted((a,blocks[r],word,w,label) for (_,a,r,word,w),label in outgoing[representatives[b]])
        rows[b]=row
        for a,r,word,w,label in row:
            changed.append((b,a,r,word,w));changed_labels.append(label)
    for p in range(n):
        row=sorted((a,blocks[r],word,w,label) for (_,a,r,word,w),label in outgoing[p])
        assert row==rows[blocks[p]],'quotient failed a control row identity'
    keys=[(p,a,label) for (p,a,r,word,w),label in zip(changed,changed_labels)]
    assert len(keys)==len(set(keys))
    epsilon={(p,a) for p,a,label in keys if not label}
    assert not any((p,a) in epsilon and label for p,a,label in keys)
    certificate={'source_controls':n,'source_transitions':len(transitions),'partition_sizes':rounds,
                 'blocks':blocks,'representatives':[representatives[b] for b in range(len(representatives))],
                 'quotient_controls':len(representatives),'quotient_transitions':len(changed)}
    return {('class',b):b for b in range(len(representatives))},changed,changed_labels,certificate
