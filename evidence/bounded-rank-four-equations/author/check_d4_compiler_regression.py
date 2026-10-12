"""Deterministic labelled-PDA replay of the missing-P-guard regression witness."""
from pathlib import Path
import json
from stack_sorting import bounded_rank as tagged
from prune_d4_pda_returns import build_pda,READY,FINAL
from minimize_d4_pda_controls import quotient

PERMUTATION=(6,3,2,5,10,8,4,13,12,11,9,7,1)


def replay(permutation=PERMUTATION,minimized=True):
    states,transitions,labels=build_pda(with_labels=True)
    if minimized:states,transitions,labels,_=quotient(states,transitions,labels)
    lookup={}
    for (p,a,r,word,w),label in zip(transitions,labels):
        key=(p,a,label);assert key not in lookup;lookup[key]=(r,word)
    control=READY;stack=('#',);steps=0
    def epsilon(control,stack):
        count=0
        while stack and (control,stack[0],()) in lookup:
            target,word=lookup[control,stack[0],()];control=target;stack=word+stack[1:];count+=1
            assert count<=20,'nonterminating epsilon processing'
        return control,stack,count
    input_labels=[(t,) if isinstance(t,str) else ('H',t) for t in tagged.tokens(permutation)]+[('$',)]
    for label in input_labels:
        control,stack,count=epsilon(control,stack);steps+=count
        if not stack or (control,stack[0],label) not in lookup:return False,steps
        target,word=lookup[control,stack[0],label];control=target;stack=word+stack[1:];steps+=1
    control,stack,count=epsilon(control,stack);steps+=count
    return control==FINAL and not stack,steps


if __name__=='__main__':
    assert tagged.accepts(PERMUTATION,4)
    raw,raw_steps=replay(minimized=False);small,small_steps=replay(minimized=True)
    assert raw and small
    result={'status':'PASS corrected raw and quotient PDA accept regression',
            'permutation':PERMUTATION,'raw_steps':raw_steps,'quotient_steps':small_steps,
            'scope':'One exact regression, not a replacement for the all-length compiler proof.'}
    Path('d4-compiler-regression-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
