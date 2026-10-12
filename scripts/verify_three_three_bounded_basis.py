#!/usr/bin/env python3
"""Replay the frozen finite-state construction and verify its rational certificate.

Standard library only; defaults to H=7 with an explicit 100,000-state limit in
its frozen constructor. No unrestricted-basis completeness is inferred.
"""
from pathlib import Path
import json, subprocess, sys, tempfile, shutil
ROOT=Path(__file__).resolve().parents[1]
EVIDENCE=ROOT/'evidence'/'three-three-bounded-basis'

def trim(p):
    while len(p)>1 and p[-1]==0:p.pop()
    return p

def add(a,b,scale=1):
    p=a[:]+[0]*max(0,len(b)-len(a))
    for i,v in enumerate(b):p[i]+=scale*v
    return trim(p)

def check_certificate(dfa):
    cert=json.loads((EVIDENCE/'rational-polynomial-certificate.json').read_text())
    P,Q=cert['numerators'],cert['denominator']
    assert Q[0]==1
    for key,row in dfa['states'].items():
        i=int(key);p=P[i][:]
        if i in dfa['accept']:p=add(p,Q,-1)
        for j in row.values():p=add(p,[0]+P[j],-1)
        assert trim(p)==[0],(i,p)
    assert P[dfa['start']]==[0,0,0,0,0,0,0,36,108,72,108,0,36,-36]
    assert Q==[1,0,0,-3,0,-1]

def main():
    expected=json.loads((EVIDENCE/'basis-dfa-width-7.json').read_text())
    check_certificate(expected)
    with tempfile.TemporaryDirectory(prefix='three-three-bounded-') as td:
        work=Path(td);(work/'analysis').mkdir();(work/'source').mkdir()
        for name in ('automaton.py','basis_automaton.py','analyze_automaton.py','verify_sets.py'):
            shutil.copy2(EVIDENCE/'source'/name,work/'analysis'/name)
        for name in ('basis_automaton.py','analyze_automaton.py'):
            result=subprocess.run([sys.executable,'analysis/'+name,'7'],cwd=work,
                                  capture_output=True,text=True,check=True,timeout=60)
            print(result.stdout,end='')
        actual=json.loads((work/'analysis/basis-dfa-7.json').read_text())
        assert actual==expected,'rebuilt DFA differs from certificate'
        census=ROOT/'evidence/three-three-basis-through-13.txt'
        if not census.exists():raise FileNotFoundError(census)
        shutil.copy2(census,work/'source'/census.name)
        result=subprocess.run([sys.executable,'analysis/verify_sets.py'],cwd=work,
                              capture_output=True,text=True,check=True,timeout=60)
        print(result.stdout,end='')
        obs=json.loads((work/'analysis/finite-set-check.json').read_text())
        assert obs==json.loads((EVIDENCE/'finite-set-check.json').read_text())
    print('PASS: exact DFA replay, all 28 rational equations, and retained census set equality.')

if __name__=='__main__':main()
