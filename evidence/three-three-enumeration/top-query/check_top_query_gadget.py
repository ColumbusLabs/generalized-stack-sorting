"""Literal four-fresh-input gadget forcing a chosen old token to be top."""
from itertools import permutations
from pathlib import Path
import json,time,hashlib

def insert_all(states,value):
 return {s[:k]+(value,)+s[k:] for s in states for k in range(min(3,len(s)+1))}
def remove_value(states,value):
 result=set()
 for s in states:
  k=s.index(value)
  if k<3:result.add(s[:k]+s[k+1:])
 return result

def gadget(initial,target):
 u=len(initial)+1;states={initial}
 for v in range(u,u+4):states=insert_all(states,v)
 for v in (u+3,target,u,u+1,u+2):states=remove_value(states,v)
 return states

start=time.time();checks=0
for h in range(1,7):
 for stack in permutations(range(1,h+1)):
  for target in stack:
   expected={stack[1:]} if stack[0]==target else set()
   assert gadget(stack,target)==expected,(stack,target)
   checks+=1
out={'status':'PASS literal gadget image','max_initial_height':6,'stack_target_cases':checks,'seconds':time.time()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path('top-query-gadget-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
