#!/usr/bin/env python3
"""Run exact-algebra checks in a fresh output directory, preserving every result."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
DRIVERS=['independent_identities.py','independent_branch.py','independent_reverse_lift.py','independent_display.py','independent_irreducibility.py','run_controls.py']
def verify():
 manifest=json.loads((ROOT/'review/input_manifest.json').read_text())
 for name,row in manifest.items():
  assert hashlib.sha256((ROOT/'review/frozen'/name).read_bytes()).hexdigest()==row['sha256'],name
 return manifest
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--verify-only',action='store_true');a=p.parse_args();m=verify()
 if a.verify_only:print('Exact-algebra input hashes PASS:',len(m),'files; no symbolic checker invoked.');return
 if a.output is None:p.error('--output is required unless --verify-only is used')
 out=a.output.resolve();assert out!=ROOT and ROOT not in out.parents,'Use a fresh output directory outside the package';out.mkdir(parents=True,exist_ok=False)
 work=out/'checks';shutil.copytree(ROOT/'review',work);results=[]
 for driver in DRIVERS:
  started=time.monotonic()
  with (out/(driver+'.log')).open('w') as log:r=subprocess.run([sys.executable,str(work/driver)],cwd=work,stdout=log,stderr=subprocess.STDOUT)
  results.append({'driver':driver,'exit_code':r.returncode,'seconds':time.monotonic()-started});(out/'RESULTS.json').write_text(json.dumps(results,indent=2)+'\n')
  assert r.returncode==0,(driver,r.returncode)
  print(driver,'PASS',flush=True)
if __name__=='__main__':main()
