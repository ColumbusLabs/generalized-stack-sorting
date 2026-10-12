#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,shutil,time
ROOT=Path(__file__).resolve().parent;source=(ROOT/'independent_branch.py').read_text();results={}
mutations={
 'false_unit_pivots':("vn,vd=val(nn,N),val(dd,N);assert vd is not None", "vn,vd=val(nn,N),val(dd,N);assert vd==0, (label,'false unit assumption');assert vd is not None"),
 'wrong_simple_derivative':("assert H.derivative(0)(325692,0)==-576","assert H.derivative(0)(325692,0)==-575"),
 'wrong_selected_jet':("assert jets[str(v)]==center[str(v)][:5]", "assert jets[str(v)]==(['13']+center[str(v)][1:5] if str(v)=='g' else center[str(v)][:5])"),
 'alternate_scalar_root':("coeff=[fmpq(325692)]","coeff=[fmpq(325656)]"),
}
for name,(old,new) in mutations.items():
    assert old in source;folder=ROOT/'controls'/name;folder.mkdir(parents=True,exist_ok=True)
    for f in ['input_manifest.json','independent_derived_formulas.json']:shutil.copy2(ROOT/f,folder/f)
    if not (folder/'frozen').exists():(folder/'frozen').symlink_to(ROOT/'frozen',target_is_directory=True)
    modified=source.replace(old,new)
    if name=='alternate_scalar_root':modified=modified.replace('coeff.append(residual[degree]/576)','coeff.append(-residual[degree]/576)')
    (folder/'independent_branch.py').write_text(modified)
    started=time.monotonic();p=subprocess.run(['python3',str(folder/'independent_branch.py')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=25)
    (folder/'output.log').write_text(p.stdout)
    assert p.returncode!=0,(name,'mutation unexpectedly passed')
    assert 'AssertionError' in p.stdout,(name,p.stdout)
    results[name]={'rejected':True,'returncode':p.returncode,'last_line':p.stdout.strip().splitlines()[-1],'seconds':time.monotonic()-started}
receipt={'status':'PASS','controls':results,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'controls_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
