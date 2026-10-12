#!/usr/bin/env python3
"""Check the final displayed coefficients and the author's finite center claims."""
from pathlib import Path
import sys,re,json,hashlib,time,resource
import sympy as S
from sympy.parsing.sympy_parser import parse_expr,standard_transformations,implicit_multiplication_application
from flint import fmpq_poly,fmpq
ROOT=Path(__file__).resolve().parent;start=time.monotonic()
resource.setrlimit(resource.RLIMIT_AS,(384<<20,384<<20))
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
manifest=json.loads((ROOT/'input_manifest.json').read_text())
for name,row in manifest.items():
    assert hashlib.sha256((ROOT/'frozen'/name).read_bytes()).hexdigest()==row['sha256'],name
read=lambda name:json.loads((ROOT/'frozen'/name).read_text())
cand=read('scalar_G_degree12_x6_candidate.json');final=read('direct-G33-equation.json')
assert final['terms_x_y_coefficient']==cand['terms']
y=S.Symbol('y');groups={k:sum(co*y**dy for dx,dy,co in cand['terms'] if dx==k) for k in range(7)}
for k in range(7):assert S.expand(S.sympify(final['grouped_coefficients_x'][str(k)])-groups[k])==0
text=(ROOT/'frozen/direct-G33-equation.md').read_text()
block=text.split(r'\begin{aligned}')[1].split(r'\end{aligned}')[0]
chunks=re.findall(r'A_([0-6])=\{\}&(.*?)(?=A_[0-6]=|\Z)',block,re.S)
assert len(chunks)==7
for k,chunk in chunks:
    chunk=re.sub(r'\\hspace\{\d+mm\}','',chunk)
    chunk=re.sub(r'\\\\\[2pt\]','',chunk).replace('\\\\','').replace('&','')
    chunk=re.sub(r'\^\{(\d+)\}',r'**\1',chunk).replace('^','**').replace('\n','').replace('.','')
    expr=parse_expr(chunk.strip().rstrip(','),local_dict={'y':y},transformations=standard_transformations+(implicit_multiplication_application,))
    assert S.expand(expr-groups[int(k)])==0,('display',k)
branch=read('scalar_G_branch_certificate.json');independent=json.loads((ROOT/'branch_receipt.json').read_text())
assert branch['center_coefficients']==independent['G_coefficients'][:29]
center=fmpq_poly([fmpq(z) for z in branch['center_coefficients']]);X=fmpq_poly([0,1]);P=fmpq_poly([]);DP=fmpq_poly([])
for dx,dy,co in cand['terms']:
    P+=co*X**dx*center**dy
    if dy:DP+=co*dy*X**dx*center**(dy-1)
valuation=lambda z:next(k for k in range(z.degree()+1) if z[k])
assert valuation(P)==40 and valuation(DP)==11 and DP[11]==-576
assert branch['residual_valuation']==40 and branch['derivative_valuation']==11 and branch['derivative_leading']=='-576'
ift=read('scalar_G_ordinary_ift_certificate.json')
assert ift['recovered_seven_parameter_jet4']==independent['selected_seven_jets']
assert ift['R_terms']==645 and ift['R_degree_z']==12 and ift['R_degree_x']==92
receipt={'status':'PASS','all_seven_latex_groups_match_frozen_69_terms':True,'final_json_matches_original_candidate':True,'degree28_center_matches_independent_scalar_root':True,'center_residual_valuation':40,'center_derivative_valuation':11,'center_derivative_leading':'-576','final_source_hashes':{name:manifest[name]['sha256'] for name in ['direct-G33-equation.md','direct-G33-equation.json','direct-G33-irreducibility.md']},'seconds':time.monotonic()-start,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'display_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
