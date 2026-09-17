#!/usr/bin/env python3
"""Recheck the author-review package without modifying its preserved inputs.
Python 3.10+, standard library. Add --full for the 231-bundle legacy replay.
"""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]

def need(b,msg):
 if not b:raise ValueError(msg)
def logical(x):
 if isinstance(x,dict):return {k:logical(v) for k,v in x.items() if k not in ('seconds','elapsed_seconds')}
 if isinstance(x,list):return [logical(v) for v in x]
 return x

def main():
 full='--full' in sys.argv[1:];manifest=ROOT/'SHA256SUMS.txt';hashes=0
 if manifest.exists():
  for line in manifest.read_text().splitlines():
   h,name=line.split('  ',1);p=ROOT/name
   need(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==h,'Hash mismatch: '+name);hashes+=1
 else:raise ValueError('Missing SHA256SUMS.txt; this is not the completed release.')
 with tempfile.TemporaryDirectory(prefix='epoch-v2-check-') as tmp:
  tmp=Path(tmp);fresh=tmp/'new';fresh.mkdir()
  def run(name,args):
   p=subprocess.run([sys.executable]+list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=150)
   need(p.returncode==0,name+' failed:\n'+p.stdout);print(name+': PASS',flush=True)
  r=ROOT/'repro';old=ROOT/'results'
  run('regenerate one-free-direction certificate',[r/'parametric_generator_search.py',fresh])
  for f in ['one_free_generator_certificate.json','one_free_generator_summary.json']:
   need((fresh/f).read_bytes()==(old/f).read_bytes(),'Changed regenerated '+f)
  run('independent parameter checker',[r/'check_parametric_certificate.py',fresh/'one_free_generator_certificate.json',fresh/'independent_parametric_check.json'])
  need((fresh/'independent_parametric_check.json').read_bytes()==(old/'independent_parametric_check.json').read_bytes(),'Changed parameter checker result')
  run('regenerate singleton certificate',[r/'singleton_generator_search.py',fresh/'singleton_generator_certificate.json'])
  need((fresh/'singleton_generator_certificate.json').read_bytes()==(old/'singleton_generator_certificate.json').read_bytes(),'Changed singleton certificate')
  run('independent singleton checker',[r/'check_singleton_certificate.py',fresh/'singleton_generator_certificate.json',fresh/'independent_singleton_check.json'])
  need((fresh/'independent_singleton_check.json').read_bytes()==(old/'independent_singleton_check.json').read_bytes(),'Changed singleton result')
  run('probe and coherent reduction calculus',[r/'check_probe_calculus.py',fresh/'probe_calculus_checks.json'])
  need((fresh/'probe_calculus_checks.json').read_bytes()==(old/'probe_calculus_checks.json').read_bytes(),'Changed probe calculus result')
  if full:
   work=tmp/'legacy_dag';shutil.copytree(r/'legacy_dag',work)
   run('full legacy arithmetic and graph corpus',[work/'check_all.py'])
   got=json.loads((work/'results/complete_bundle_audit.json').read_text());expected=json.loads((old/'full_aggregate_replay.json').read_text())
   need(logical(got)==logical(expected),'Legacy replay mathematical output changed')
  report={'status':'PASS','payload_hashes_checked':hashes,'new_outputs_reproduced_byte_identically':True,
    'full_legacy_replay':full,'official_epoch_verifier':False,'new_lean_build':False}
  print(json.dumps(report,indent=2))

if __name__=='__main__':main()
