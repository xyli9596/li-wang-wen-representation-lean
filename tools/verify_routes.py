#!/usr/bin/env python3
"""Inspect Lean declaration bodies, not just import lists, after verify.py succeeds."""
from pathlib import Path
import subprocess, json, hashlib, datetime
root=Path(__file__).resolve().parents[1]
report_path=root/'verification/verification.json'
report=json.loads(report_path.read_text())
assert report['all_requested_checks_passed'], 'Run the full verifier first'
for entry in report['files']:
 assert hashlib.sha256((root/entry['file']).read_bytes()).hexdigest()==entry['sha256'], entry['file']
 assert hashlib.sha256((root/entry['olean']).read_bytes()).hexdigest()==entry['olean_sha256'], entry['olean']
result=subprocess.run(['lake','env','lean','tools/ProofDependencies.lean'],cwd=root,capture_output=True,text=True)
(root/'verification/proof-routes.log').write_text(result.stdout+result.stderr)
assert result.returncode==0, result.stdout+result.stderr
rows=json.loads(result.stdout.split('ROUTE_AUDIT_JSON:',1)[1])
assert len(rows)==14
for row in rows:
 deps=set(row['local_dependencies']); name=row['declaration']
 row['uses_wiman_valiron_quantitative']='WimanValiron.wimanValiron_quantitative' in deps
 row['uses_fourier_factorial_decay']='LiWangWen.verticalFourierCoeff_factorial_decay' in deps
 if name.startswith(('LiWangWen.example38_', 'LiWangWen.example39_')):
  assert 'LiWangWen.constantPlusX_polynomial_obstruction' in deps, name
  assert 'LiWangWen.finiteOrder_solution_has_normalized_polynomial_solution' in deps, name
  row['route']='examples_from_proved_polynomial_obstruction'
  row['uses_proved_polynomial_obstruction']=True
  continue
 if name in {'LiWangWen.theorem_3_1','LiWangWen.corollary_3_4','LiWangWen.lemma_5_2_mean_type',
             'LiWangWen.lemma_5_2_prime_symmetric'}:
  row['route']='shared'; continue
 direct=name.endswith('_direct') or name in {'LiWangWen.theorem_3_2_polynomial_factors','LiWangWen.corollary_3_3_matrix'}
 row['route']='direct' if direct else 'recurrence'
 assert row['uses_wiman_valiron_quantitative']==direct,name
 assert row['uses_fourier_factorial_decay']!=direct,name
out={'status':'passed','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'method':'Lean ConstantInfo type and proof-body transitive closure; all imported constants traversed',
 'verification_sha256':hashlib.sha256(report_path.read_bytes()).hexdigest(),
 'diagnostic_source_sha256':hashlib.sha256((root/'tools/ProofDependencies.lean').read_bytes()).hexdigest(),
 'endpoints':rows}
(root/'verification/proof-routes.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 14 proof endpoints, including Examples 3.8 and 3.9; direct and recurrence paths separated in proof terms.')
