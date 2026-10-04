import subprocess,time
from pathlib import Path
for i in range(9):
 t=time.monotonic(); log=Path(f'/tmp/small_endpoint_part_{i:02}.log')
 with log.open('w') as out:
  r=subprocess.run(['./tooling/with_lean.sh','lake','build',f'SerreMarkov.PositiveSmallEndpointPart{i:02}'],stdout=out,stderr=subprocess.STDOUT)
 print(f'part {i:02}: exit {r.returncode}, {time.monotonic()-t:.1f} seconds',flush=True)
 if r.returncode:
  print('\n'.join(log.read_text().splitlines()[-20:]),flush=True)
  raise SystemExit(r.returncode)
