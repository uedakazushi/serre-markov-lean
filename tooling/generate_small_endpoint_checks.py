from pathlib import Path
root=Path('SerreMarkov')
for idx in range(9):
 a,f=divmod(idx,3)
 lines=['import SerreMarkov.PositiveSmallEndpointBase','','namespace SerreMarkov.PositiveSmallEndpointCensus','','set_option Elab.async false','set_option maxRecDepth 100000','set_option maxHeartbeats 200000000','']
 for b in range(52):
  lines += [f'theorem block_{a}_{f}_{b} : blockCheck {a} {f} {b}=true := by decide +kernel','']
 lines += [f'theorem checked_{a}_{f} (b : Fin 52) : blockCheck {a} {f} b.val=true := by','  fin_cases b']
 for b in range(52): lines += [f'  · exact block_{a}_{f}_{b}']
 lines += ['','end SerreMarkov.PositiveSmallEndpointCensus','']
 (root/f'PositiveSmallEndpointPart{idx:02}.lean').write_text('\n'.join(lines))
lines=[f'import SerreMarkov.PositiveSmallEndpointPart{idx:02}' for idx in range(9)]
lines += ['','namespace SerreMarkov.PositiveSmallEndpointCensus','','theorem all_blocks_checked (a f : Fin 3) (b : Fin 52) : blockCheck a.val f.val b.val=true := by','  fin_cases a <;> fin_cases f']
for idx in range(9):
 a,f=divmod(idx,3)
 lines += [f'  · exact checked_{a}_{f} b']
lines += ['','end SerreMarkov.PositiveSmallEndpointCensus','']
(root/'PositiveSmallEndpointChecks.lean').write_text('\n'.join(lines))
