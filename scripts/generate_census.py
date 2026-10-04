#!/usr/bin/env python3
"""Generate untrusted finite witnesses, all rechecked by Lean's kernel.

No import from the original verification code. The generic Lean enumeration
coverage proof, not this script, ensures that every involution is considered.
The Lean projection equality identifies these rows with that complete list.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path

N=12
BETA=tuple(3*(i//3)+(i+1)%3 for i in range(N))
REPS=(
 (1,0,3,2,6,9,4,10,11,5,7,8),
 (3,4,6,0,1,9,2,11,10,5,8,7),
 (3,6,9,0,7,11,1,4,10,2,8,5),
 (3,6,9,0,7,10,1,4,11,2,5,8),
 (3,4,6,0,1,9,2,10,11,5,7,8),
)

def matchings(xs):
 if not xs:
  yield ()
  return
 x=xs[0]
 for y in xs[1:]:
  rest=tuple(z for z in xs[1:] if z!=y)
  for pairs in matchings(rest): yield ((x,y),)+pairs

def rooted(alpha,root):
 queue=[root];label={root:0}
 for v in queue:
  for w in (alpha[v],BETA[v]):
   if w not in label:label[w]=len(queue);queue.append(w)
 if len(queue)!=12:return None
 code=tuple(label[alpha[v]] for v in queue)+tuple(label[BETA[v]] for v in queue)
 return code,tuple(label[v] for v in range(12))

def canonical(alpha):
 candidates=[rooted(alpha,i) for i in range(12)]
 if candidates[0] is None:return None
 return min(candidates)

def orbits(alpha):
 p=[alpha[BETA[i]] for i in range(12)]
 visited=set();out=[]
 for i in range(12):
  if i in visited:continue
  cyc=[];j=i
  while j not in visited:
   visited.add(j);cyc.append(j);j=p[j]
  out.append(cyc)
 return out

def reachable(alpha):
 q=[0];seen={0}
 for i in q:
  for j in (alpha[i],BETA[i]):
   if j not in seen:seen.add(j);q.append(j)
 return seen

def generate():
 repKeys={canonical(a)[0]:(i,canonical(a)[1]) for i,a in enumerate(REPS)}
 rows=[];counts=Counter()
 for pairs in matchings(tuple(range(12))):
  a=list(range(12))
  for x,y in pairs:a[x]=y;a[y]=x
  a=tuple(a);reach=reachable(a)
  if len(reach)!=12:
   color=[0 if i in reach else 1 for i in range(12)]
   assert set(color)=={0,1}
   assert all(color[a[i]]==color[i] and color[BETA[i]]==color[i] for i in range(12))
   witness=f'.disconnected {color}';counts['disconnected']+=1
  else:
   cyc=orbits(a)
   if len(cyc)==4:
    color=[0]*12
    for j,cc in enumerate(cyc):
     for v in cc:color[v]=j
    assert set(color)==set(range(4))
    assert all(color[a[BETA[i]]]==color[i] for i in range(12))
    witness=f'.manyCycles {color}';counts['four_cycles']+=1
   else:
    assert len(cyc)==2
    key,label=canonical(a);r,replabel=repKeys[key]
    inv=[0]*12
    for i,j in enumerate(replabel):inv[j]=i
    g=[inv[label[i]] for i in range(12)]
    assert sorted(g)==list(range(12))
    assert all(g[a[i]]==REPS[r][g[i]] and g[BETA[i]]==BETA[g[i]] for i in range(12))
    witness=f'.conjugate {r} {g}';counts['conjugate']+=1
   rows.append((list(a),witness))
   continue
  rows.append((list(a),witness))
 assert len(rows)==10395
 assert counts=={'disconnected':675,'four_cycles':5184,'conjugate':4536}
 chunks=[rows[i:i+100] for i in range(0,len(rows),100)]
 out=[]
 for group in range((len(chunks)+9)//10):
  previous='SerreMarkov.Census' if group==0 else f'SerreMarkov.CensusPart{group-1:03}'
  part=[f'import {previous}\n\n',
   '/-! Kernel-checked finite certificates; modules are chained to bound memory. -/\n\n',
   'set_option Elab.async false\nset_option maxRecDepth 50000\nset_option maxHeartbeats 100000000\n\n',
   'namespace SerreMarkov.IndexTwelve\n\n']
  for i in range(group*10,min((group+1)*10,len(chunks))):
   chunk=chunks[i]
   part.append(f'def censusChunk{i:03} : List CensusRow := [\n')
   part.extend('  ⟨'+str(a)+', '+w+'⟩'+(',' if j<len(chunk)-1 else '')+'\n' for j,(a,w) in enumerate(chunk))
   part.append(']\n\n')
   part.append(f'theorem censusChunk{i:03}_checked : ∀ row ∈ censusChunk{i:03}, row.Valid := by\n  have hc : censusChunk{i:03}.all CensusRow.Check = true := by decide +kernel\n  intro row hrow\n  exact row.check_correct.mp ((List.all_eq_true.mp hc) row hrow)\n\n')
  part.append('end SerreMarkov.IndexTwelve\n')
  Path(f'SerreMarkov/CensusPart{group:03}.lean').write_text(''.join(part))
 out=[f'import SerreMarkov.CensusPart{(len(chunks)-1)//10:03}\n\n',
  '/-! All 10,395 witnesses assembled from independently kernel-checked chunks.\n',
  'The preceding module chain enforces bounded-memory sequential builds. -/\n\n',
  'set_option Elab.async false\nset_option maxRecDepth 50000\n',
  'set_option maxHeartbeats 100000000\n\nnamespace SerreMarkov.IndexTwelve\n\n']
 out.append('def allCensusChunks : List (List CensusRow) := [\n  '+',\n  '.join(f'censusChunk{i:03}' for i in range(len(chunks)))+'\n]\n\n')
 out.append('def allCensusRows : List CensusRow := allCensusChunks.flatten\n\n')
 out.append('theorem allCensusChunks_checked :\n    ∀ chunk ∈ allCensusChunks, ∀ row ∈ chunk, row.Valid := by\n')
 out.append('  simp only [allCensusChunks, List.forall_mem_cons]\n')
 out.append('  exact '+''.join('⟨'+f'censusChunk{i:03}_checked, ' for i in range(len(chunks)))+'(by intro x hx; cases hx)'+'⟩'*len(chunks)+'\n\n')
 out.append('''theorem allCensusRows_checked : ∀ row ∈ allCensusRows, row.Valid := by
  intro row hrow
  obtain ⟨chunk, hchunk, hmem⟩ := List.mem_flatten.mp hrow
  exact allCensusChunks_checked chunk hchunk row hmem

end SerreMarkov.IndexTwelve
''')
 Path('SerreMarkov/CensusData.lean').write_text(''.join(out))
 print(dict(counts), 'rows',len(rows),'chunks',len(chunks))

if __name__=='__main__':generate()
