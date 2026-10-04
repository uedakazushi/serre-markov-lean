#!/usr/bin/env python3
"""Extend the kernel-verified finite-conic slice construction to d=6,7,8.

Symbolic output is untrusted; each polynomial identity and coordinate bound
is proved again by Lean. No upper bound on a general terminal d is asserted.
"""
from pathlib import Path
import sys, json
base=Path(__file__).resolve().parent
for d in map(int,sys.argv[1:] or ('6','7','8')):
 assert d in (6,7,8)
 name={6:'Six',7:'Seven',8:'Eight'}[d];word=name.lower()
 code=(base/'generate_positive_three_five_bounds.py').read_text()
 code=code.replace('PositiveThreeFive','PositiveThree'+name).replace('a_three_d_five','a_three_d_'+word)
 code=code.replace('a=3;d=5','a=3;d='+str(d)).replace('range(4,12)','range(4,'+str(3*d-3)+')')
 code=code.replace('c,5,e,f','c,'+str(d)+',e,f')
 code=code.replace('{A}*c-15*f','{A}*c-{3*d}*f').replace('{B}*f-15*c','{B}*f-{3*d}*c')
 code=code.replace('{3*b-5}','{3*b-d}').replace('{5*b-3}','{d*b-3}')
 code=code.replace('*c-5*e+{50-5*b}','*c-{d}*e+{50-5*b}')
 code=code.replace('{15-b}','{3*d-b}').replace('{50-5*b}','{10*d-5*b}').replace('{84-7*b}','{3*(d*d+d-2)-(d+2)*b}')
 code=code.replace('b ≤ 11','b ≤ '+str(3*d-4)).replace('z.b ≤ 11','z.b ≤ '+str(3*d-4))
 code=code.replace('15-b','%s-b'%(3*d)).replace('15-z.b','%s-z.b'%(3*d))
 code=code.replace('c-5*e+50-5*b',f'c-{d}*e+{10*d}-5*b').replace('z.c-5*z.e+50-5*z.b',f'z.c-{d}*z.e+{10*d}-5*z.b')
 code=code.replace('f-3*e+84-7*b',f'f-3*e+{3*(d*d+d-2)}-{d+2}*b').replace('z.f-3*z.e+84-7*z.b',f'z.f-3*z.e+{3*(d*d+d-2)}-{d+2}*z.b')
 code=code.replace('(hd : z.d=5)','(hd : z.d='+str(d)+')').replace('z.c,5,z.e','z.c,'+str(d)+',z.e')
 code=code.replace('slice a=3,d=5','slice a=3,d='+str(d))
 ns={'__file__':str(base/'generate_positive_three_five_bounds.py')}
 exec(compile(code,str(base/'generate_positive_three_fixed_bounds.py'),'exec'),ns)
 (base/f'positive_three_{word}_boxes.json').write_text(json.dumps(ns['records'],indent=2))
 print(d,ns['records'])
