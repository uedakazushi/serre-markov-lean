from collections import Counter

def q1(z):
 a,b,c,d,e,f=z
 return a*a+b*b+c*c+d*d+e*e+f*f-a*b*d-a*c*e-b*c*f-d*e*f+a*c*d*f

def q2(z):
 a,b,c,d,e,f=z
 return a*f-b*e+c*d

def marker(z):
 a,b,c,d,e,f=z
 return 32-4*(a*a+b*b+c*c+d*d+e*e+f*f)+2*(a*b*d+a*c*e+b*c*f+d*e*f)

def nodrop1(z):
 a,b,c,d,e,f=z
 return (2*(d+e)<=a*(b+c) and 2*(b+c)<=a*(d+e)
     and 2*(b+f)<=d*(a+e) and 2*(a+e)<=d*(b+f)
     and 2*(c+e)<=f*(b+d) and 2*(b+d)<=f*(c+e))

if __name__=='__main__':
 caps={(3,3):35,(3,4):36,(3,5):40,(4,4):40,(4,5):48,(5,5):63}
 out=[]
 for (a,f),cap in caps.items():
  rows=[]
  for b in range(3,cap-8):
   for c in range(3,cap-b-5):
    for d in range(3,cap-b-c-2):
     for k in (-4,4):
      x=a*f+c*d-k
      if x%b: continue
      e=x//b
      z=(a,b,c,d,e,f)
      if e<3 or b+c+d+e>cap or q1(z)!=8 or marker(z)<=0 or not nodrop1(z):continue
      rows.append(z)
  print((a,f),len(rows), 'max total',max(map(sum,rows),default=0))
  print(rows)
  out.extend(rows)
 print('TOTAL',len(out))
