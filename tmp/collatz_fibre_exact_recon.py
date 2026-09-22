from fractions import Fraction as Q
from math import isqrt

def plus(n):
    return n//2 if n%2 == 0 else (3*n+1)//2

def odd_step(n, sign=1):
    n=3*n+sign
    while n%2==0: n//=2
    return n

def juggler(n):
    return isqrt(n) if n%2==0 else isqrt(n**3)

def fibre(m, sign=1, size=6):
    out=[]
    for k in range(1, 2*size+3):
        if ((1<<k)*m-sign)%3 == 0:
            out.append((k, ((1<<k)*m-sign)//3))
        if len(out)==size: break
    return out

def exact_layer(previous, sign=1):
    M=3*len(previous)
    P=2*(M//3)
    f=[]
    for a in range(M):
        q=Q()
        for k in range(1,P+1):
            r=(pow(2,k,M)*a-sign)%M
            if r%3==0:
                q+=Q(3,2**k)*previous[r//3]
        f.append(q/(1-Q(1,2**P)))
    return f

for m in (1,5,7,11,13,17,19,23,25):
    print('target',m,'Collatz',fibre(m),'Juggler-even',
          [n for n in range(m*m,(m+1)**2) if n%2==0])
for sign in (1,-1):
    print('sign', sign)
    # Units only: exclude leaf children divisible by three.
    f=[Q(0),Q(1),Q(1)]
    for d in range(1,5):
        f=exact_layer(f,sign)
        units=[(a,v) for a,v in enumerate(f) if a%3]
        print('unit depth',d,'mean',sum(v for a,v in units)/len(units),
              'min',min(units,key=lambda av:av[1]),
              'maximum',max(v for a,v in units),
              'first',[(a,str(v)) for a,v in units[:6]])
