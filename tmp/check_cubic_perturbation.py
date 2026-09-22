"""Independent exact symbolic check of the dual remainder and exponent budget."""
import sympy as s
from fractions import Fraction as F

t,h,j,u=s.symbols('t h j u', nonzero=True)
r=3*h*t**3/2+2*j/(3*t**2)
full=r/2-h*t**9/4+j*t**4/6
pure=r/2-2*r**3/(27*h*h)
rem=j*t**4/2+4*j*j/(27*h*t)+16*j**3/(729*h*h*t**6)
assert s.cancel(full-pure-rem)==0
rp=s.diff(r,t)
d=rem
for order in range(1,5):
    d=s.factor(s.diff(d,t)/rp)
    print('D'+str(order), d)
    if order==3:
        target=-4*u*(1-9*u+3*u*u)/(27*h*h*(1-u)**3)
        assert s.cancel(d-target.subs(u,8*j/(27*h*t**5)))==0
    if order==4:
        target=40*u*(1-16*u)/(243*h**3*t**3*(1-u)**5)
        assert s.cancel(d-target.subs(u,8*j/(27*h*t**5)))==0
theta=F(1,6)+F(1,1354)
alpha=F(1,2708)
beta=F(1,50000)
delta=F(1,25000)
exponents={
 'classical main': F(11,18)+(F(1,3)-alpha)/6+beta,
 'classical tail': F(23,36)+beta/2,
 'Robert main': F(3,4)-5*theta/6+(F(1,3)+beta)*theta+(F(1,2)+3*theta)*beta,
 'Robert tail': F(1,4)+5*(1-theta)/6+(F(1,3)-alpha)*(theta-1),
}
for name,exponent in exponents.items():
    assert exponent < F(2,3)-delta
    print(name, 'saving', F(2,3)-exponent, float(F(2,3)-exponent))
print('All exact identities and exponent margins pass.')
