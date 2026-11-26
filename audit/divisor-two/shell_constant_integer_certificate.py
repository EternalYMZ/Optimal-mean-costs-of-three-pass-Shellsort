"""Cache-free rational/fixed-point certificate for the variational minimum.
All bounding computations use integers or Fraction. Floats are output only.
The analytic assumptions (concavity, heat-kernel identity, tail lemma) are
spelled out in audit_constant_certificate_repair_2026-11-17.txt.
"""
from fractions import Fraction as F
from math import isqrt, factorial
from pathlib import Path
import hashlib
import json
import numpy as np

S=10**24
MODES=128
DELTA0=F(1,10000)
GRID=128
TARGET=F(3041,5000)

def floorf(x):return x.numerator//x.denominator
def ceilf(x):return -((-x.numerator)//x.denominator)
def fixed(x):return floorf(x*S),ceilf(x*S)
def ceildiv(a,b):return -((-a)//b)
def mul(a,b):
    # All uses have nonnegative operands.
    return a[0]*b[0]//S,ceildiv(a[1]*b[1],S)
def root(a):return isqrt(a[0]*S),isqrt(a[1]*S)+1
def reciprocal(a):return S*S//a[1],ceildiv(S*S,a[0])
def atan(q,n):
    v=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    err=F(1,(2*n+1)*q**(2*n+1))
    return (v,v+err) if n%2==0 else (v-err,v)

aa,bb=atan(5,40),atan(239,12)
PI=(16*aa[0]-4*bb[1],16*aa[1]-4*bb[0])
assert 3<PI[0]<PI[1]<F(16,5)
PIF=(floorf(PI[0]*S),ceilf(PI[1]*S))
PISQ=mul(PIF,PIF)
COEF=(2*S*S//PISQ[1],ceildiv(2*S*S,PISQ[0]))
QCOEF=reciprocal(root((2*PIF[0],2*PIF[1])))
sqrtpi=root(PIF)
C0=root((sqrtpi[0]//8,ceildiv(sqrtpi[1],8)))

# Exact rational proofs of the elementary-function remainder budgets.
assert F(8,5)**43/F(factorial(43)) < F(1,S)
assert F(1,8)**25/F(factorial(25)) < F(1,S)
assert F(2,5)**80 < F(1,S)
# The omitted heat tail: a=4*pi^2*delta>=36/10000, first r=129.
# a*r^2>59 and a*(2r+1)>9/10 give an upper bound on the geometric tail.
TAIL=F(2,9)*F(2,5)**59/F(129**2)*F(19,9)
assert TAIL<F(1,S)

def sin2(u):
    u-=floorf(u)
    if u>F(1,2):u=1-u
    if not u:return 0,0
    y=(floorf(PI[0]*u*S),ceilf(PI[1]*u*S))
    y2=mul(y,y);term=y;lo,hi=y
    for j in range(1,21):
        a,b=mul(term,y2);den=(2*j)*(2*j+1)
        term=(a//den,ceildiv(b,den))
        if j%2:lo-=term[1];hi-=term[0]
        else:lo+=term[0];hi+=term[1]
    # The next alternating term is negative and less than one lattice unit.
    lo=max(0,lo-1);hi=min(S,hi)
    return lo*lo//S,ceildiv(hi*hi,S)

def expminus(x):
    # x is an enclosing nonnegative fixed-point interval.
    if x[0]>=80*S:return 0,1
    scale=1
    while x[1]>S*scale//8:scale*=2
    y=(x[0]//scale,ceildiv(x[1],scale))
    # y<=1/8+1/S; enlarge scale once if rounding crossed 1/8.
    if y[1]>S//8:
        scale*=2;y=(x[0]//scale,ceildiv(x[1],scale))
    term=(S,S);lo=hi=S
    for j in range(1,25):
        a,b=mul(term,y);term=(a//j,ceildiv(b,j))
        if j%2:lo-=term[1];hi-=term[0]
        else:lo+=term[0];hi+=term[1]
    lo=max(0,lo-1);hi=min(S,hi)
    while scale>1:
        lo,hi=mul((lo,hi),(lo,hi));hi=min(S,hi);scale//=2
    return lo,hi

GRIDS={}
def grid(n,mid):
    key=(n,mid)
    if key in GRIDS:return GRIDS[key]
    if mid:
        xs=[F(i*i+(i+1)**2,4*n*n) for i in range(n)]
        ws=[2*i+1 for i in range(n)];den=2*n*n
    else:
        xs=[F(i*i,2*n*n) for i in range(n+1)]
        ws=[1]+[4*i for i in range(1,n)]+[2*n-1];den=4*n*n
    bounds=[[sin2(k*x) for x in xs] for k in range(1,MODES+1)]
    sl=np.array([[x[0] for x in row] for row in bounds],dtype=object)
    sh=np.array([[x[1] for x in row] for row in bounds],dtype=object)
    bases=[fixed(x*(1-x)) for x in xs]
    GRIDS[key]=(xs,ws,den,sl,sh,bases)
    return GRIDS[key]

def integral(lam,n,mid):
    xs,ws,den,sl,sh,bases=grid(n,mid)
    total=0
    for t,wt in zip(xs,ws):
        delta=lam*t*(1-t)
        if not delta:
            continue
        if delta<DELTA0:
            # V_delta(x)=E min(||Z||_circle,x), x<=1/2, Z~N(0,2delta).
            # Hence V<=E|Z|=2 sqrt(delta/pi), an elementary upper bound.
            gaussian_upper=ceildiv(2*root(fixed(delta))[1]*S,sqrtpi[0])
            values=[min(b[1],gaussian_upper) for b in bases] if mid else [0]*len(xs)
        else:
            el=[];eh=[]
            for k in range(1,MODES+1):
                x=(floorf(4*PI[0]*PI[0]*delta*k*k*S),
                   ceilf(4*PI[1]*PI[1]*delta*k*k*S))
                low,high=expminus(x)
                el.append(low//(k*k));eh.append(ceildiv(high,k*k))
            dl=np.array(el,dtype=object)@sl
            dh=np.array(eh,dtype=object)@sh
            if mid:
                values=[b[1]-COEF[0]*int(d)//(S*S) for b,d in zip(bases,dl)]
            else:
                values=[b[0]-ceildiv(COEF[1]*int(d),S*S)-1 for b,d in zip(bases,dh)]
        row=0
        for wx,value in zip(ws,values):
            if mid:assert value>=0
            rt=isqrt(max(0,value)*S)+(1 if mid else 0)
            row+=wx*rt
        total+=wt*row
    return F(4*QCOEF[int(mid)]*total,S*S*den*den)

def sqrtlo(x):return F(isqrt(floorf(x*S*S)),S)
def sqrthi(x):return sqrtlo(x)+F(1,S)

MEMORY={}
def jbounds(z):
    if z not in MEMORY:
        lam=1/z**2
        MEMORY[z]=(integral(lam,GRID,False),integral(lam,GRID,True))
        print('fresh integral',str(z),*[float(v) for v in MEMORY[z]],flush=True)
    return MEMORY[z]

def chord(l,u):
    jl,_=jbounds(l);ju,_=jbounds(u)
    slope=(jl-ju)/(1/l**2-1/u**2);intercept=ju-slope/u**2
    c=F(C0[0],S)
    if slope<0 or intercept<0:
        return c/sqrthi(u)+min(intercept*l,intercept*u)+min(slope/l,slope/u)
    def sign(x):
        v=intercept*x*x-slope
        low=v-c*sqrthi(x)/2;high=v-c*sqrtlo(x)/2
        return 1 if low>=0 else (-1 if high<=0 else 0)
    if sign(l)>=1:return c/sqrthi(l)+intercept*l+slope/l
    if sign(u)<=-1:return c/sqrthi(u)+intercept*u+slope/u
    lo,hi=l,u
    for _ in range(70):
        mid=(lo+hi)/2;sg=sign(mid)
        if sg==1:hi=mid
        elif sg==-1:lo=mid
        else:break
        if hi-lo<F(1,10**12):break
    return c/sqrthi(hi)+intercept*lo+slope/hi

def verify_tail_constant():
    # ell = pi^(-3/4) int_0^1 [t(1-t)]^(1/4) dt > .26.
    # Concavity makes ordinary trapezoids a lower bound; two isqrt steps
    # give downward fourth roots. This is independent of gamma functions.
    n=4096
    vals=[]
    for i in range(1,n):
        v=F(i*(n-i),n*n)
        vals.append(sqrtlo(sqrtlo(v)))
    beta=sum(vals,F(0))/n
    piupper=PI[1]
    pi_three_quarters=sqrthi(piupper*sqrthi(piupper))
    ell=beta/pi_three_quarters
    assert ell>F(26,100)
    # e > 65/24 by its first five Taylor terms, hence sqrt(1-e^-1)>.794.
    assert 1-F(24,65)>F(794,1000)**2
    return ell

def noncoprime_certificate():
    # Independent positive-series lower bound; no exponentials or old cache.
    pi_hi=F(PIF[1],S)
    def b_lower(z):
        values=[]
        for i in range(65):
            t=F(i,64);v=t*(1-t);delta=v/(z*z)
            w=sum((2*delta/(1+4*pi_hi*pi_hi*delta*j*j)
                   for j in range(1,65)),F(0))
            values.append(sqrtlo(v+z*z*w))
        integral=(sum(values[1:-1],F(0))+(values[0]+values[-1])/2)/64
        return sqrtlo(1/pi_hi)*integral
    c=sqrtlo(PI[0])/8
    points=[F(1,2),F(3,4),F(1)]
    bvals={z:b_lower(z) for z in points}
    hvals={(l,u):chord(l,u) for l,u in zip(points[:-1],points[1:])}
    answer={}
    for d in [2,3]:
        bounds=[(sqrtlo(2*c)+(d-1)*c)/sqrthi(F(d)),
                (TARGET+(d-1)*bvals[F(1)])/sqrthi(F(d))]
        bounds += [(hvals[l,u]+(d-1)*bvals[l])/sqrthi(F(d))
                   for l,u in zip(points[:-1],points[1:])]
        answer[str(d)]=min(bounds)
        assert answer[str(d)]>F(615,1000)
    assert 5*c>TARGET
    answer['d>=4']=(TARGET+3*c)/2
    assert answer['d>=4']>F(615,1000)
    return {key:str(value) for key,value in answer.items()}

def certify():
    ell=verify_tail_constant()
    c=F(C0[0],S);b=F(26,100)*F(794,1000);aa=c-2*b
    assert c/sqrthi(F(1,2))>TARGET
    assert aa>0 and aa/b<10
    assert aa/sqrthi(F(10))+b*sqrtlo(F(10))>TARGET
    knots=list(map(F,[1,2,3,5,10]));knots=[F(1,2),F(1),F(5,4),F(3,2),F(2),F(3),F(5),F(10)]
    todo=list(zip(knots[:-1],knots[1:]));accepted=[]
    while todo:
        l,u=todo.pop();lb=chord(l,u)
        print('interval',str(l),str(u),'lower',float(lb),flush=True)
        if lb>TARGET:accepted.append((l,u,lb));continue
        assert u-l>F(1,10000),'grid or target too ambitious'
        mid=(l+u)/2;todo.extend([(l,mid),(mid,u)])
    z=F(291,200);_,upperj=jbounds(z)
    upper=F(C0[1],S)/sqrtlo(z)+z*upperj
    assert upper<F(608275,1000000)
    noncoprime=noncoprime_certificate()
    result={'contract':'integer-outward-v1','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scale':S,'modes':MODES,'delta_cutoff':str(DELTA0),'grid':GRID,
            'cache_policy':'no disk cache read; all integrals freshly generated',
            'minimum_lower':str(TARGET),'minimum_upper':str(upper),'upper_decimal_display_only':float(upper),
            'point_z':str(z),'ell_lower':str(ell),
            'noncoprime_lower_bounds':noncoprime,
            'accepted_intervals':[[str(x) for x in row] for row in accepted],
            'integral_intervals':{str(z):[str(v) for v in b] for z,b in MEMORY.items()},
            'pi_bounds':[str(v) for v in PI]}
    dest=Path(__file__).with_name('shell_constant_integer_certificate_result.json')
    dest.write_text(json.dumps(result,indent=2))
    print('RATIONAL CERTIFICATE',float(TARGET),float(upper),flush=True)

if __name__=='__main__':certify()
