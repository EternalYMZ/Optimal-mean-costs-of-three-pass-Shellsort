"""Directed rational quadrature of the deep-chain deficit coefficient.

The elementary-function enclosures and spatial meshes are from the checked P01
integer integral certificate. This program adds monotone tail control and time
midpoint/trapezoid quadrature of the convex deficit.
"""
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import sys

def resolve_kernel():
    here = Path(__file__).resolve().parent
    filename = "shell_constant_integer_certificate.py"
    candidates = (here.parent / "divisor-two" / filename,
                  here.parents[1] / "outputs/paper_reorganization_2026-11-25/P01/supplement" / filename)
    return next(path for path in candidates if path.is_file())


def load_kernel(path):
    spec = importlib.util.spec_from_file_location("p01_integer_kernel", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def spatial_mean(k, time, nx, upper):
    if not time:
        return F(0)
    xs, weights, denominator, sinlo, sinhi, bases = k.grid(nx, upper)
    if time < k.DELTA0:
        if not upper:
            return F(0)
        variance_bound = k.ceildiv(2*k.root(k.fixed(time))[1]*k.S, k.sqrtpi[0])
        bounds = [min(pair[1], variance_bound) for pair in bases]
    else:
        exponents = []
        for frequency in range(1,k.MODES+1):
            squared = frequency*frequency
            a = (k.floorf(4*k.PI[0]**2*time*squared*k.S),
                 k.ceilf(4*k.PI[1]**2*time*squared*k.S))
            lo,hi = k.expminus(a)
            exponents.append(lo//squared if upper else k.ceildiv(hi,squared))
        columns = k.np.array(exponents,dtype=object) @ (sinlo if upper else sinhi)
        if upper:
            bounds = [v[1]-k.COEF[0]*int(col)//(k.S*k.S) for v,col in zip(bases,columns)]
            assert min(bounds)>=0
        else:
            # The tail from modes greater than 128 is below one lattice unit.
            bounds = [max(0,v[0]-k.ceildiv(k.COEF[1]*int(col),k.S*k.S)-1)
                      for v,col in zip(bases,columns)]
    row = sum(w*(isqrt(b*k.S)+int(upper)) for w,b in zip(weights,bounds))
    return F(2*k.QCOEF[int(upper)]*row,k.S*k.S*denominator)


def calculate(k, nx, nt):
    invariant = k.root((k.PIF[0]//128,k.ceildiv(k.PIF[1],128)))
    limit_lo,limit_hi = (F(x,k.S) for x in invariant)
    nodes = [F(i*i,2*nt*nt) for i in range(nt+1)]
    upper_gap = [limit_hi-spatial_mean(k,y,nx,False) for y in nodes]
    lower = F(0)
    upper = F(0)
    for i,(a,b) in enumerate(zip(nodes,nodes[1:])):
        midpoint = (a+b)/2
        lower_gap = max(F(0),limit_lo-spatial_mean(k,midpoint,nx,True))
        lower += 2*(b-a)*lower_gap
        upper += (b-a)*(upper_gap[i]+upper_gap[i+1])
    tail = F(2,5)**18/18
    return lower,upper+tail


def main():
    kernel=resolve_kernel()
    k=load_kernel(kernel)
    lower,upper=calculate(k,128,112)
    assert lower>0 and upper>lower
    result=dict(spatial_intervals=128,time_intervals=112,
                kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                lower=str(lower),upper=str(upper),
                trillionths_lower=(10**12*lower.numerator)//lower.denominator,
                trillionths_upper=-((-10**12*upper.numerator)//upper.denominator))
    if len(sys.argv)>1:
        Path(sys.argv[1]).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print("Outward endpoints in units of 10^-12:",
          result["trillionths_lower"],result["trillionths_upper"])
    print("Integral enclosure from 128 spatial and 112 temporal intervals, 128 Fourier modes.")


if __name__=="__main__":
    main()
