"""Check the uniform finite variance approximation with integer arithmetic."""
from math import comb, gcd
from fractions import Fraction as F


def numerator(length, width, g, num, den, scale):
    masses = [0]*g
    for k in range(length+1):
        masses[k % g] += comb(length,k)*num**k*(den-num)**(length-k)
    hits = [sum(masses[(a-x) % g] for a in range(1,width+1))
            * (scale // den**length) for x in range(g)]
    return hits, [p*(scale-p) for p in hits]


def main():
    cases=0
    maximum=F(0)
    max_case=None
    for h in range(2,14):
        for g in range(2,15):
            if gcd(h,g)!=1:
                continue
            inverse=pow(h,-1,g)
            for width in range(1,g):
                center=h*width//g
                for num,den in ((0,1),(1,5),(1,2),(3,4),(1,1)):
                    for m in (0,1,3,8):
                        scale=den**(m+1)
                        su,sv=numerator(m,width,g,num,den,scale)
                        lu,lv=numerator(m+1,width,g,num,den,scale)
                        assert sum(abs(lv[i]-sv[i]) for i in range(g))<=2*scale**2
                        for shift in range(g):
                            phases=[(inverse*s-shift) % g for s in range(h)]
                            second=[sv[x] for x in phases]
                            prob=[su[x] for x in phases]
                            for rem in range(h):
                                if m or rem:
                                    # Check both ends over every deleted owner, including all feasible ones.
                                    observed=sum(second)
                                    nominal=(h-rem)*sum(sv)+rem*sum(lv)
                                    err=max(abs(g*(observed-max(second))-nominal),
                                            abs(g*(observed-min(second))-nominal))
                                    assert 4*err<=25*g*scale**2
                                    if err*maximum.denominator>maximum.numerator*g*scale**2:
                                        maximum=F(err,g*scale**2)
                                        max_case=(m*h+rem,h,g,width,shift,num,den)
                                    total=sum(prob)
                                    assert total-max(prob)>=scale*(center-1)
                                    assert total-min(prob)<=scale*(center+1)
                                    cases+=h
                                second[rem]=lv[phases[rem]]
                                prob[rem]=lu[phases[rem]]
    print("Integer owner/arc/threshold variance and drift checks:",cases)
    print("Largest observed absolute variance error:",maximum)
    print("(n,h,g,width,phase_shift,t_numerator,t_denominator):",max_case)


if __name__=="__main__":
    main()
