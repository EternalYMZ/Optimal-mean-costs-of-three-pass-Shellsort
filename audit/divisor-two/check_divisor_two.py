"""Check the scalar comparisons for the best noncoprime divisor in P01.

The existing integer quadrature supplies rational enclosures of pi, J at
z = 1, and the global lower bound on H. The proof in the appendix
reduces all positive z and integer d >= 3 to the five rows below.
All square roots are rounded outwards using integer square roots. The
lower bound on W(1/4) uses four Taylor terms beyond the constant for exp(9).
Run with Python 3 and the adjacent shell_constant_integer_certificate_result.json.
"""

import json
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sqrt_lower(value):
    scale = 10**12
    return F(isqrt(value.numerator * scale**2 // value.denominator), scale)


def sqrt_upper(value):
    lower = sqrt_lower(value)
    return lower if lower**2 == value else lower + F(1, 10**12)


def check():
    data = json.loads(Path(__file__).with_name(
        "shell_constant_integer_certificate_result.json"
    ).read_text(encoding="utf-8"))
    pi_lo, pi_hi = map(F, data["pi_bounds"])
    c_lo, c_hi = sqrt_lower(pi_lo) / 8, sqrt_upper(pi_hi) / 8
    j = data["integral_intervals"]
    require(F(data["minimum_lower"]) >= F("0.6082"), "global floor of H")
    require(F(j["1"][1]) <= F("0.15371270"), "upper J at z=1")

    # B(1) <= [1/(4 sqrt(3)) + pi/9] / sqrt(pi) by the semicircle integral.
    b_upper = (1 / (4 * sqrt_lower(F(3))) + pi_hi / 9) / sqrt_lower(pi_lo)
    d2_upper = (sqrt_upper(c_hi) + F("0.15371270") + b_upper) / sqrt_lower(F(2))
    require(d2_upper < F("0.63837"), "d=2 trial exceeds its claimed upper bound")

    # W(1/4) >= (1-exp(-pi^2))/12.  The finite positive series bounds exp(9).
    exp9_lo = sum(F(9**k, factorial(k)) for k in range(5))
    w_lo = F("0.083")
    require(pi_lo**2 > 9 and (1 - 1 / exp9_lo) / 12 > w_lo, "W at 1/4")

    j_floor = F("0.15369822")
    require(j_floor <= F(j["1"][0]), "lower J at z=1")
    require(4 * j_floor**2 < c_lo, "monotonicity for 0 < z <= 1")

    def shape_floor(right):
        return sqrt_lower(c_lo / right) + j_floor * right

    def class_floor(left):
        # For z >= left and 0 < left <= 1, concavity of W gives this floor.
        return c_lo * sqrt_lower(1 + 4 * w_lo * left**2)

    rows = [
        ("(0,1/2]", shape_floor(F(1, 2)), c_lo, "0.7425", "0.22155"),
        ("[1/2,3/4]", shape_floor(F(3, 4)), class_floor(F(1, 2)), "0.6587", "0.2305"),
        ("[3/4,7/8]", shape_floor(F(7, 8)), class_floor(F(3, 4)), "0.6376", "0.24135"),
        ("[7/8,1]", shape_floor(F(1)), class_floor(F(7, 8)), "0.62438", "0.2481"),
        ("[1,infinity)", F(data["minimum_lower"]), class_floor(F(1)), "0.6082", "0.2557"),
    ]
    for interval, h_bound, b_bound, h_printed, b_printed in rows:
        h, b = F(h_printed), F(b_printed)
        require(h_bound >= h and b_bound >= b, f"rounded floors on {interval}")
        # The derivative of the profiled lower bound has the sign of (d+1)*b-h.
        require(4 * b > h, f"monotonicity in d on {interval}")
        require((h + 2 * b)**2 > 3 * F("0.646")**2, f"d=3 floor on {interval}")
    print("d=2 trial at z=1 < 0.63837")
    print("all five shape intervals for d >= 3 > 0.646")
    print("certified coefficient gap > 0.00763")


if __name__ == "__main__":
    check()
