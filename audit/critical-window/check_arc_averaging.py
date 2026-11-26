"""Regression for the width average in the fixed-divisor remainder (Python 3).

Use exact binomial phase masses, then integrate the square root of their
piecewise affine arc variance explicitly. No uniform asymptotic constant
is fitted or estimated from this check.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb


def phase_kernel(g, trials, threshold):
    a, b = threshold.numerator, threshold.denominator
    mass = [0] * g
    for k in range(trials + 1):
        mass[k % g] += comb(trials, k) * a**k * (b-a)**(trials-k)
    distance_mass = [0] * (g // 2 + 1)
    for i, left in enumerate(mass):
        for j, right in enumerate(mass):
            distance = min(abs(i-j), g-abs(i-j))
            distance_mass[distance] += left * right
    total = b**(2 * trials)
    assert sum(distance_mass) == total
    return [Fraction(sum(count * min(k, g-k, d)
                         for d, count in enumerate(distance_mass)), g * total)
            for k in range(g + 1)]


def check_width_average(g, trials, threshold):
    variance = phase_kernel(g, trials, threshold)
    assert variance == variance[::-1] and variance[0] == 0
    assert all(variance[k] <= variance[k+1] for k in range(g // 2))
    with localcontext() as context:
        context.prec = 45
        heights = [(Decimal(v.numerator) / Decimal(v.denominator)).sqrt()
                   for v in variance]
        variation = sum(abs(x-y) for x, y in zip(heights, heights[1:]))
        discrete = sum(heights[:-1]) / g
        # E min(x,1-x,dist(T,Z)) is affine on each width cell: all kinks
        # of each clipped tent are grid nodes, also for odd g.
        integral = sum((2*(x*x + x*y + y*y) / (3*(x+y)) if x+y else Decimal(0))
                       for x, y in zip(heights, heights[1:])) / g
        tolerance = Decimal("1e-38")
        assert -tolerance <= integral-discrete <= variation/g + tolerance
        assert abs(variation - 2 * max(heights)) < tolerance
        # The width-zero term is identically zero and excluded from the
        # singular inverse-root majorant used after variance comparison.
        envelope_mean = sum((Decimal(g)/min(k, g-k)).sqrt()
                            for k in range(1, g)) / g
        assert envelope_mean < 3


if __name__ == "__main__":
    checked = 0
    for g in range(2, 20):
        for m in (g, g*g, g*g+1):
            for t in map(Fraction, ("0", "1/127", "1/4", "1/2", "126/127", "1")):
                check_width_average(g, m, t)
                checked += 1
    print(f"{checked} binomial phase profiles verified, including both threshold endpoints.")
