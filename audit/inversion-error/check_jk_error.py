"""Exact uniform means of final-pass inversions for coprime Shellsort gaps.

For a fixed pivot slot, its conditional mean incident inversion count at key
value t is a polynomial in t of degree at most n-1. Evaluate the independent
binomial source laws at n rational nodes, integrate by exact interpolation,
then divide the sum of incident counts by two. Compare with physical
insertion on every permutation through eight keys and revisit the first
three nontrivial rows of Janson and Knuth's Section 10 experiment.
"""
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import comb, factorial, gcd, lcm


@cache
def integration_weights(d):
    """Integer weights for the integral at nodes i/d, with a common denominator."""
    coefficients = [1]
    for i in range(d + 1):
        product = [0] * (len(coefficients) + 1)
        for k, value in enumerate(coefficients):
            product[k] -= i * value
            product[k + 1] += value
        coefficients = product

    multiple = lcm(*range(1, d + 2))
    denominator = multiple * factorial(d)
    antiderivative = [d**k * (multiple // (k + 1)) for k in range(d + 1)]
    weights = []
    for i in range(d + 1):
        quotient = [0] * (d + 1)
        quotient[d] = coefficients[d + 1]
        for k in range(d - 1, -1, -1):
            quotient[k] = coefficients[k + 1] + i * quotient[k + 1]
        assert coefficients[0] + i * quotient[0] == 0
        integral = sum(a * b for a, b in zip(quotient, antiderivative))
        weight = integral * comb(d, i)
        weights.append(-weight if (d - i) % 2 else weight)
    assert sum(weights) == denominator
    assert sum(w * i**d * (d + 1) for i, w in enumerate(weights)) == denominator * d**d
    return weights, denominator


def source_residue_weights(length, i, d, h, g):
    """Mass of h times a Bin(length,i/d) count modulo g, scaled by d**length."""
    mass = [0] * g
    for k in range(length + 1):
        mass[h * k % g] += comb(length, k) * i**k * (d - i) ** (length - k)
    assert sum(mass) == d**length
    return mass


def absolute_moment(masses, totals, owner, center):
    coefficients = [1]
    for s, hit in enumerate(masses):
        if s == owner:
            continue
        miss = totals[s] - hit
        product = [0] * (len(coefficients) + 1)
        for k, value in enumerate(coefficients):
            product[k] += miss * value
            product[k + 1] += hit * value
        coefficients = product
    return sum(abs(k - center) * weight for k, weight in enumerate(coefficients))


def conditional_total(i, n, h, g, lengths):
    """All pivots' incident counts at t=i/(n-1), scaled by (n-1)**(n-1)."""
    d = n - 1
    sample_lengths = set(lengths) | {length - 1 for length in lengths if length}
    mass = {ell: source_residue_weights(ell, i, d, h, g) for ell in sample_lengths}
    totals = [d**ell for ell in lengths]
    result = 0
    for j in range(g):
        pivot_residue = [mass[ell - 1][(j - s) % g] if ell else 0
                         for s, ell in enumerate(lengths)]
        hit = [0] * h
        for width in range(1, g):
            target = (j + h * width) % g
            for s, ell in enumerate(lengths):
                hit[s] += mass[ell][(target - s) % g]
            center = h * width // g
            for owner, p in enumerate(pivot_residue):
                if p:
                    result += lengths[owner] * p * absolute_moment(hit, totals, owner, center)
    return result


def exact_means(n, h, g):
    assert n >= 2 and h >= 1 and g >= 1 and gcd(h, g) == 1
    d = n - 1
    weights, denominator = integration_weights(d)
    lengths = [len(range(s, n, h)) for s in range(h)]
    integral = sum(w * conditional_total(i, n, h, g, lengths) for i, w in enumerate(weights))
    actual = Fraction(integral, 2 * denominator * d**d)
    reference = 0
    for width in range(1, g):
        center = h * width // g
        reference += sum(abs(k - center) * comb(h - 1, k) * width**k * (g - width)**(h - 1 - k)
                         for k in range(h))
    return actual, Fraction(n * reference, 2 * g ** (h - 1))


def insertion(state, gap):
    result = state.copy()
    shifts = 0
    for i in range(gap, len(result)):
        key = result[i]
        pos = i
        while pos >= gap and result[pos - gap] > key:
            result[pos] = result[pos - gap]
            shifts += 1
            pos -= gap
        result[pos] = key
    return result, shifts


def physical_means(n, pairs):
    total = {pair: 0 for pair in pairs}
    for permutation in permutations(range(n)):
        previous = {h: insertion(list(permutation), h)[0] for h in {h for h, _ in pairs}}
        for h, g in pairs:
            after_g, _ = insertion(previous[h], g)
            _, shifts = insertion(after_g, 1)
            total[h, g] += shifts
    return {pair: Fraction(count, factorial(n)) for pair, count in total.items()}


def check_bounds(n, h, g, actual, reference):
    error = abs(actual - reference)
    assert error**2 <= Fraction(27, 4) * g**6 * h**3  # Uses pi > 3.
    if h <= n:
        contraction = min(Fraction(1), Fraction(3 * g**2, 2 * (n // h)))
        assert error**2 <= Fraction(3, 4) * n**2 * (g - 1)**2 * (h - 1) * contraction**2
    assert actual <= reference + n * (g - 1)
    if g == 2 and 2 < h < n:
        assert actual < reference


def main():
    pairs_checked = executions = 0
    for n in range(4, 9):
        pairs = [(h, g) for h in range(3, n) for g in range(2, h) if gcd(h, g) == 1]
        physical = physical_means(n, pairs)
        for h, g in pairs:
            actual, reference = exact_means(n, h, g)
            assert actual == physical[h, g], (n, h, g, actual, physical[h, g])
            check_bounds(n, h, g, actual, reference)
        pairs_checked += len(pairs)
        executions += len(pairs) * factorial(n)
    print(f"Exact interpolation matched physical insertion on {executions} permutation/table pairs "
          f"for all {pairs_checked} legal coprime triples with 4 <= n <= 8.")

    other = [(10, 9, 2), (11, 7, 5), (23, 5, 3), (32, 7, 4), (97, 3, 2), (4, 7, 2),
             (4, 2, 5), (4, 1, 3), (4, 3, 1)]
    for n, h, g in other:
        actual, reference = exact_means(n, h, g)
        check_bounds(n, h, g, actual, reference)
        if n <= 4:
            assert physical_means(n, [(h, g)])[h, g] == actual
    print(f"Also checked {len(other)} triples with short or unequal chains, deep chains, "
          "or redundant passes.")

    for g in range(2, 5):
        h = g**2 + 1
        n = g**2 * h
        actual, reference = exact_means(n, h, g)
        check_bounds(n, h, g, actual, reference)
        assert actual < reference
        print(f"n={n}, h={h}, g={g}: E M3={float(actual):.12f}, n psi={float(reference):.12f}, "
              f"deficit={float(reference - actual):.12f}")
        print(f"  E M3 = {actual}")
        print(f"  n psi = {reference}")


if __name__ == "__main__":
    main()
