"""Exact finite checks for the second-pass window estimate in Lemma 2.2.

Only Python's standard library is required. The general inequalities are proved
in the paper. This program tests them against a separate two-chain count.
"""
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import comb, factorial


def integrated_difference(m):
    """Beta-integrate the positive part of two independent Bin(m,t) counts."""
    total = Fraction(0)
    for y in range(1, m + 1):
        for z in range(y):
            total += Fraction((y - z) * comb(m, y) * comb(m, z),
                              (2 * m + 1) * comb(2 * m, y + z))
    return total


@cache
def inversion_probability(length_a, length_b, rank_a, rank_b):
    """P(A_(rank_a) > B_(rank_b)) for a uniform interleaving of two chains."""
    prefix = rank_a + rank_b - 1
    favorable = sum(comb(length_a, k) * comb(length_b, prefix - k)
                    for k in range(max(0, prefix - length_b), rank_a))
    return Fraction(favorable, comb(length_a + length_b, prefix))


def second_pass_mean(n, h, g):
    lengths = [len(range(r, n, h)) for r in range(h)]
    total = Fraction(0)
    for i in range(n):
        for j in range(i + g, n, g):
            if i % h != j % h:
                total += inversion_probability(lengths[i % h], lengths[j % h],
                                               i // h + 1, j // h + 1)
    return total


def insertion_pass(values, gap):
    a = list(values)
    shifts = 0
    for i in range(gap, len(a)):
        value = a[i]
        j = i
        while j >= gap and value < a[j - gap]:
            a[j] = a[j - gap]
            j -= gap
            shifts += 1
        a[j] = value
    return a, shifts


def closed_form(m):
    return Fraction(m * 4**m, 4 * (2 * m + 1) * comb(2 * m, m))


def main():
    for m in range(31):
        assert integrated_difference(m) == closed_form(m), m
    cases = executions = distinct_means = 0
    for n in range(1, 41):
        for h in range(1, n + 1):
            window = closed_form(n // h)
            totals = [0] * (h + 1)
            if n <= 7:
                for order in permutations(range(n)):
                    after, _ = insertion_pass(order, h)
                    for g in range(1, h + 1):
                        totals[g] += insertion_pass(after, g)[1]
                        executions += 1
            for g in range(1, h + 1):
                mean = second_pass_mean(n, h, g)
                rho = Fraction(h, g)
                assert n * ((rho - 1) * window - 2 * rho) <= mean <= n * (rho * window + 2 * rho), (n, h, g)
                if n <= 7:
                    assert mean == Fraction(totals[g], factorial(n)), (n, h, g)
                    distinct_means += 1
                cases += 1
    assert (cases, distinct_means, executions) == (11480, 84, 158323)
    print(f"31 beta integrals, {cases} window inequalities, {distinct_means} exact means, {executions} executions")


if __name__ == "__main__":
    main()
