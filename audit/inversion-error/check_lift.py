"""Recheck the ordinary four-pass residue-class identity with exact means.

Run python check_lift.py. Python's standard library is sufficient. The subset
calculation tracks one marked rank at a time. The permutation test runs ordinary
insertion directly.
"""
import itertools
import math
import random
from fractions import Fraction
from functools import lru_cache


@lru_cache(maxsize=None)
def means(size, gaps):
    """Average over each possible set of smaller slots and each marked key.

    Given a set of s original smaller slots, the next rank is equally likely
    at any remaining slot. Each (set, marked slot) event has probability
    1/(n*binom(n-1,s)). Before every pass the candidate multiplicities tell
    where these marked keys occupy a slot for this particular set. Actual
    insertion of the marked key shifts every earlier larger key on its chain
    and stops at one earlier smaller key precisely when an earlier smaller key
    exists. Every candidate on the chain ends up after all smaller keys.
    """
    chains = [tuple(tuple(range(start, size, gap)) for start in range(gap)) for gap in gaps]
    shifts = [[0] * size for _ in gaps]
    stops = [[0] * size for _ in gaps]
    for mask in range((1 << size) - 1):
        smaller = tuple((mask >> slot) & 1 for slot in range(size))
        count = sum(smaller)
        candidates = [1 - occupied for occupied in smaller]
        for index, stage in enumerate(chains):
            sorted_smaller = [0] * size
            new_candidates = [0] * size
            for chain in stage:
                small_before = 0
                mass = 0
                for rank, slot in enumerate(chain):
                    weight = candidates[slot]
                    shifts[index][count] += weight * (rank - small_before)
                    if small_before:
                        stops[index][count] += weight
                    small_before += smaller[slot]
                    mass += weight
                for slot in chain[:small_before]:
                    sorted_smaller[slot] = 1
                if mass:
                    new_candidates[chain[small_before]] = mass
            smaller, candidates = sorted_smaller, new_candidates

    pass_means = []
    for shift_bands, stop_bands in zip(shifts, stops):
        moves = comparisons = Fraction()
        for count in range(size):
            denominator = size * math.comb(size - 1, count)
            moves += Fraction(shift_bands[count], denominator)
            comparisons += Fraction(shift_bands[count] + stop_bands[count], denominator)
        pass_means.append((moves, comparisons))
    total = tuple(map(sum, zip(*pass_means)))
    return total, pass_means[-1]


def full_schedules(size):
    for divisor in range(2, size):
        for first in range(3, (size - 1) // divisor + 1):
            for second in range(2, first):
                yield divisor, first, second


def insert_passes(array, gaps):
    state = list(array)
    moves = comparisons = 0
    for gap in gaps:
        for pos in range(gap, len(state)):
            key = state[pos]
            cursor = pos
            while cursor >= gap:
                comparisons += 1
                if state[cursor - gap] < key:
                    break
                state[cursor] = state[cursor - gap]
                moves += 1
                cursor -= gap
            state[cursor] = key
    return (moves, comparisons), state


def check_input(array, divisor, first, second):
    raw, sorted_raw = insert_passes(array, (divisor * first, divisor * second, divisor, 1))
    prefix, prefix_state = insert_passes(array, (divisor * first, divisor * second, divisor))
    _, direct_state = insert_passes(array, (divisor,))
    assert prefix_state == direct_state
    tail, sorted_tail = insert_passes(direct_state, (1,))
    local_means = [insert_passes(array[index::divisor], (first, second, 1))[0]
                   for index in range(divisor)]
    assert sorted_raw == sorted_tail == sorted(array)
    for counter in range(2):
        assert prefix[counter] == sum(local[counter] for local in local_means)
        assert raw[counter] == prefix[counter] + tail[counter]


def arctangent_bounds(inv, terms):
    value = sum((Fraction((-1) ** t, (2 * t + 1) * inv ** (2 * t + 1))
                 for t in range(terms)), Fraction())
    next_term = Fraction((-1) ** terms, (2 * terms + 1) * inv ** (2 * terms + 1))
    return min(value, value + next_term), max(value, value + next_term)


def check_coefficient_bounds():
    a_lo, a_hi = arctangent_bounds(5, 12)
    b_lo, b_hi = arctangent_bounds(239, 4)
    pi_lo, pi_hi = 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo
    c_lo, c_hi = Fraction("0.22155673135"), Fraction("0.22155673138")
    s_lo, s_hi = Fraction("1.41421356236"), Fraction("1.41421356239")
    assert 64 * c_lo**2 < pi_lo < pi_hi < 64 * c_hi**2
    assert s_lo**2 < 2 < s_hi**2

    # These four rational endpoints are inputs from the manuscript's enclosures.
    k_lo, k_hi = Fraction("0.60822153"), Fraction("0.60827485406")
    j_lo, j_hi = Fraction("0.15369822"), Fraction("0.15371270")
    assert Fraction("0.62525495") < Fraction(1, 4) + c_lo + j_lo
    assert Fraction(1, 4) + c_hi + j_hi < Fraction("0.62526944")
    assert Fraction(1, 4) + c_lo + j_lo - k_hi > Fraction("0.01698009")
    jk_lift_hi = (Fraction(1, 4) + 2 * c_hi + j_hi) / s_lo
    assert jk_lift_hi < Fraction("0.59880")
    assert k_lo - jk_lift_hi > Fraction("0.00942")
    assert Fraction("0.5867418") < (k_lo + c_lo) / s_hi
    assert (k_hi + c_hi) / s_lo < Fraction("0.5867796")
    assert k_lo - (k_lo + c_hi) / s_lo > Fraction("0.0214796")
    assert 3 * c_lo > k_hi


def main():
    exact_tables = ragged_identity = divisible_optima = pointwise = 0
    divisors = set()
    for size in range(7, 15):
        divisible = {}
        for divisor, first, second in full_schedules(size):
            quot, rem = divmod(size, divisor)
            actual, _ = means(size, (divisor * first, divisor * second, divisor, 1))
            _, tail = means(size, (divisor, 1))
            short, _ = means(quot, (first, second, 1))
            long = means(quot + 1, (first, second, 1))[0] if rem else short
            for counter in range(2):
                expected = ((divisor - rem) * short[counter] +
                            rem * long[counter] + tail[counter])
                assert actual[counter] == expected
            exact_tables += 1
            divisors.add(divisor)
            if rem and first == quot:
                ragged_identity += 1
            if rem == 0:
                divisible.setdefault(divisor, []).append((actual, short))
        for divisor, candidates in divisible.items():
            _, tail = means(size, (divisor, 1))
            for counter in range(2):
                global_min = min(actual[counter] for actual, _ in candidates)
                local_min = min(local[counter] for _, local in candidates)
                assert global_min == divisor * local_min + tail[counter]
            divisible_optima += 1

    for size in (7, 8):
        for table in full_schedules(size):
            for array in itertools.permutations(range(size)):
                check_input(array, *table)
                pointwise += 1

    rng = random.Random(20261126)
    for size in range(9, 25):
        for table in full_schedules(size):
            for _ in range(5):
                array = list(range(size))
                rng.shuffle(array)
                check_input(array, *table)
                pointwise += 1
    print(f"Exact table means for both counters: {exact_tables} across n=7..14, d={sorted(divisors)}")
    print(f"Ragged cases with a short-class identity gap: {ragged_identity}")
    print(f"Divisible-size optimality checks for both counters: {divisible_optima}")
    print(f"Pointwise ordinary insertion checks: {pointwise:,}; exhaustive for every table at n=7,8")
    check_coefficient_bounds()
    print("Rational coefficient implications of the kappa and J(1) enclosures passed.")
    print("0.62525495 < K_JK < 0.62526944; K_JK - kappa > 0.01698009.")
    print("K_JK lifted with d=2 is below 0.59880; its gain over kappa exceeds 0.00942.")
    print("0.5867418 < f(2) < 0.5867796; kappa - f(2) > 0.0214796; 3c > kappa.")


if __name__ == "__main__":
    main()
