"""Exact long-array deficit for fixed coprime gaps, using the occupancy Poisson equation."""
from fractions import Fraction
from functools import cache
from itertools import product
from math import comb, factorial, gcd, prod
import json
from pathlib import Path
import sys


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, parts - 1):
            yield (first,) + tail


@cache
def orbit(counts):
    return min(counts[i:] + counts[:i] for i in range(len(counts)))


def incident_sum(state, h, g):
    total = 0
    for j, owners in enumerate(state):
        count = 0
        for width in range(1, g):
            count += state[(j + width) % g]
            total += owners * abs(count - h * width // g)
    return total


def reference(h, g):
    numerator = sum(abs(k - h * width // g) * comb(h-1, k) *
                    width**k * (g-width)**(h-1-k)
                    for width in range(1, g) for k in range(h))
    return Fraction(numerator, 2*g**(h-1))


def fraction_free_solve(matrix):
    """Bareiss elimination on the integer augmented matrix, then exact substitution."""
    size = len(matrix)
    rows = [row[:] for row in matrix]
    previous = 1
    for col in range(size-1):
        switch = next(i for i in range(col, size) if rows[i][col])
        rows[col], rows[switch] = rows[switch], rows[col]
        pivot = rows[col][col]
        for i in range(col+1, size):
            multiplier = rows[i][col]
            for j in range(col+1, size+1):
                value = pivot * rows[i][j] - multiplier * rows[col][j]
                quotient, remainder = divmod(value, previous)
                assert remainder == 0
                rows[i][j] = quotient
            rows[i][col] = 0
        previous = pivot
    solution = [Fraction(0)] * size
    for i in reversed(range(size)):
        remainder = rows[i][-1] - sum(rows[i][j] * solution[j] for j in range(i+1, size))
        solution[i] = Fraction(remainder, rows[i][i])
    return solution


def compute(h, g):
    assert g >= 2 and h >= 2 and gcd(h, g) == 1
    states = sorted({orbit(c) for c in compositions(h, g)})
    index = {state: i for i, state in enumerate(states)}
    count = len(states)
    assert count * g == comb(h+g-1, g-1)
    stationary = [g * factorial(h) // prod(factorial(c) for c in state) for state in states]
    assert sum(stationary) == g**h
    mean = 2*h*reference(h, g)
    rewards = [incident_sum(c, h, g) for c in states]
    assert sum(a*b for a,b in zip(stationary,rewards)) == g**h * mean
    transitions = []
    matrix = []
    for i,c in enumerate(states):
        rates = {}
        for j,rate in enumerate(c):
            if not rate:
                continue
            nxt = list(c)
            nxt[j] -= 1
            nxt[(j+1) % g] += 1
            dst = index[orbit(tuple(nxt))]
            rates[dst] = rates.get(dst, 0) + rate
        transitions.append(rates)
        row = [0] * (count+1)
        row[i] = h
        for j,rate in rates.items():
            row[j] -= rate
        row[-1] = mean.numerator - mean.denominator * rewards[i]
        matrix.append(row)
    matrix[-1] = stationary + [0]
    scaled = fraction_free_solve(matrix)
    values = [q/mean.denominator for q in scaled]
    assert sum(a*b for a,b in zip(stationary,values)) == 0
    for i,rates in enumerate(transitions):
        assert h*values[i] - sum(w*values[j] for j,w in rates.items()) == mean-rewards[i]
    start = [0] * g
    inv = pow(h,-1,g)
    for s in range(h):
        start[(inv*s) % g] += 1
    ans = values[index[orbit(tuple(start))]]
    return count, ans


def main():
    # Select by a declared state-space budget, independently of any sign.
    pairs = [(h,g) for h,g in product(range(2,14),range(2,9))
             if gcd(h,g)==1 and comb(h+g-1,g-1)//g <= 105]
    rows = []
    for h,g in pairs:
        size, result = compute(h,g)
        if h == 2:
            assert result == Fraction((g*g-1)*(g*g-5),96*g)
        if (h,g) == (4,3):
            assert result == Fraction(55,81)
        rows.append(dict(h=h,g=g,orbits=size,deep_deficit=str(result)))
    if len(sys.argv)>1:
        Path(sys.argv[1]).write_text(json.dumps(rows,indent=2)+"\n",encoding="utf-8")
    print("Solved",len(rows),"Poisson equations exactly, including",
          sum(r["g"]<r["h"] for r in rows),"strictly descending gap pairs.")
    print("Positive long-array deficits:",sum(Fraction(r["deep_deficit"])>0 for r in rows))
    for r in rows:
        if (r["h"],r["g"]) in [(2,3),(3,2),(4,3),(5,3),(5,4),(7,3),(7,4)]:
            print((r["h"],r["g"]),r["orbits"],r["deep_deficit"])


if __name__ == "__main__":
    main()
