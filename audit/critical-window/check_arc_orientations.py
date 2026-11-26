"""Check the oriented use of Janson--Knuth Lemma 1 against actual same-class inversions."""
from itertools import combinations, permutations
from math import gcd


def gap_sort(state, gap):
    result = list(state)
    for start in range(gap):
        result[start::gap] = sorted(state[start::gap])
    return result


def check(state, h, g):
    d = gcd(h, g)
    H, G = h // d, g // d
    after = gap_sort(gap_sort(state, h), g)
    forward = wrapped = 0
    for cls in range(d):
        before_class = state[cls::d]
        after_class = after[cls::d]
        for pos, key in enumerate(after_class):
            j = pos % G
            if G == 1:
                continue
            endpoints = []
            for source in range(H):
                smaller = sum(other < key for other in before_class[source::H])
                endpoints.append((source + H * smaller) % G)
            arc = set()
            for width in range(1, G):
                other = (j + H * width) % G
                arc.add(other)
                expected = abs(sum(e in arc for e in endpoints) - H * width // G)
                actual = sum((i < pos and after_class[i] > key) or
                             (i > pos and after_class[i] < key)
                             for i in range(other, len(after_class), G))
                assert expected == actual, (state, h, g, pos, width)
                if j < other:
                    forward += 1
                else:
                    wrapped += 1
    return forward, wrapped


if __name__ == "__main__":
    counts = [0, 0]
    tables = 0
    for n in range(4, 8):
        for g, h in combinations(range(2, n), 2):
            for state in permutations(range(n)):
                a, b = check(state, h, g)
                counts[0] += a
                counts[1] += b
                tables += 1
    print(f"{tables} permutation/table pairs, {counts[0]} forward and "
          f"{counts[1]} wrapped incident counts verified.")
