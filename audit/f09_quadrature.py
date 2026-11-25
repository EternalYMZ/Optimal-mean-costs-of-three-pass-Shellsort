"""Exact proposal replay for the Lean F09 integer cubature, using only Python integers.

For each class node, mirror Eval/Quad operations, including each choice of
floor and ceiling, and record enough intermediate values to replay each row.
The signed proof obligation remains with the Lean kernel.
"""
import argparse
import json
import re
from fractions import Fraction as Q
from functools import cache
from math import ceil, floor, isqrt
from pathlib import Path

S = 1 << 160
M = 65536
SCORE_SCALE = 10**12
PI_LO = Q(314159265358979323846, 10**20)
PI_HI = Q(314159265358979323847, 10**20)
NODES = {
    "witness": ("291/200", "14986499/100000000"),
    "j1_2": ("1/2", "15594707/100000000"),
    "j3_4": ("3/4", "1937887/12500000"),
    "j1": ("1", "7684911/50000000"),
    "j5_4": ("5/4", "15183639/100000000"),
    "j11_8": ("11/8", "7533711/50000000"),
    "j23_16": ("23/16", "1875377/12500000"),
    "j3_2": ("3/2", "1866811/12500000"),
    "j7_4": ("7/4", "14622049/100000000"),
    "j2": ("2", "7134197/50000000"),
    "j3": ("3", "6400487/50000000"),
    "j5": ("5", "5309131/50000000"),
    "j10": ("10", "7830839/100000000"),
}


def pack(lo, hi):
    return max(0, floor(lo*S)), max(0, ceil(hi*S))


def root(box):
    return isqrt(box[0]*S), isqrt(box[1]*S)+1


def prod(a, b):
    return a[0]*b[0]//S, a[1]*b[1]//S+1


def exp_neg(q):
    y = q / (1 << 60)
    lo, hi = pack(1-y, 1/(1+y))
    for _ in range(60):
        lo, hi = lo*lo//S, -(-hi*hi//S)
    return lo, hi


def coefficients(delta):
    seed = exp_neg(4*PI_HI**2*delta)[0], exp_neg(4*PI_LO**2*delta)[1]
    cut = next((k for k in (2, 4, 8, 16, 32, 64)
                if 59 <= 36*delta*(k+1)**2), 128)

    @cache
    def power(n):
        if n == 0:
            return S, S
        half = power(n//2)
        square = prod(half, half)
        return prod(square, seed) if n%2 else square

    return seed, [power(k*k) for k in range(1, cut+1)]


@cache
def sin_grid(level, m):
    if not level:
        return 0, 0
    half = 1 << (level-1)
    p = m if m <= half else 2*half-m
    lo, hi = sin_grid(level-1, p)
    a, b = root((max(0,S-hi),max(0,S-lo)))
    if 2*p <= half:
        return max(0,(S-b)//2), max(0,(S-a+1)//2)
    return (S+a)//2, (S+b+1)//2


def table_lookup(path):
    """Read the exact 385 literals from the shared Lean data module."""
    source = path.read_text(encoding="utf-8")
    stride = 1 << 112

    def literal_table(name, size, step):
        line = source.split("def "+name+" (",1)[1].splitlines()[1]
        pairs = [tuple(map(int, p)) for p in re.findall(r"\((\d+),(\d+)\)",line)]
        assert len(pairs) == size, (name,len(pairs))
        result = []
        for i,(sn,cs) in enumerate(pairs):
            boxes = ((sn*stride,(sn+2)*stride),(cs*stride,(cs+2)*stride))
            for box,m in zip(boxes,(step*i,32768-step*i)):
                lo,hi = root(sin_grid(16,m))
                assert box[0] <= lo <= hi <= box[1], (name,i,m)
            result.append(boxes)
        return result

    coarse = literal_table("coarse",129,256)
    fine = literal_table("fine",256,1)

    @cache
    def lookup(u):
        u %= M
        u = min(u,M-u)
        i,j = divmod(u,256)
        a,b = coarse[i],fine[j]
        first = prod(a[0],b[1])
        second = prod(a[1],b[0])
        wave = (first[0]+second[0],first[1]+second[1])
        return prod(wave,wave)
    return lookup


PI_ROOT = root(pack(PI_LO, PI_HI))
NORMALIZER_BOX = root(pack(2*PI_LO, 2*PI_HI))


@cache
def xs(upper):
    if upper:
        return [(i*i+(i+1)**2, 2*(2*i+1)) for i in range(128)]
    return [(2*i*i, (2*i-1 if i else 0)+(2*i+1 if i < 128 else 0)) for i in range(129)]


def row_value(upper, delta, bank, trig_fn, partials=None):
    """Exact Eval.root and Quad.nodeFrom using rational, then integer arithmetic."""
    small = delta < Q(1, 10000)
    seed_upper = Q(2*root(pack(delta,delta))[1], PI_ROOT[0]) if small else None
    heights = {}
    total = 0
    for x, weight in xs(upper):
        X = Q(x,M)
        v = X*(1-X)
        if small:
            box = pack(0, min(v,seed_upper))
        else:
            relevant = 0
            for k, term in enumerate(bank,1):
                trig = trig_fn((k*x)%M)
                if upper:
                    relevant += (term[0]*trig[0]//S)//(k*k)
                else:
                    relevant += (term[1]*trig[1]//S+1)//(k*k)+1
            if upper:
                box = (0,max(0,ceil(v*S-2*relevant/PI_HI**2)))
            else:
                box = (max(0,floor(v*S-2*relevant/PI_LO**2-Q(S,2**59))),0)
        height = root(box)[int(upper)]
        heights[x] = height
        total += weight*height
    if partials is not None:
        for start in range(0,128,8):
            cells = range(start,start+8)
            if upper:
                value = sum((2*i+1)*2*heights[i*i+(i+1)**2] for i in cells)
            else:
                value = sum((2*i+1)*(heights[2*i*i]+heights[2*(i+1)**2]) for i in cells)
            partials.append(value)
        assert sum(partials) == total
    return total


def pair(q):
    return [q.numerator,q.denominator]


def evaluate(name, pad, trig_fn):
    upper = name == "witness"
    z, target = map(Q,NODES[name])
    lam = 1/(z*z)
    rows = []
    total = 0
    for i, (t,weight) in enumerate(xs(upper)):
        delta = lam * Q(t*(M-t),M*M)
        seed, bank = coefficients(delta)
        raw = row_value(upper,delta,bank,trig_fn)
        score_q = Q(raw*SCORE_SCALE,M*S)
        score = ceil(score_q)+pad if upper else max(0,floor(score_q)-pad)
        good = raw*SCORE_SCALE <= score*M*S if upper else score*M*S <= raw*SCORE_SCALE
        assert good
        total += weight*score
        rows.append(dict(i=i,t=t,deltaQ=pair(delta),seed=seed,bank=bank,
                         rowValue=raw,score=score))
    norm = Q(4*S, NORMALIZER_BOX[0 if upper else 1])
    approx = norm * Q(total,M*SCORE_SCALE)
    margin = target-approx if upper else approx-target
    return dict(node=name,z=pair(z),lam=pair(lam),upper=upper,scoreScale=SCORE_SCALE,
                proposalPad=pad,rows=rows,scoreTotal=total,approximateQ=pair(approx),
                targetQ=pair(target),marginQ=pair(margin),passes=margin>=0)


def check_published_rows(name, data):
    """Check the literal Lean scores against the recomputed row enclosures."""
    upper = data["upper"]
    if upper:
        module, declaration = "F09WitnessUpper", "witnessScore"
    else:
        module = "F09CertificateLowerJ" + name[1:].replace("_", "d")
        declaration = "scores"
    source = Path(__file__).resolve().parents[1] / "Shellsort" / (module + ".lean")
    pattern = rf"private def {declaration}\b[^\n]*?#\[([\d,\s]+)\]"
    match = re.search(pattern, source.read_text(encoding="utf-8"))
    if match is None:
        raise ValueError(f"Missing score array in {source}")
    scores = [int(field) for field in match.group(1).split(",")]
    total = 0
    for row, score, (t, weight) in zip(data["rows"], scores, xs(upper), strict=True):
        excess = score * M * S - row["rowValue"] * SCORE_SCALE
        if row["t"] != t or (excess < 0 if upper else excess > 0):
            raise ValueError(f"Published {name} score fails at row {row['i']}")
        total += weight * score
    endpoint = Q(4 * S * total, NORMALIZER_BOX[0 if upper else 1] * M * SCORE_SCALE)
    target = Q(*data["targetQ"])
    if (upper and endpoint >= target) or (not upper and endpoint <= target):
        raise ValueError(f"Published {name} scores miss their strict bound")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("nodes", nargs="*", default=None)
    parser.add_argument("--pad",type=int,default=8)
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument("--sine-table",type=Path,help="Use the literal table from F09CertificateSinTableData.lean")
    parser.add_argument("--compare",type=Path,help="Check every previously proposed score against this replay")
    parser.add_argument("--chunks-from",type=Path,help="Read checked lookup rows and output only 16 raw partial sums per row")
    args = parser.parse_args()
    trig_fn = table_lookup(args.sine_table) if args.sine_table else lambda u: sin_grid(16,u)

    args.output.mkdir(exist_ok=True,parents=True)
    for name in args.nodes or NODES:
        if name not in NODES:
            parser.error(f"unknown node {name}")
        if args.chunks_from:
            base = json.loads((args.chunks_from/f"{name}.json").read_text(encoding="utf-8"))
            chunks = []
            for row in base["rows"]:
                parts = []
                raw = row_value(base["upper"],Q(*row["deltaQ"]),row["bank"],trig_fn,parts)
                assert raw == row["rowValue"] and len(parts) == 16
                chunks.append({"i":row["i"],"partials":parts})
            (args.output/f"{name}.json").write_text(json.dumps(chunks,separators=(",",":")),encoding="utf-8")
            print(f"{name}: {len(chunks)} integer-verified blocks of 16 partials",flush=True)
            continue
        data = evaluate(name,args.pad,trig_fn)
        data["trig"] = "lookup" if args.sine_table else "sinGrid"
        if args.compare:
            previous = json.loads((args.compare/f"{name}.json").read_text(encoding="utf-8"))
            for prior,row in zip(previous["rows"],data["rows"],strict=True):
                assert (prior["i"],prior["t"],prior["seed"],prior["bank"]) == (row["i"],row["t"],list(row["seed"]),list(map(list,row["bank"])))
                carry = prior["score"]*M*S-row["rowValue"]*SCORE_SCALE
                assert (carry if data["upper"] else -carry) >= 0,(name,row["i"])

        check_published_rows(name, data)
        assert data["passes"], f"{name} fails its target"
        target = args.output / f"{name}.json"
        tmp = target.with_suffix(".tmp")
        tmp.write_text(json.dumps(data,separators=(",",":")),encoding="utf-8")
        tmp.replace(target)
        print(f"{name} {len(data['rows'])} rows, scoreTotal={data['scoreTotal']}, "
              f"approx={float(Q(*data['approximateQ'])):.13f}, "
              f"strict margin={float(Q(*data['marginQ'])):.3g}",flush=True)


if __name__ == "__main__":
    main()
