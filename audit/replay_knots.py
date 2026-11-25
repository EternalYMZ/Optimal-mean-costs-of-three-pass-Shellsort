"""Rebuild the F09 numerical certificate with bounded simultaneous Lean jobs.

Run from a P01 checkout with its matching Lean toolchain and mathlib cache:
    python replay_knots.py --repo . --jobs 2
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import re
import subprocess
import sys

FAMILY = re.compile(r"F09(?:Witness(?:Batch\d+|\d+|Upper)|CertificateLower\w+|CertificateKnots)$")
IMPORT = re.compile(r"^import Shellsort\.(\w+)\s*$",flags=re.MULTILINE)


def layers(repo):
    shellsort = repo / "Shellsort"
    files = {p.stem:p for p in shellsort.glob("F09*.lean") if FAMILY.fullmatch(p.stem)}
    if "F09WitnessUpper" not in files:
        raise ValueError("F09WitnessUpper.lean not found in the requested P01 checkout")
    graph = {name:set(IMPORT.findall(path.read_text(encoding="utf-8"))) & files.keys()
             for name,path in files.items()}
    result=[]
    while graph:
        level=sorted(name for name, deps in graph.items() if not deps)
        if not level:
            raise ValueError("Cyclic certificate import graph")
        result.append(level)
        for name in level:
            del graph[name]
        for deps in graph.values():
            deps.difference_update(level)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo",type=Path,default=Path.cwd())
    parser.add_argument("--lake",default="lake",help="lake executable, from PATH by default")
    parser.add_argument("--jobs",type=int,default=1,help="number of concurrent module subprocesses")
    parser.add_argument("--dry-run",action="store_true")
    parser.add_argument("--logs",type=Path,help="keep detailed subprocess logs; defaults to .lake/build/f09-replay-logs")
    args=parser.parse_args()
    if args.jobs<1:
        parser.error("--jobs must be positive")
    repo=args.repo.resolve()
    stages=[["F09CertificateRows"],*layers(repo)]
    for k,level in enumerate(stages):
        print(f"Stage {k+1}: {len(level)} modules",flush=True)
    if args.dry_run:
        for level in stages:
            print(" ".join(level))
        return
    if not (repo/"Shellsort/F09CertificateKnots.lean").is_file():
        parser.error("F09CertificateKnots.lean is missing")
    logs=args.logs or (repo/".lake/build/f09-replay-logs")
    logs.mkdir(parents=True,exist_ok=True)
    def build(name):
        log=logs/f"{name}.log"
        with log.open("wb") as stream:
            result=subprocess.run([args.lake,"build",f"Shellsort.{name}"],cwd=repo,stdout=stream,stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"{name} failed, see {log}")
        print(f"checked {name}",flush=True)
    for level in stages:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for job in as_completed([pool.submit(build,name) for name in level]):
                job.result()


if __name__=="__main__":
    main()
