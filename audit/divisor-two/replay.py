"""Run inside a built proof project: lake env python replay_scale_penalty.py SOURCE [ROOT ...]."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


source = Path(sys.argv[1]).resolve()
roots = sys.argv[2:] or ["Shellsort.F09.fixed_shape_scale_penalty", "Shellsort.F09.fixed_shape_scale_penalty_lower"]
axioms = ["propext", "Classical.choice", "Quot.sound"]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


with tempfile.TemporaryDirectory(prefix="p01-scale-") as tmp:
    scratch = Path(tmp)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(scratch) + os.pathsep + env["LEAN_PATH"]
    olean = scratch / (source.stem + ".olean")
    proof = scratch / "proof.ndjson"
    statements = scratch / "statements.txt"
    config = scratch / "nanoda.json"
    compiled = subprocess.run([shutil.which("lean"), "-R", source.parent, "-o", olean, source],
                              env=env, check=True, capture_output=True, text=True)
    with proof.open("wb") as out:
        subprocess.run([shutil.which("leanexport"), source.stem, "--", *roots], env=env, check=True, stdout=out)
    statements.touch()
    config.write_text(json.dumps({
        "export_file_path": str(proof), "permitted_axioms": axioms,
        "unpermitted_axiom_hard_error": True, "unsafe_permit_all_axioms": False,
        "nat_extension": True, "string_extension": True, "pp_declars": roots,
        "pp_output_path": str(statements), "pp_options": {"proofs": False},
        "print_success_message": True,
    }), encoding="utf-8")
    checked = subprocess.run([shutil.which("nanoda_bin"), config], env=env, check=True,
                             capture_output=True, text=True, encoding="utf-8")
    types = statements.read_text(encoding="utf-8")
    if any("theorem " + name + " " not in types for name in roots):
        raise ValueError("Nanoda did not print all requested theorem types")
    with proof.open("rb") as stream:
        metadata = json.loads(stream.readline())["meta"]
    print(json.dumps({
        "invocation": " ".join(["lake env python replay_scale_penalty.py", source.name, *sys.argv[2:]]),
        "export_invocation": "leanexport " + source.stem + " -- " + " ".join(roots),
        "roots": roots, "permitted_axioms": axioms,
        "source_sha256": digest(source), "proof_sha256": digest(proof),
        "proof_bytes": proof.stat().st_size, "metadata": metadata,
        "lean_output": compiled.stdout.strip(), "lean_stderr": compiled.stderr.strip(),
        "nanoda_output": checked.stdout.strip(), "nanoda_stderr": checked.stderr.strip(),
        "statements": types.strip(),
    }, indent=2))
