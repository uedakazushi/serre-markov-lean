#!/usr/bin/env python3
"""Package the verified import closure, logs, versions and documentation.

Usage: python3 scripts/package_verified.py /absolute/build.log /absolute/output.zip
No dependency caches, compiler binaries or development probes are included.
"""
from pathlib import Path
import hashlib
import json
import re
import sys
import zipfile

project = Path(__file__).resolve().parent.parent
log = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2]).resolve()
text = log.read_text()
if "Build completed successfully" not in text or "AUDIT_PASSED:" not in text:
    raise SystemExit("A successful whole-project build and axiom audit are required")

sources = set()
def visit(path):
    if path in sources:
        return
    sources.add(path)
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            for name in line[7:].split():
                if name == "SerreMarkov" or name.startswith("SerreMarkov."):
                    visit(project / (name.replace(".", "/") + ".lean"))
visit(project / "AxiomAudit.lean")

def lean_tokens(source):
    # Strip nested block comments, line comments and string literals.
    result, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i): depth += 1; i += 2
            elif source.startswith("-/", i): depth -= 1; i += 2
            else: i += 1
        elif source.startswith("/-", i): depth = 1; i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j == -1 else j
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\": i += 2
                elif source[i] == '"': i += 1; break
                else: i += 1
            result.append(" ")
        else: result.append(source[i]); i += 1
    return "".join(result)

for path in sources:
    forbidden = re.search(r"\b(sorry|admit|axiom|native_decide)\b", lean_tokens(path.read_text()))
    if forbidden:
        raise SystemExit(f"Forbidden source token {forbidden.group()} in {path}")
    if path.stat().st_mtime > log.stat().st_mtime:
        raise SystemExit(f"Source changed after this build log: {path}")

files = set(sources)
for name in ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "README.md",
             "PLAN_ja.md", "STATUS_ja.md", "CENSUS_ja.md", "POSITIVE_GEOMETRY_API_ja.md",
             "HANDOFF.md", "STATUS.md", "GAPS.md"]:
    files.add(project / name)
for directory in ["scripts", "tooling", "docs"]:
    files.update(p for p in (project/directory).rglob("*") if p.is_file() and
                 "__pycache__" not in p.parts and p.suffix not in [".so", ".pyc"])
blueprint = project / "blueprint"
if blueprint.is_dir():
    for path in blueprint.rglob("*"):
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        if path.suffix in [".aux", ".out", ".toc", ".paux", ".fls", ".fdb_latexmk", ".pyc"]:
            continue
        if path.parent.name == "src" and path.name in ["print.log", "print.pdf"]:
            continue
        files.add(path)

manifest = {str(p.relative_to(project)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files)}
verified_names = set(re.findall(r"VERIFIED: (\S+)", text))
def completion(headline):
    return "completed_unconditionally" if headline in verified_names else "not_completed"

report = {
    "target": "serre_markov_20261004_v4_public_bundle.zip",
    "target_sha256": "7b9986660c563d9faf83dfaaa75685be1369625c4d69527924076802a2ea8baa",
    "lean": "4.24.0",
    "mathlib_commit": "f897ebcf72cd16f89ab4577d0c826cd14afaafc7",
    "compiled_theorem_declarations": int(re.findall(r"AUDIT_PASSED: (\d+)", text)[-1]),
    "audited_definition_declarations": int(re.findall(r"AUDITED_DEFINITIONS: (\d+)", text)[-1]),
    "count_note": "Includes compiler-generated auxiliaries; not a count of manuscript theorems.",
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "full_regular_classification": completion("SerreMarkov.FullClassification.full_classification"),
    "negative_classification": completion("SerreMarkov.NegativeClassificationFull.negative_classification"),
    "degenerate_classification": completion("SerreMarkov.degenerate_classification"),
    "negative_full_fiber_formulas": completion("SerreMarkov.NegativeFamilyOrbitFibers.odd_solution_forgetful_fiber_card"),
    "positive_general_classification": completion("SerreMarkov.PositiveClassificationFull.positive_classification"),
    "all_solution_classification": completion("SerreMarkov.FullClassification.full_classification"),
    "all_forgetful_fibers_finite": completion("SerreMarkov.FullClassification.all_forgetful_fibers_finite"),
    "computable_mutation_decision": completion("SerreMarkov.FullClassification.mutationEquivalentTest_correct"),
    "computable_lattice_decision": completion("SerreMarkov.FullClassification.latticeEquivalentTest_correct"),
    "canonical_orbit_bijection": completion("SerreMarkov.FullClassification.canonical_orbit_map_bijective"),
    "positive_bounded_reduction": completion("SerreMarkov.PositiveClassificationFull.positive_reaches_bounded"),
    "prime_square_explicit_representatives": completion("SerreMarkov.FullClassification.prime_square_power_unique_representative"),
    "own_lean_files": len(sources),
    "build_log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    "source_sha256": manifest,
}
prefix = "serre_markov_lean"
with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in sorted(files):
        archive.write(path, f"{prefix}/{path.relative_to(project)}")
    archive.write(log, f"{prefix}/verification/build.log")
    archive.writestr(f"{prefix}/verification/manifest.json",
                     json.dumps(report, indent=2, ensure_ascii=False)+"\n")
    archive.writestr(f"{prefix}/verification/README.md",
        "The log records a successful whole-project build and transitive axiom audit.\n"
        "The declaration count includes generated proof helpers.\n"
        "STATUS_ja.md is the authoritative boundary of the formalized mathematics.\n")
print(json.dumps({"path": str(output), "bytes": output.stat().st_size,
                  "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
                  "lean_files": len(sources)}, ensure_ascii=False))
