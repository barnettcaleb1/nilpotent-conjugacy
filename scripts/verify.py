#!/usr/bin/env python3
"""Reproduce kernel and axiom checks for the included Lean package."""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".verification-local"
OUT.mkdir(exist_ok=True)
# Limit concurrent kernel replays on memory-constrained machines.
os.environ.setdefault("LEAN_NUM_THREADS", "2")
EXPECTED_LEAN = "4.33.1"
EXPECTED_MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
record = {
    "scope": "Included Lean declarations; see CubicTheorem.lean and VERIFICATION.md for the mathematical scope and external results not included.",
    "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    "platform": platform.platform(),
    "lean_num_threads": os.environ["LEAN_NUM_THREADS"],
    "commands": [],
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "status": "running",
}


def save() -> None:
    tmp = OUT / "checks.tmp"
    tmp.write_text(json.dumps(record, indent=2) + "\n")
    tmp.replace(OUT / "checks.json")


def run(label: str, command: list[str], timeout: int = 1200) -> str:
    print(f"Running {label}...", flush=True)
    started = dt.datetime.now(dt.timezone.utc)
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout, check=False)
    (OUT / f"{label}.log").write_text(result.stdout)
    record["commands"].append({
        "label": label, "command": command, "exit_code": result.returncode,
        "started_at": started.isoformat(),
        "completed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "log": f"{label}.log",
        "log_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
    })
    save()
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        raise RuntimeError(f"{label} failed with exit code {result.returncode}")
    return result.stdout


def source_without_comments_and_strings(text: str) -> str:
    """Remove nested Lean comments and strings before the supplementary scan."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
                out.append(" ")
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed Lean block comment")
    return "".join(out)


def inputs() -> dict[str, str]:
    paths = [ROOT / "NilpotentConjugacy.lean", ROOT / "lakefile.toml",
             ROOT / "lean-toolchain", ROOT / "lake-manifest.json",
             ROOT / "verification/AxiomAudit.lean", Path(__file__).resolve()]
    paths += sorted((ROOT / "NilpotentConjugacy").rglob("*.lean"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in paths}


try:
    record["input_sha256"] = inputs()
    sources = [ROOT / "NilpotentConjugacy.lean"] + sorted(
        (ROOT / "NilpotentConjugacy").rglob("*.lean"))
    banned = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")
    for path in sources:
        source = source_without_comments_and_strings(path.read_text())
        hit = banned.search(source)
        if hit or "skipKernelTC" in source:
            raise RuntimeError(f"Forbidden proof shortcut in {path.relative_to(ROOT)}")
    aggregate = (ROOT / "NilpotentConjugacy.lean").read_text()
    for path in sources[1:]:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        if not re.search(r"^import " + re.escape(module) + r"\s*$", aggregate, re.M):
            raise RuntimeError(f"Module missing from aggregate import: {module}")
    record["source_scan"] = "passed"
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    if f"version {EXPECTED_LEAN}," not in version:
        raise RuntimeError("Unexpected Lean version")
    revision = run("mathlib-revision", ["git", "-C", ".lake/packages/mathlib",
                                        "rev-parse", "HEAD"]).strip()
    if revision != EXPECTED_MATHLIB:
        raise RuntimeError("Unexpected Mathlib revision")
    run("build", ["lake", "build"])
    run("kernel-replay", ["lake", "env", "leanchecker", "-v", "NilpotentConjugacy"])
    axioms = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true",
                             "verification/AxiomAudit.lean"])
    match = re.search(r"Axiom audit passed for (\d+) declarations\.", axioms)
    if not match:
        raise RuntimeError("Axiom audit did not report completion")
    record["declarations_audited"] = int(match.group(1))
    if record["input_sha256"] != inputs():
        raise RuntimeError("Inputs changed during verification")
    record["status"] = "passed"
    print("Lean package passed. Consult VERIFICATION.md for the exact mathematical scope.")
except Exception as error:
    record["status"] = "failed"
    record["error"] = str(error)
    print(str(error), file=sys.stderr)
finally:
    record["completed_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
    save()

sys.exit(0 if record["status"] == "passed" else 1)
