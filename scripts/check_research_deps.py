#!/usr/bin/env python3
"""
Compute the exact transitive local-file dependency closure of LeanGeodesyResearch
(starting from LeanGeodesyResearch.lean and LeanGeodesyResearch/Axioms.lean) and
determine whether any changed file in a git diff intersects it.

Used by `.github/workflows/research_proofs.yml` so Research Proofs CI runs
whenever a certificate OR any of its transitive upstream dependencies changes,
without relying on fragile manual path filters.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)

RESEARCH_ROOTS = [
    "LeanGeodesyResearch.lean",
    "LeanGeodesyResearch/Axioms.lean",
]

INFRA_FILES = {
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    ".github/workflows/research_proofs.yml",
    "scripts/check_research_deps.py",
}


def module_to_relpath(mod: str) -> str | None:
    rel = Path(*mod.split(".")).with_suffix(".lean")
    if (ROOT / rel).is_file():
        return rel.as_posix()
    return None


def transitive_closure(seed_files: list[str]) -> set[str]:
    visited: set[str] = set()
    stack = list(seed_files)
    while stack:
        rel = stack.pop()
        if rel in visited:
            continue
        path = ROOT / rel
        if not path.is_file():
            continue
        visited.add(rel)
        text = path.read_text(encoding="utf-8")
        for match in IMPORT_RE.finditer(text):
            dep = module_to_relpath(match.group(1))
            if dep is not None and dep not in visited:
                stack.append(dep)
    return visited


def git_changed_files(base: str, head: str) -> list[str]:
    res = subprocess.run(
        ["git", "diff", "--name-only", f"{base}...{head}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return [line.strip() for line in res.stdout.splitlines() if line.strip()]


def main() -> int:
    deps = transitive_closure(RESEARCH_ROOTS) | INFRA_FILES
    if len(sys.argv) == 2 and sys.argv[1] == "--list":
        for f in sorted(deps):
            print(f)
        return 0
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} [--list | <base_sha> <head_sha>]", file=sys.stderr)
        return 2

    base, head = sys.argv[1], sys.argv[2]
    try:
        changed = git_changed_files(base, head)
    except subprocess.CalledProcessError:
        # Fallback if base commit is unavailable (e.g., force push / shallow clone): run conservatively
        print("should_run=true")
        print("reason=fallback_diff_unavailable", file=sys.stderr)
        return 0

    hits = sorted(f for f in changed if f in deps)
    print(f"Tracked transitive dependencies: {len(deps)}", file=sys.stderr)
    print(f"Changed files: {len(changed)}", file=sys.stderr)
    if hits:
        print("Triggered by:", file=sys.stderr)
        for h in hits:
            print(f"  - {h}", file=sys.stderr)
        print("should_run=true")
    else:
        print("No research proof or transitive dependency changed.", file=sys.stderr)
        print("should_run=false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
