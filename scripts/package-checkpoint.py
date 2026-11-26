#!/usr/bin/env python3
"""Package the verified public import closure, source hashes and build evidence."""

from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import argparse
import json
import re
import zipfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    selected: set[Path] = set()

    def visit(module: str) -> None:
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file() or path in selected:
            return
        selected.add(path)
        source = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
        for imports in re.findall(r"^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)", source, re.M):
            for dep in imports.split("--", 1)[0].split():
                if dep == "UniformTuran" or dep.startswith(("UniformTuran.", "Checks.")):
                    visit(dep)

    for module in ("UniformTuran", "Checks.Axioms", "Checks.CombinatorialAudit"):
        visit(module)
    proof_module_count = len(selected)
    for filename in (
        "README.md", "LICENSE", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        ".gitignore", "Challenge.lean", "Solution.lean", "comparator.json",
        "formalization.yaml", ".github/workflows/palomar-preflight.yml",
    ):
        selected.add(root / filename)
    for directory in ("docs", "scripts"):
        selected.update(p for p in (root / directory).rglob("*") if p.is_file() and "__pycache__" not in p.parts)

    files = {str(p.relative_to(root)): p.read_bytes() for p in sorted(selected)}
    verification = json.loads((root / "docs/verification-summary.json").read_text())
    module_count = sum(name.endswith(".lean") for name in files)
    build_log = (root / "docs/verification-build.txt").read_text()
    if verification.get("exit_code") != 0 or verification.get("built_modules") != proof_module_count:
        raise SystemExit("The verification summary must cover the current public import closure.")
    if f"Built {proof_module_count} local Lean modules successfully." not in build_log:
        raise SystemExit("The complete successful build log is required.")
    if re.search(r"\b(?:warning|error):", build_log):
        raise SystemExit("Resolve the diagnostics before packaging the verified release.")
    audited = verification.get("audited_declarations")
    if f"Axiom audit passed for {audited} project declarations." not in build_log:
        raise SystemExit("The transitive axiom audit must match the verification summary.")
    complete = verification.get("main_theorem_complete") is True
    if complete and "UniformTuran/Main.lean" not in files:
        raise SystemExit("A completed release must include the unconditional main proof.")
    manifest = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "paper": "https://arxiv.org/abs/2611.06964",
        "main_theorem_complete": complete,
        "remaining_obligation": verification.get("remaining_obligation"),
        "proof_entrypoint": "UniformTuran.paperMainTheorem" if complete else None,
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "mathlib_commit": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
        "lean_module_count": module_count,
        "proof_build_modules": proof_module_count,
        "lean_source_lines": sum(data.count(b"\n") for name, data in files.items() if name.endswith(".lean")),
        "audited_declarations": audited,
        "permitted_axioms": verification.get("permitted_axioms"),
        "portable_lake_build_executed": verification.get("portable_lake_build_executed", False),
        "sha256": {name: sha256(data).hexdigest() for name, data in files.items()},
    }
    files["CHECKPOINT.json"] = (json.dumps(manifest, indent=2, ensure_ascii=False) + "\n").encode()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in files.items():
            entry = zipfile.ZipInfo("uniform-turan/" + name)
            entry.create_system = 3
            executable = name in ("scripts/build-local.sh", "scripts/lean-local.sh")
            entry.external_attr = (0o100755 if executable else 0o100644) << 16
            archive.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(json.dumps({"path": str(args.output.resolve()), "bytes": args.output.stat().st_size,
                      "lean_modules": manifest["lean_module_count"],
                      "lean_source_lines": manifest["lean_source_lines"],
                      "main_theorem_complete": complete}, ensure_ascii=False))


if __name__ == "__main__":
    main()
