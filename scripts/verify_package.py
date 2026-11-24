#!/usr/bin/env python3
"""Build a Lean package and audit all declarations by their defining module."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def axiom_audit_source(library, module_roots=None):
    """Audit imported modules independently of their declaration inventories."""
    # Defining-module lookup includes private names, recursors and instances.
    # collectAxioms is also used by Lean's built-in #print axioms command.
    roots = module_roots or [library]
    root_names = ", ".join(f"`{root}" for root in roots)
    return f'''import {library}
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleRoots : List Name := [{root_names}]
  let isLocal := fun (moduleName : Name) =>
    moduleRoots.any (fun root => root.isPrefixOf moduleName)
  let mut names : Array Name := #[]
  let mut counts : Array Nat := Array.replicate env.header.moduleNames.size 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if isLocal env.header.moduleNames[idx]! then
        names := names.push name
        counts := counts.modify idx.toNat (· + 1)
  for idx in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[idx]!
    if isLocal moduleName then
      let row := Json.mkObj [
        ("module", toJson moduleName.toString),
        ("declaration_count", toJson counts[idx]!)]
      logInfo m!"MODULE_AUDIT {{row.compress}}"
  for name in names.qsort Name.lt do
    let axioms ← Lean.collectAxioms name
    let idx := (env.getModuleIdxFor? name).get!
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson env.header.moduleNames[idx]!.toString),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"AXIOM_AUDIT {{row.compress}}"
'''


def check_axiom_audit(audit, expected_modules):
    """Require every source import and every compiled declaration audit record."""
    module_rows = [json.loads(line.split("MODULE_AUDIT ", 1)[1])
                   for line in audit.splitlines() if "MODULE_AUDIT " in line]
    counts = {row["module"]: row["declaration_count"] for row in module_rows}
    if not module_rows or len(counts) != len(module_rows):
        raise RuntimeError("Missing or duplicate module audit records")
    if any(type(count) is not int or count < 0 for count in counts.values()):
        raise RuntimeError("Invalid module declaration counts")
    imported_modules = set(counts)
    missing = expected_modules - imported_modules
    if missing:
        raise RuntimeError(f"Local source modules not imported: {sorted(missing)}")
    unrecorded = imported_modules - expected_modules
    if unrecorded:
        raise RuntimeError(f"Imported local modules without recorded source: {sorted(unrecorded)}")
    rows = [json.loads(line.split("AXIOM_AUDIT ", 1)[1])
            for line in audit.splitlines() if "AXIOM_AUDIT " in line]
    found = {row["name"]: sorted(row["axioms"]) for row in rows}
    if len(found) != len(rows):
        raise RuntimeError("Duplicate declaration audit records")
    actual_counts = dict.fromkeys(counts, 0)
    for row in rows:
        if row["module"] not in actual_counts:
            raise RuntimeError(f"Declaration from an unrecorded module: {row['module']}")
        actual_counts[row["module"]] += 1
    if counts != actual_counts:
        raise RuntimeError("Compiled declaration audit counts differ from the Lean environment: "
                           f"expected {counts}, found {actual_counts}")
    unexpected = {name: axioms for name, axioms in found.items() if set(axioms) - ALLOWED_AXIOMS}
    if unexpected:
        raise RuntimeError(f"Nonstandard or incomplete-proof dependencies: {unexpected}")
    return {
        "axioms": found,
        # Preserve the existing meaning: modules defining audited declarations.
        "audited_modules": sorted(module for module, count in counts.items() if count),
        "imported_modules": sorted(imported_modules),
        "declaration_free_modules": sorted(module for module, count in counts.items() if not count),
        "compiled_declarations_by_module": dict(sorted(counts.items())),
    }


def local_dependency_inputs(package_root):
    """Record editable Lake path dependencies, recursively, without build caches."""
    dependencies = {}
    visited = {package_root.resolve()}

    def visit(parent):
        manifest_path = parent / "lake-manifest.json"
        if not manifest_path.is_file():
            return
        manifest = json.loads(manifest_path.read_text())
        for package in manifest["packages"]:
            if package["type"] != "path":
                continue
            dependency = (parent / package["dir"]).resolve()
            if dependency in visited:
                continue
            visited.add(dependency)
            if not dependency.is_dir():
                raise FileNotFoundError(f"Local Lean dependency is missing: {dependency}")
            files = []
            for directory, subdirectories, names in os.walk(dependency):
                subdirectories[:] = [name for name in subdirectories
                                     if not name.startswith(".") and name != "_archive"]
                files.extend(Path(directory) / name for name in names if name.endswith(".lean"))
            files.extend(dependency / name for name in (
                "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verification.json",
                "verify.py", "setup.sh") if (dependency / name).is_file())
            dependencies[os.path.relpath(dependency, package_root)] = {
                "name": package["name"], "files": sorted(set(files))}
            visit(dependency)

    visit(package_root)
    return dependencies


def main(default_project=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=default_project,
                        required=default_project is None)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root, output = args.project.resolve(), args.output.resolve()
    config = json.loads((root / "verification.json").read_text())
    library = config["library"]
    libraries = config.get("libraries", [library])
    if (not libraries or library not in libraries or len(set(libraries)) != len(libraries)
            or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name)
                   for name in [library, *libraries])):
        raise ValueError("Expected unique single-component Lean library names including the entry")
    output.mkdir(parents=True, exist_ok=True)
    if (output / "validation.json").exists():
        raise FileExistsError("Choose a new output directory to preserve previous evidence")
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    start = time.monotonic()
    report = {"status": "running", "started_utc": datetime.now(timezone.utc).isoformat()}

    def save():
        (output / "validation.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")

    def run(command, log=None):
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if log:
            (output / log).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f"{command!r} failed:\n{result.stdout}")
        return result.stdout

    save()
    try:
        def source_files():
            return sorted(p for name in libraries for p in
                          [root / f"{name}.lean", *sorted((root / name).rglob("*.lean"))])

        sources = source_files()
        recorded = [*sources, *(root / p for p in (
            "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verification.json", "verify.py", "setup.sh")),
            *(root / p for p in config.get("verification_inputs", []))]
        project_root = root if any(root.glob(p) for p in config["manuscript_globs"]) else root.parents[1]
        manuscript = sorted({p for pattern in config["manuscript_globs"]
                             for p in project_root.glob(pattern) if p.is_file()})
        if not manuscript:
            raise RuntimeError("No manuscript files matched the configured coverage input")
        local_dependencies = local_dependency_inputs(root)
        dependency_files = [p for dependency in local_dependencies.values() for p in dependency["files"]]
        initial_hashes = {p: sha256(p) for p in [*recorded, *manuscript,
                                               *dependency_files, Path(__file__).resolve()]}
        expected_modules = {str(p.relative_to(root).with_suffix("")).replace(os.sep, ".")
                            for p in sources}
        theorem_count = sum(len(re.findall(r"^\s*(?:@\[[^\n]*\]\s*)?(?:private\s+)?"
                                          r"(?:theorem|lemma)\s+", p.read_text(), re.MULTILINE))
                            for p in sources)
        source_line_count = sum(len(p.read_text().splitlines()) for p in sources)
        for index, command in enumerate(config.get("pre_build_checks", [])):
            run(command, f"pre-build-check-{index}.log")
        run(["lake", "build"], "build.log")
        for index, command in enumerate(config.get("post_build_checks", [])):
            run(command, f"post-build-check-{index}.log")
        audit_source = axiom_audit_source(library, libraries)
        (output / "AxiomAudit.lean").write_text(audit_source)
        with tempfile.TemporaryDirectory(prefix="lean-environment-audit-") as temp:
            audit_file = Path(temp) / "AxiomAudit.lean"
            audit_file.write_text(audit_source)
            audit = run(["lake", "env", "lean", "-DwarningAsError=true", str(audit_file)], "axioms.log")
        audit_result = check_axiom_audit(audit, expected_modules)
        found = audit_result["axioms"]
        manifest = json.loads((root / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        lean_version = run(["lean", "--version"]).strip()
        lake_version = run(["lake", "--version"]).strip()
        final_sources = source_files()
        changed_inputs = [str(p) for p, digest in initial_hashes.items()
                          if not p.is_file() or sha256(p) != digest]
        dependency_inventory_changed = local_dependencies != local_dependency_inputs(root)
        if sources != final_sources or changed_inputs or dependency_inventory_changed:
            raise RuntimeError(f"Verification inputs changed during the run: {changed_inputs}; "
                               f"source inventory changed: {sources != final_sources}; "
                               f"local dependency inventory changed: {dependency_inventory_changed}")
        report.update(
            status="passed", finished_utc=datetime.now(timezone.utc).isoformat(),
            libraries=libraries,
            elapsed_seconds=round(time.monotonic() - start, 3),
            lean=lean_version, lake=lake_version,
            mathlib_revision=mathlib["rev"], source_theorem_count=theorem_count,
            inputs_unchanged_during_verification=True,
            compiled_declaration_count=len(found), **audit_result,
            lean_source_lines=source_line_count,
            source_sha256={str(p.relative_to(root)): initial_hashes[p] for p in recorded},
            local_dependencies={directory: {
                "name": dependency["name"],
                "source_sha256": {str(p.relative_to((root / directory).resolve())): initial_hashes[p]
                                  for p in dependency["files"]}}
                for directory, dependency in local_dependencies.items()},
            shared_verifier_sha256=initial_hashes[Path(__file__).resolve()],
            manuscript_sha256={str(p.relative_to(project_root)): initial_hashes[p] for p in manuscript},
            coverage=config["coverage"], not_verified=config["not_verified"])
        save()
        print(f"PASS: {theorem_count} source theorems, {len(found)} compiled declarations; "
              f"only standard logical axioms; {report['lean_source_lines']} Lean source lines")
    except Exception as error:
        report.update(status="failed", error=str(error), finished_utc=datetime.now(timezone.utc).isoformat())
        save()
        raise


if __name__ == "__main__":
    main()
