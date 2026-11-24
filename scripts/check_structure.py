#!/usr/bin/env python3
"""Check the unified source graph, its subject layering and migration inventory without writing files.

This is a source-structure check, not a substitute for Lean compilation or the
compiled-declaration axiom audit performed by verify.py. Original source files
are provenance records, not live dependencies; their current contents are not
read or compared here.
"""

from __future__ import annotations

import argparse
from collections import Counter
from graphlib import CycleError, TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import sys


ROOT = "PLAStochastic"
LIBRARIES = (ROOT,)
ORIGIN_PACKAGES = {
    "BrownianAffine": "brownian-affine-constants/theory/lean",
    "SwingRepair": "swing-filter/theory/lean",
    "PGM": "pgm-analysis/theory/lean",
}
RESULTS = "Results"
# Subject areas and the areas each may import (Mathlib-style layering).
ALLOWED_IMPORTS = {
    "ForMathlib": {"ForMathlib"},
    "Brownian": {"ForMathlib", "Brownian"},
    "Affine": {"ForMathlib", "Brownian", "Affine"},
    "Swing": {"ForMathlib", "Brownian", "Affine", "Swing"},
    "Index": {"ForMathlib", "Brownian", "Affine", "Index"},
    RESULTS: {"ForMathlib", "Brownian", "Affine", "Swing", "Index"},
}
UPSTREAM_LIBRARIES = {
    "Mathlib": "mathlib",
    "Batteries": "batteries",
    "Aesop": "aesop",
    "Qq": "Qq",
    "ProofWidgets": "proofwidgets",
    "Plausible": "plausible",
    "ImportGraph": "importGraph",
    "LeanSearchClient": "LeanSearchClient",
    "Cli": "Cli",
}
BUILTIN_LIBRARIES = {"Init", "Lean", "Std"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*|[^\s]")
RAW_STRING = re.compile(r'r(#+)?"')
CHARACTER = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")
SHA256 = re.compile(r"[0-9a-f]{64}")
GIT_REVISION = re.compile(r"[0-9a-f]{40}")
FORBIDDEN_TOKEN = re.compile(r"(?<![\w'])(?:sorry|admit|axiom|sorryAx)(?![\w'])")
IMPORT_TOKEN = re.compile(r"(?<![\w'])import(?![\w'])")
BODY_COMMANDS = {
    "abbrev", "attribute", "axiom", "builtin_initialize", "class", "constant",
    "def", "declare_syntax_cat", "deriving", "elab", "elab_rules", "end",
    "example", "export", "inductive", "initialize", "instance", "lemma",
    "local", "macro", "macro_rules", "mutual", "namespace", "noncomputable",
    "opaque", "open", "protected", "scoped", "section", "set_option",
    "structure", "syntax", "theorem", "universe", "universes", "variable",
    "variables",
}
IMPORT_MODIFIERS = {"public", "private", "meta"}
HEADER_BOUNDARIES = BODY_COMMANDS | IMPORT_MODIFIERS | {"import", "module", "prelude"}


class StructureError(Exception):
    """A source graph or provenance invariant was violated."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise StructureError(message)


def blank(text: str) -> str:
    """Preserve source offsets and line numbers while masking non-code text."""
    return "".join("\n" if char == "\n" else " " for char in text)


def literal(text: str) -> str:
    """Keep a placeholder so unsupported literals cannot disappear in a header."""
    return "¤" + blank(text[1:])


def scrub_lean(text: str, label: str = "source") -> str:
    """Mask nested comments, literals and escaped identifiers in Lean source.

    Unsupported interpolated strings fail explicitly: masking their embedded
    expressions could otherwise hide a proof hole. Ordinary and raw strings,
    character literals, and nested block comments are handled independently.
    """
    output: list[str] = []
    i = 0
    length = len(text)
    while i < length:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = length if end == -1 else end
            output.append(blank(text[i:end]))
            i = end
        elif text.startswith("/-", i):
            start = i
            i += 2
            depth = 1
            while i < length and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, f"{label}: unterminated block comment")
            output.append(blank(text[start:i]))
        elif text[i] == "«":
            end = text.find("»", i + 1)
            require(end != -1, f"{label}: unterminated escaped identifier")
            output.append(literal(text[i:end + 1]))
            i = end + 1
        else:
            raw = None
            if text[i] == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
                raw = RAW_STRING.match(text, i)
            if raw:
                delimiter = '"' + (raw.group(1) or "")
                end = text.find(delimiter, raw.end())
                require(end != -1, f"{label}: unterminated raw string")
                end += len(delimiter)
                output.append(literal(text[i:end]))
                i = end
            elif text[i] == '"':
                require(i == 0 or text[i - 1] != "!",
                        f"{label}: interpolated strings require a supported expression scanner")
                start = i
                i += 1
                while i < length:
                    if text[i] == "\\":
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise StructureError(f"{label}: unterminated string")
                require(i <= length, f"{label}: unterminated string escape")
                output.append(literal(text[start:i]))
            elif text[i] == "'" and (char := CHARACTER.match(text, i)):
                output.append(literal(char.group()))
                i = char.end()
            else:
                output.append(text[i])
                i += 1
    return "".join(output)


def parse_imports(code: str, label: str = "source") -> list[str]:
    """Parse a conservative Lean import header, including multiline imports.

    Module names use the ASCII spelling established by this repository. An
    unsupported header form or an import outside the header is an error, never
    a silently ignored dependency. The Lean build remains the syntax authority.
    """
    tokens = iter(TOKEN.finditer(code))
    current = next(tokens, None)
    imports: list[str] = []
    positions: set[int] = set()
    prefix: set[str] = set()
    while current is not None:
        word = current.group()
        if word in {"module", "prelude"}:
            require(not imports and word not in prefix, f"{label}: unexpected {word} in import header")
            prefix.add(word)
            current = next(tokens, None)
            continue
        modifiers: list[str] = []
        while current is not None and current.group() in IMPORT_MODIFIERS:
            modifiers.append(current.group())
            current = next(tokens, None)
        if current is None or current.group() != "import":
            break
        require(len(modifiers) == len(set(modifiers)) and not {"public", "private"} <= set(modifiers),
                f"{label}: unsupported import modifiers {modifiers}")
        positions.add(current.start())
        current = next(tokens, None)
        names: list[str] = []
        last_end = 0
        while current is not None and current.group() not in HEADER_BOUNDARIES:
            word = current.group()
            if not MODULE_NAME.fullmatch(word):
                require(bool(names) and word in {"@", "#"} and "\n" in code[last_end:current.start()],
                        f"{label}: unsupported import syntax near {word!r}")
                break
            names.append(word)
            last_end = current.end()
            current = next(tokens, None)
        require(bool(names), f"{label}: import has no recognized module names")
        imports.extend(names)
    unparsed = [match.start() for match in IMPORT_TOKEN.finditer(code) if match.start() not in positions]
    require(not unparsed, f"{label}: import outside the supported module header")
    require(len(imports) == len(set(imports)), f"{label}: duplicate imports")
    return imports


def closure(graph: dict[str, list[str]], entries: list[str]) -> set[str]:
    seen: set[str] = set()
    todo = list(entries)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo.extend(graph[module])
    return seen


def module_list(value: object, label: str) -> list[str]:
    require(isinstance(value, list) and all(isinstance(item, str) and MODULE_NAME.fullmatch(item)
                                         for item in value), f"{label}: expected a module-name list")
    require(len(value) == len(set(value)), f"{label}: duplicate module names")
    return value


def parse_lakefile(text: str) -> dict[str, object]:
    """Read this package's constrained TOML format using only Python 3.9 stdlib.

    Accepted values are JSON-style strings, booleans and single-line arrays.
    Unsupported TOML forms fail explicitly instead of being partly interpreted.
    """
    config: dict[str, object] = {}
    table = config
    for number, original in enumerate(text.splitlines(), 1):
        quoted = escaped = False
        line = original
        for offset, char in enumerate(original):
            if quoted:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
            elif char == "#":
                line = original[:offset]
                break
        line = line.strip()
        if not line:
            continue
        label = f"lakefile.toml:{number}"
        if line in {"[[require]]", "[[lean_lib]]"}:
            key = line[2:-2]
            require(isinstance(config.get(key, []), list), f"{label}: inconsistent table {key}")
            table = {}
            config.setdefault(key, []).append(table)
        elif line == "[leanOptions]":
            require("leanOptions" not in config, f"{label}: duplicate leanOptions table")
            table = {}
            config["leanOptions"] = table
        else:
            assignment = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)", line)
            require(assignment is not None, f"{label}: unsupported TOML syntax")
            key, encoded = assignment.groups()
            require(key not in table, f"{label}: duplicate key {key}")
            try:
                value = json.loads(encoded)
            except ValueError as error:
                raise StructureError(f"{label}: unsupported TOML value {encoded!r}") from error
            require(isinstance(value, (str, bool)) or
                    isinstance(value, list) and all(isinstance(item, str) for item in value),
                    f"{label}: only strings, booleans and string arrays are supported")
            table[key] = value
    return config


def check_package(package: Path) -> dict[str, object]:
    package = package.resolve()
    migration = json.loads((package / "migration.json").read_text())
    config = parse_lakefile((package / "lakefile.toml").read_text())
    manifest = json.loads((package / "lake-manifest.json").read_text())
    require(migration.get("version") == 2, "migration.json: unsupported inventory version")
    require(config.get("name") == manifest.get("name"), "Lake configuration and manifest package names differ")
    configured_libraries = [library.get("name") for library in config.get("lean_lib", [])]
    require(configured_libraries == [ROOT], "Lake must define exactly the PLAStochastic library")
    require(config.get("defaultTargets") == [ROOT], "Lake default target must be PLAStochastic")
    require(config.get("leanOptions", {}).get("warningAsError") is True, "Lean warnings must be treated as errors")
    for library in config.get("lean_lib", []):
        require(not {"srcDir", "roots", "globs"} & library.keys(),
                f"{library.get('name')}: external or custom source discovery is unsupported")
    dependencies = config.get("require", [])
    require(len(dependencies) == 1 and dependencies[0].get("name") == "mathlib"
            and dependencies[0].get("git") == "https://github.com/leanprover-community/mathlib4.git"
            and not {"path", "dir"} & dependencies[0].keys(),
            "Lake must depend directly only on the pinned upstream Mathlib Git package")
    locked: dict[str, dict[str, object]] = {}
    for dependency in manifest.get("packages", []):
        name = dependency.get("name")
        require(isinstance(name, str) and name not in locked, "Manifest has an invalid or duplicate dependency")
        require(dependency.get("type") == "git" and "dir" not in dependency
                and isinstance(dependency.get("rev"), str) and GIT_REVISION.fullmatch(dependency["rev"]),
                f"Manifest dependency {name}: require a commit-pinned Git dependency, not a source path")
        locked[name] = dependency
    require("mathlib" in locked, "Manifest is missing Mathlib")
    require(locked["mathlib"].get("url") == dependencies[0]["git"], "Mathlib repository differs from its lock")
    environment = migration.get("environment")
    require(isinstance(environment, dict) and isinstance(environment.get("mathlib"), dict),
            "migration.json: missing pinned environment provenance")
    require((package / "lean-toolchain").read_text().strip() == environment.get("lean_toolchain"),
            "Lean toolchain differs from the migration environment")
    require(dependencies[0].get("rev") == environment["mathlib"].get("input_rev")
            == locked["mathlib"].get("inputRev"), "Mathlib version differs from the migration environment")
    require(locked["mathlib"].get("rev") == environment["mathlib"].get("rev"),
            "Mathlib commit differs from the migration environment")

    sources: dict[str, Path] = {}
    all_imports: dict[str, list[str]] = {}
    for directory, subdirs, files in os.walk(package, followlinks=False):
        subdirs[:] = sorted(name for name in subdirs if name not in {".lake", ".git", "__pycache__"})
        for name in subdirs:
            child = Path(directory) / name
            require(not child.is_symlink(), f"Source discovery hides a symlink directory: {child.relative_to(package)}")
        for filename in sorted(files):
            if not filename.endswith(".lean"):
                continue
            path = Path(directory) / filename
            relative = path.relative_to(package)
            module = ".".join(relative.with_suffix("").parts)
            require(MODULE_NAME.fullmatch(module) is not None and module.split(".")[0] == ROOT,
                    f"Unexpected local Lean source: {relative}")
            require(module == ROOT or module.split(".")[1] in ALLOWED_IMPORTS,
                    f"Lean source outside the subject areas: {relative}")
            require(path.resolve().is_relative_to(package), f"Source escapes the unified package: {relative}")
            require(module not in sources, f"Duplicate module: {module}")
            sources[module] = path
            code = scrub_lean(path.read_text(), str(relative))
            forbidden = FORBIDDEN_TOKEN.search(code)
            if forbidden:
                line = code.count("\n", 0, forbidden.start()) + 1
                raise StructureError(f"{relative}:{line}: forbidden proof token {forbidden.group()!r}")
            all_imports[module] = parse_imports(code, str(relative))
    require(ROOT in sources, "Missing the PLAStochastic root module")
    for module in sources:
        parts = module.split(".")
        for k in range(2, len(parts)):
            require(".".join(parts[:k]) not in sources,
                    f"{module}: a module file may not also be a directory of modules ({'.'.join(parts[:k])})")
    graph: dict[str, list[str]] = {}
    for module, imports in all_imports.items():
        graph[module] = []
        for dependency in imports:
            library = dependency.split(".")[0]
            if library == ROOT:
                require(dependency in sources, f"{module}: missing local import {dependency}")
                graph[module].append(dependency)
                if module != ROOT:
                    area, target = module.split(".")[1], dependency.split(".")[1]
                    require(target in ALLOWED_IMPORTS[area],
                            f"{module}: area {area} may not import {dependency}")
            else:
                require(library in BUILTIN_LIBRARIES or UPSTREAM_LIBRARIES.get(library) in locked,
                        f"{module}: undeclared external source import {dependency}")
    try:
        tuple(TopologicalSorter(graph).static_order())
    except CycleError as error:
        raise StructureError(f"Local import cycle: {error.args[1]}") from error

    inventory = migration.get("modules")
    require(isinstance(inventory, dict), "migration.json: missing copied-module inventory")
    facades = {module for module in sources if module.startswith(f"{ROOT}.{RESULTS}.")}
    native = migration.get("native", {})
    require(isinstance(native, dict), "migration.json: native must map new modules to their records")
    for module, record in native.items():
        require(module in sources and module not in facades and module != ROOT,
                f"{module}: native module is missing or is a facade")
        require(isinstance(record, dict) and isinstance(record.get("record"), str)
                and isinstance(record.get("description"), str),
                f"{module}: native module needs a research record and description")
    copied = set(sources) - facades - {ROOT} - native.keys()
    require(copied == inventory.keys(),
            f"Copied module inventory differs: unrecorded={sorted(copied - inventory.keys())}, "
            f"missing={sorted(inventory.keys() - copied)}")
    origins: set[str] = set()
    for module, record in inventory.items():
        require(isinstance(record, dict), f"{module}: malformed provenance record")
        for key in ("source_sha256", "integration_sha256", "sha256"):
            require(isinstance(record.get(key), str) and SHA256.fullmatch(record[key]) is not None,
                    f"{module}: missing or invalid {key}")
        origin_module = record.get("origin_module")
        require(isinstance(origin_module, str) and MODULE_NAME.fullmatch(origin_module) is not None
                and origin_module.split(".")[0] in ORIGIN_PACKAGES,
                f"{module}: missing or unknown origin module")
        if "split_from" in record:
            parent = inventory.get(record["split_from"])
            require(isinstance(parent, dict) and "split_from" not in parent
                    and parent.get("origin_module") == origin_module and isinstance(record.get("changes"), str),
                    f"{module}: a split file must name its documented parent module with the same origin")
        else:
            require(origin_module not in origins, f"{module}: duplicate origin module")
            origins.add(origin_module)
        origin = ORIGIN_PACKAGES[origin_module.split(".")[0]] + "/" + origin_module.replace(".", "/") + ".lean"
        require(record.get("source") == origin, f"{module}: unexpected original source location")
        require(hashlib.sha256(sources[module].read_bytes()).hexdigest() == record["sha256"],
                f"{module}: source hash differs from its recorded version")
        require(module_list(record.get("imports"), f"{module} recorded imports") == graph[module],
                f"{module}: local imports differ from the migration inventory")
    developed = copied | native.keys()
    entries = module_list(migration.get("entry_modules"), "migration entry_modules")
    require(entries and set(entries) <= developed, "Migration entry modules must name retained modules")
    require(closure(graph, entries) == developed,
            f"Sources differ from the selected entry-module closure: "
            f"unreachable={sorted(developed - closure(graph, entries))}")
    public_entries = migration.get("public_entries")
    require(isinstance(public_entries, dict) and public_entries, "Migration public_entries must record the facades")
    require(facades == public_entries.keys(), "Public facade files differ from migration public_entries")
    mapped_entries: set[str] = set()
    for facade, value in public_entries.items():
        imports = module_list(value, f"{facade} recorded entries")
        require(imports and set(imports) <= developed, f"{facade}: entries must name retained modules")
        require(all_imports[facade] == imports, f"{facade}: imports differ from its documented entries")
        mapped_entries.update(imports)

    require(mapped_entries == set(entries), "Public facade entries differ from selected migration entries")
    require(set(all_imports[ROOT]) == facades, "PLAStochastic must import exactly the public result facades")
    public_closure = closure(graph, [ROOT])
    require(public_closure == sources.keys(), f"Unreachable local sources: {sorted(sources.keys() - public_closure)}")
    excluded = migration.get("excluded")
    require(isinstance(excluded, dict) and set(excluded) == set(ORIGIN_PACKAGES),
            "Migration excluded-module inventory must record the three source libraries")
    for library, value in excluded.items():
        names = module_list(value, f"{library} excluded modules")
        require(all(module.startswith(library + ".") for module in names) and not set(names) & origins,
                f"{library}: excluded modules overlap the retained sources or another library")
    areas = Counter(module.split(".")[1] for module in sources if module != ROOT)
    origin_counts = Counter(record["origin_module"].split(".")[0] for record in inventory.values())
    return {
        "status": "passed",
        "local_modules": len(sources),
        "copied_modules": len(copied),
        "native_modules": len(native),
        "public_facades": len(facades),
        "areas": dict(sorted(areas.items())),
        "origins": dict(sorted(origin_counts.items())),
        "excluded_modules": sum(len(value) for value in excluded.values()),
        "lean_toolchain": environment["lean_toolchain"],
        "mathlib_commit": locked["mathlib"]["rev"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print the check summary as JSON")
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    try:
        result = check_package(package)
    except (StructureError, OSError, ValueError, TypeError, KeyError) as error:
        print(f"Structure check failed: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Structure check passed: {result['local_modules']} local modules, "
              f"{result['copied_modules']} copied modules, {result['native_modules']} native modules, "
              f"{result['public_facades']} public facades.")
        print("Areas: " + ", ".join(f"{key}={value}" for key, value in result["areas"].items()))
        print("Origins: " + ", ".join(f"{key}={value}" for key, value in result["origins"].items()))
        print(f"Pinned environment: {result['lean_toolchain']}; Mathlib {result['mathlib_commit']}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
