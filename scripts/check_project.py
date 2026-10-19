#!/usr/bin/env python3
"""Check the project's source boundary, local links, and dependency lock.

Uses only the Python 3.9+ standard library. It does not invoke Git, access the
network, or read manuscript files outside this repository.
"""

import argparse
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent
TRUST_ESCAPE = re.compile(
    r"^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*"
    r"(?:axiom|unsafe|opaque)\b|"
    r"\b(?:sorry|admit|native_decide|TODO|FIXME|PLACEHOLDER)\b",
    re.MULTILINE,
)
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private)[ \t]+)?import[ \t]+([^\n]+)", re.MULTILINE)
INLINE_LINK = re.compile(r"!?\[[^\]\n]*\]\(\s*(<[^>\n]+>|[^\s)]+)")
REFERENCE_LINK = re.compile(r"^[ \t]{0,3}\[[^\]\n]+\]:[ \t]*(<[^>\n]+>|\S+)", re.MULTILINE)
PIN = re.compile(r"[0-9a-f]{40}")


def check_project(root, require_dependencies=False):
    errors = []

    def read(relative):
        path = root / relative
        if not path.is_file():
            errors.append("Missing required file: " + relative)
            return ""
        return path.read_text(encoding="utf-8")

    for relative in ("MomentAmbiguity.lean", "MomentAmbiguityChecks.lean"):
        if not (root / relative).is_file():
            errors.append("Missing Lean entry point: " + relative)

    sources = sorted(set(root.glob("*.lean")) | set((root / "MomentAmbiguity").rglob("*.lean")))
    if not sources:
        errors.append("No project Lean sources found.")
    for path in sources:
        source = path.read_text(encoding="utf-8")
        relative = path.relative_to(root).as_posix()
        # This is intentionally conservative: these tokens are forbidden even
        # in comments, so the check cannot hide a proof hole behind prose.
        for match in TRUST_ESCAPE.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append("{}:{}: forbidden source token {!r}".format(relative, line, match.group().strip()))
        for match in IMPORT.finditer(source):
            for module in match.group(1).split("--", 1)[0].split():
                if module.startswith("MomentAmbiguity"):
                    target = root / (module.replace(".", "/") + ".lean")
                    if not target.is_file():
                        line = source.count("\n", 0, match.start()) + 1
                        errors.append("{}:{}: missing local import {}".format(relative, line, module))

    docs = sorted(path.relative_to(root).as_posix() for path in (root / "docs").rglob("*") if path.is_file())
    if docs != ["docs/Formalization.md"]:
        errors.append("docs/ must contain only Formalization.md; found: " + ", ".join(docs))
    for relative in ("README.md", "docs/Formalization.md"):
        content = read(relative)
        # Code examples are not Markdown links.
        content = re.sub(r"(?ms)^[ \t]*(```|~~~).*?^\s*\1[^\n]*$", "", content)
        for pattern in (INLINE_LINK, REFERENCE_LINK):
            for match in pattern.finditer(content):
                target = match.group(1).strip("<>")
                parts = urlsplit(target)
                if parts.scheme or parts.netloc or not parts.path:
                    continue
                target_path = (root / relative).parent / unquote(parts.path)
                try:
                    target_path.resolve().relative_to(root.resolve())
                except ValueError:
                    errors.append("{}: file link leaves the repository: {}".format(relative, target))
                    continue
                if not target_path.exists():
                    errors.append("{}: missing file link target: {}".format(relative, target))

    config = read("lakefile.toml")
    requirements = re.findall(r"(?ms)^\[\[require\]\][ \t]*\n(.*?)(?=^\[|\Z)", config)
    mathlib_blocks = [block for block in requirements if re.search(r'^name\s*=\s*"mathlib"\s*$', block, re.MULTILINE)]
    configured_rev = None
    configured_url = None
    if len(mathlib_blocks) != 1:
        errors.append("lakefile.toml must have exactly one mathlib requirement.")
    else:
        for field in ("rev", "git"):
            match = re.search(r'^' + field + r'\s*=\s*"([^"\n]+)"\s*$', mathlib_blocks[0], re.MULTILINE)
            if match is None:
                errors.append("Missing mathlib {} in lakefile.toml.".format(field))
            elif field == "rev":
                configured_rev = match.group(1)
            else:
                configured_url = match.group(1)
        if configured_rev is not None and not PIN.fullmatch(configured_rev):
            errors.append("mathlib must be pinned to a full 40-character commit in lakefile.toml.")

    manifest_text = read("lake-manifest.json")
    try:
        manifest = json.loads(manifest_text)
    except json.JSONDecodeError as error:
        errors.append("Invalid lake-manifest.json: " + str(error))
        manifest = {}
    packages = manifest.get("packages", [])
    mathlib_packages = [package for package in packages if package.get("name") == "mathlib"]
    if len(mathlib_packages) != 1:
        errors.append("lake-manifest.json must lock exactly one mathlib package.")
    else:
        mathlib = mathlib_packages[0]
        if mathlib.get("rev") != configured_rev or mathlib.get("inputRev") != configured_rev:
            errors.append("The mathlib revisions in lakefile.toml and lake-manifest.json differ.")
        if mathlib.get("url") != configured_url:
            errors.append("The mathlib URLs in lakefile.toml and lake-manifest.json differ.")
    for package in packages:
        if package.get("type") != "git" or not PIN.fullmatch(package.get("rev", "")):
            errors.append("Dependency is not locked to a Git commit: " + str(package.get("name")))
        if require_dependencies:
            package_path = root / manifest.get("packagesDir", ".lake/packages") / package["name"]
            if not package_path.is_dir():
                errors.append("Missing dependency {}; run the README setup commands first.".format(package["name"]))

    toolchain = read("lean-toolchain").strip()
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+", toolchain):
        errors.append("lean-toolchain must pin a Lean release.")
    return errors, len(sources)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-dependencies", action="store_true", help="also require every locked dependency checkout to be present")
    args = parser.parse_args()
    errors, source_count = check_project(ROOT, args.require_dependencies)
    if errors:
        for error in errors:
            print("ERROR: " + error, file=sys.stderr)
        return 1
    print("Project checks passed: {} Lean sources, local imports and links, one formalization guide, and pinned dependencies.".format(source_count))
    return 0


if __name__ == "__main__":
    sys.exit(main())
