#!/usr/bin/env python3
"""Verify every Lean module under FracLap/ is imported by FracLap.lean."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Annotated

import typer
from logsetup import init as init_logging

app = typer.Typer(
    add_completion=False,
    help="Verify all FracLap/**/*.lean modules are imported in FracLap.lean.",
)

_IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
_TEX_INPUT_RE = re.compile(r"^\s*\\input\{([A-Za-z0-9_./-]+)\}", re.MULTILINE)
_STMT_BLOCK_RE = re.compile(
    r"\\begin\{(?:definition|lemma|theorem|proposition|corollary)\}"
    r".*?\\end\{(?:definition|lemma|theorem|proposition|corollary)\}",
    re.DOTALL,
)
_BLUEPRINT_META_TEX = {
    Path("content.tex"),
    Path("web.tex"),
    Path("print.tex"),
    Path("macros/common.tex"),
    Path("macros/web.tex"),
    Path("macros/print.tex"),
    # Appendix of standard analysis facts stated in words; has no Lean module counterpart.
    Path("StandardResults.tex"),
}


def discover_lean_modules(lib_dir: Path, prefix: str = "FracLap") -> set[str]:
    """Return dotted module names for all .lean files inside lib_dir."""
    if not lib_dir.is_dir():
        return set()
    modules: set[str] = set()
    for path in sorted(lib_dir.rglob("*.lean")):
        rel_parts = path.relative_to(lib_dir).with_suffix("").parts
        modules.add(".".join((prefix, *rel_parts)))
    return modules


def parse_root_imports(root_file: Path) -> set[str]:
    """Extract imported module names from the root Lean entry file."""
    if not root_file.is_file():
        return set()
    content = root_file.read_text(encoding="utf-8")
    return {m.group(1) for m in _IMPORT_RE.finditer(content)}


def find_missing_imports(lib_dir: Path, root_file: Path, prefix: str = "FracLap") -> list[str]:
    """Return sorted list of modules present under lib_dir but missing from root_file."""
    expected = discover_lean_modules(lib_dir, prefix=prefix)
    imported = parse_root_imports(root_file)
    return sorted(expected - imported)


def _strip_tex_comments(text: str) -> str:
    """Remove LaTeX line comments while preserving escaped percent signs."""
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", line) for line in text.splitlines())


def _collect_blueprint_input_errors(
    content_file: Path,
    lean_rels: set[str],
) -> list[str]:
    """Validate that content.tex is a pure \\input{...} aggregator matching lean_rels."""
    if not content_file.is_file():
        return ["Missing blueprint/src/content.tex aggregator file"]
    cleaned = _strip_tex_comments(content_file.read_text(encoding="utf-8"))
    content_inputs = {m.group(1).removesuffix(".tex") for m in _TEX_INPUT_RE.finditer(cleaned)}
    errors = [
        f"Missing \\input{{{rel}}} in blueprint/src/content.tex"
        for rel in sorted(lean_rels - content_inputs)
    ]
    errors.extend(
        f"Orphan \\input{{{rel}}} in blueprint/src/content.tex without FracLap/{rel}.lean"
        for rel in sorted(content_inputs - lean_rels)
    )
    if _STMT_BLOCK_RE.search(cleaned):
        errors.append(
            "Inline theorem/definition found in blueprint/src/content.tex; "
            "move to 1-to-1 module file blueprint/src/<Module>.tex"
        )
    return errors


def find_blueprint_parity_errors(lean_dir: Path, blueprint_src_dir: Path) -> list[str]:
    """Verify 1-to-1 file parity between FracLap/**/*.lean and blueprint/src/**/*.tex."""
    if not lean_dir.is_dir() or not blueprint_src_dir.is_dir():
        return []
    lean_rels = {
        path.relative_to(lean_dir).with_suffix("").as_posix()
        for path in sorted(lean_dir.rglob("*.lean"))
    }
    tex_rels = {
        path.relative_to(blueprint_src_dir).with_suffix("").as_posix()
        for path in sorted(blueprint_src_dir.rglob("*.tex"))
        if path.relative_to(blueprint_src_dir) not in _BLUEPRINT_META_TEX
    }
    errors = [
        f"Missing blueprint file blueprint/src/{rel}.tex for FracLap/{rel}.lean"
        for rel in sorted(lean_rels - tex_rels)
    ]
    errors.extend(
        f"Orphan blueprint file blueprint/src/{rel}.tex without FracLap/{rel}.lean"
        for rel in sorted(tex_rels - lean_rels)
    )
    errors.extend(_collect_blueprint_input_errors(blueprint_src_dir / "content.tex", lean_rels))
    return errors


def _resolve_targets(
    repo_root: Path,
    lib_dir: Path | None,
    root_file: Path | None,
) -> list[tuple[Path, Path, str]]:
    """Determine `(lib_dir, root_file, prefix)` pairs to inspect."""
    if lib_dir is not None or root_file is not None:
        target_lib = lib_dir or (repo_root / "FracLap")
        target_root = root_file or (repo_root / "FracLap.lean")
        return [(target_lib, target_root, target_lib.name)]

    targets = [(repo_root / "FracLap", repo_root / "FracLap.lean", "FracLap")]
    test_lib = repo_root / "FracLapTest"
    if test_lib.is_dir():
        targets.append((test_lib, repo_root / "FracLapTest.lean", "FracLapTest"))
    return targets


def _verify_library(lib_dir: Path, root_file: Path, prefix: str) -> tuple[int, list[str]]:
    """Return total discovered modules and any missing imports for one Lean library."""
    expected = discover_lean_modules(lib_dir, prefix=prefix)
    missing = find_missing_imports(lib_dir, root_file, prefix=prefix)
    return len(expected), missing


def _report_failures(failures: list[tuple[str, list[str]]]) -> None:
    """Print missing module errors and exit with non-zero status."""
    for root_name, missing in failures:
        typer.secho(
            f"ERROR: Unimported Lean module(s) missing from {root_name}:",
            fg="red",
            err=True,
        )
        for mod in missing:
            typer.secho(f"  - {mod}", fg="red", err=True)
    raise typer.Exit(code=1)


@app.command()
def main(
    lib_dir: Annotated[
        Path | None,
        typer.Option(help="Library directory (default: FracLap/ and FracLapTest/)"),
    ] = None,
    root_file: Annotated[
        Path | None,
        typer.Option(help="Root entry file (default: FracLap.lean and FracLapTest.lean)"),
    ] = None,
) -> None:
    """Exit 1 if any Lean module is not imported by its root entry file."""
    repo_root = Path(__file__).resolve().parent.parent
    targets = _resolve_targets(repo_root, lib_dir, root_file)

    results = [
        (t_root.name, *_verify_library(t_lib, t_root, prefix)) for t_lib, t_root, prefix in targets
    ]
    failures = [(root_name, missing) for root_name, _, missing in results if missing]
    if lib_dir is None and root_file is None:
        bp_errors = find_blueprint_parity_errors(
            repo_root / "FracLap", repo_root / "blueprint" / "src"
        )
        if bp_errors:
            failures.append(("blueprint/src/content.tex (1-to-1 parity)", bp_errors))
    if failures:
        _report_failures(failures)

    total_modules = sum(count for _, count, _ in results)
    checked_roots = ", ".join(root_name for root_name, _, _ in results)
    typer.secho(
        f"Root import check clean: all {total_modules} module(s) imported in {checked_roots}.",
        fg="green",
        bold=True,
    )


if __name__ == "__main__":
    init_logging(__file__)
    app()
