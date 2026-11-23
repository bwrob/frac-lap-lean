#!/usr/bin/env python3
"""Formalization & Blueprint Progress Dashboard."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Annotated

import typer
from logsetup import init as init_logging
from rich.console import Console
from rich.table import Table

app = typer.Typer(
    add_completion=False,
    help="Display Lean 4 formalization and leanblueprint progress statistics.",
)

_DECL_RE = re.compile(
    r"^\s*(?:(?:public|private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|structure|inductive|abbrev)\b",
    re.MULTILINE,
)
_SORRY_RE = re.compile(r"\bsorry\b")
_STMT_RE = re.compile(
    r"\\begin\{(?:definition|lemma|theorem|proposition|corollary)\}(.*?)\\end\{(?:definition|lemma|theorem|proposition|corollary)\}",
    re.DOTALL,
)
_STMT_ENV_RE = re.compile(
    r"\\begin\{(definition|lemma|theorem|proposition|corollary)\}(.*?)\\end\{\1\}",
    re.DOTALL,
)
_PROOF_RE = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.DOTALL)


@dataclass
class StatusMetrics:
    """Aggregated formalization and blueprint metrics."""

    lean_files: int
    declarations: int
    sorries: int
    blueprint_nodes: int
    lean_tagged_nodes: int
    leanok_statements: int
    proofs_total: int
    leanok_proofs: int
    mathlibok_statements: int = 0
    covered_statements: int = 0


def _strip_lean_comments(text: str) -> str:
    no_block = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return "\n".join(re.sub(r"--.*$", "", line) for line in no_block.splitlines())


def _strip_tex_comments(text: str) -> str:
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", line) for line in text.splitlines())


def _collect_lean_counts(lean_dir: Path) -> tuple[int, int, int]:
    lean_paths = sorted(lean_dir.rglob("*.lean")) if lean_dir.is_dir() else []
    declarations = 0
    sorries = 0
    for path in lean_paths:
        cleaned = _strip_lean_comments(path.read_text(encoding="utf-8", errors="replace"))
        declarations += len(_DECL_RE.findall(cleaned))
        sorries += len(_SORRY_RE.findall(cleaned))
    return len(lean_paths), declarations, sorries


def _collect_blueprint_counts(
    blueprint_dir: Path,
) -> tuple[int, int, int, int, int, int, int]:
    tex_paths = sorted(blueprint_dir.rglob("*.tex")) if blueprint_dir.is_dir() else []
    bp_nodes = tagged_nodes = ok_stmts = mathlib_stmts = covered_stmts = 0
    proofs_total = ok_proofs = 0
    for path in tex_paths:
        raw = _strip_tex_comments(path.read_text(encoding="utf-8", errors="replace"))
        for m in _STMT_RE.finditer(raw):
            body = m.group(1)
            bp_nodes += 1
            has_leanok = r"\leanok" in body
            has_mathlibok = r"\mathlibok" in body
            tagged_nodes += int(r"\lean{" in body)
            ok_stmts += int(has_leanok)
            mathlib_stmts += int(has_mathlibok)
            covered_stmts += int(has_leanok or has_mathlibok)
        for pm in _PROOF_RE.finditer(raw):
            proofs_total += 1
            ok_proofs += int(r"\leanok" in pm.group(1))
    return bp_nodes, tagged_nodes, ok_stmts, mathlib_stmts, covered_stmts, proofs_total, ok_proofs


def find_uncovered_nodes(blueprint_dir: Path) -> list[tuple[Path, int, str]]:
    """Return ``(rel_path, line_no, env_name)`` for statement blocks lacking both status tags."""
    if not blueprint_dir.is_dir():
        return []
    uncovered: list[tuple[Path, int, str]] = []
    for path in sorted(blueprint_dir.rglob("*.tex")):
        raw = _strip_tex_comments(path.read_text(encoding="utf-8", errors="replace"))
        rel = path.relative_to(blueprint_dir)
        for m in _STMT_ENV_RE.finditer(raw):
            env_name, body = m.group(1), m.group(2)
            if r"\leanok" not in body and r"\mathlibok" not in body:
                line_no = raw[: m.start()].count("\n") + 1
                uncovered.append((rel, line_no, env_name))
    return uncovered


def collect_metrics(lean_dir: Path, blueprint_dir: Path) -> StatusMetrics:
    """Scan Lean sources and LaTeX blueprint files to compute progress counts."""
    lean_files, declarations, sorries = _collect_lean_counts(lean_dir)
    bp_nodes, tagged_nodes, ok_stmts, mathlib_stmts, covered_stmts, proofs_total, ok_proofs = (
        _collect_blueprint_counts(blueprint_dir)
    )
    return StatusMetrics(
        lean_files=lean_files,
        declarations=declarations,
        sorries=sorries,
        blueprint_nodes=bp_nodes,
        lean_tagged_nodes=tagged_nodes,
        leanok_statements=ok_stmts,
        proofs_total=proofs_total,
        leanok_proofs=ok_proofs,
        mathlibok_statements=mathlib_stmts,
        covered_statements=covered_stmts,
    )


def render_status_table(metrics: StatusMetrics) -> Table:
    """Build a Rich summary table of formalization metrics."""
    table = Table(title="FracLap Formalization Status", show_header=True, header_style="bold cyan")
    table.add_column("Metric", style="white")
    table.add_column("Value", justify="right", style="bold green")
    table.add_row("Lean modules (FracLap/)", str(metrics.lean_files))
    table.add_row("Lean declarations", str(metrics.declarations))
    sorry_style = "bold green" if metrics.sorries == 0 else "bold yellow"
    table.add_row("Remaining sorrys", f"[{sorry_style}]{metrics.sorries}[/{sorry_style}]")
    table.add_row("Blueprint nodes", str(metrics.blueprint_nodes))
    table.add_row(
        "Blueprint \\lean{} tagged", f"{metrics.lean_tagged_nodes}/{metrics.blueprint_nodes}"
    )
    table.add_row(
        "Blueprint \\leanok statements", f"{metrics.leanok_statements}/{metrics.blueprint_nodes}"
    )
    table.add_row("Blueprint \\mathlibok statements", str(metrics.mathlibok_statements))
    table.add_row(
        "Blueprint covered (\\leanok + \\mathlibok)",
        f"{metrics.covered_statements}/{metrics.blueprint_nodes}",
    )
    table.add_row("Blueprint \\leanok proofs", f"{metrics.leanok_proofs}/{metrics.proofs_total}")
    return table


@app.command()
def main(
    lean_dir: Annotated[Path | None, typer.Option(help="Lean library directory")] = None,
    blueprint_dir: Annotated[Path | None, typer.Option(help="Blueprint src directory")] = None,
    untagged: Annotated[
        bool,
        typer.Option("--untagged", help="List uncovered blueprint statement nodes"),
    ] = False,
) -> None:
    """Print formalization & blueprint progress summary."""
    repo_root = Path(__file__).resolve().parent.parent
    bp_dir = blueprint_dir or (repo_root / "blueprint" / "src")
    metrics = collect_metrics(lean_dir or (repo_root / "FracLap"), bp_dir)
    console = Console()
    console.print(render_status_table(metrics))
    if untagged:
        nodes = find_uncovered_nodes(bp_dir)
        if not nodes:
            console.print("All blueprint statement nodes are covered (\\leanok or \\mathlibok).")
        else:
            console.print(f"\nUncovered blueprint nodes ({len(nodes)}):")
            for rel, line_no, env_name in nodes:
                console.print(f"  - blueprint/src/{rel}:{line_no} ({env_name})")


if __name__ == "__main__":
    init_logging(__file__)
    app()
