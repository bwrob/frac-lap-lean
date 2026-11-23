#!/usr/bin/env python3
"""Fast pre-build style checker for the Lean sources.

Catches, in milliseconds, the issues that otherwise surface one build at a time because
`warningAsError = true`: over-long lines, `show` used to change goals, deprecated Mathlib names,
`haveI` for propositions, trailing whitespace, and public declarations without a docstring.

Usage: ``just lint-quick [files...]`` (default: every file under ``FracLap/`` and ``FracLapTest/``).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Annotated

import typer
from logsetup import init as init_logging

app = typer.Typer(add_completion=False, help=__doc__)

MAX_LINE = 100

# Old name -> replacement, for names deprecated in the pinned Mathlib.
DEPRECATED: dict[str, str] = {
    "Measurable.enorm": "Measurable.eNorm",
    "Continuous.enorm": "Continuous.eNorm",
    "enorm_ne_top": "eNorm_ne_top",
    "enorm_mul": "eNorm_mul",
    "ofReal_norm_eq_enorm": "ofReal_norm",
    "Lp.enorm_def": "Lp.eNorm_def",
    "Real.enorm_eq_ofReal": "Real.eNorm_eq_ofReal",
    "lintegral_rpow_enorm_eq_rpow_eLpNorm": "lintegral_rpow_eNorm_eq_rpow_eLpNorm",
    "push_neg": "push Not",
    "coe_nnnorm": "coe_nnNorm",
    "lipschitzWith_of_nnnorm_fderiv_le": "lipschitzWith_of_nnNorm_fderiv_le",
    "Isometry.antilipschitz": "Isometry.antilipschitzWith",
    "if_true": "ite_true",
}

# The `missingDocs` linter requires docstrings on definitions and structures, not on theorems.
DECL_RE = re.compile(r"^(?:(?:public|noncomputable|protected)\s+)*(def|abbrev|structure|class)\s")
SHOW_RE = re.compile(r"^\s*show\s")


def _format_problems(line: str) -> list[str]:
    """Length and whitespace problems of a single line."""
    out = []
    if len(line) > MAX_LINE:
        out.append(f"line has {len(line)} > {MAX_LINE} characters")
    if line != line.rstrip():
        out.append("trailing whitespace")
    return out


def _tactic_problems(line: str, prev_code: str) -> list[str]:
    """`show`/`haveI` misuse on a single line."""
    out = []
    continuation = prev_code.endswith((",", "["))
    term_show = " from " in line or " by " in line
    if SHOW_RE.match(line) and not continuation and not term_show:
        out.append("tactic `show` that changes the goal must be `change`")
    if re.search(r"\bhaveI\b", line):
        out.append("use `have` instead of `haveI` for propositions")
    return out


def _deprecated_problems(line: str) -> list[str]:
    """Uses of names deprecated in the pinned Mathlib."""
    return [
        f"deprecated name `{old}`; use `{new}`"
        for old, new in DEPRECATED.items()
        if old not in new and re.search(rf"(?<![\w.]){re.escape(old)}(?![\w'])", line)
    ]


def _doc_problems(line: str, prev_code: str, is_test: bool) -> list[str]:
    """Missing docstring on a public definition."""
    if is_test or not DECL_RE.match(line):
        return []
    if prev_code.endswith("-/") or prev_code.startswith("@["):
        return []
    return ["public declaration without a docstring"]


def _strip_comments_line(line: str, depth: int) -> tuple[str, int]:
    """Strip Lean line comments and nested block comments while updating depth."""
    out: list[str] = []
    i = 0
    n = len(line)
    while i < n:
        two = line[i : i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0 and two == "--":
            break
        else:
            if depth == 0:
                out.append(line[i])
            i += 1
    return "".join(out), depth


def check_file(path: Path) -> list[str]:
    """Return human-readable style problems found in ``path``."""
    problems: list[str] = []
    is_test = "FracLapTest" in str(path)
    prev_code = ""
    depth = 0
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        code, depth = _strip_comments_line(line, depth)
        found = [
            *_format_problems(line),
            *_tactic_problems(code, prev_code),
            *_deprecated_problems(code),
            *_doc_problems(code, prev_code, is_test),
        ]
        problems.extend(f"{path}:{i}: {msg}" for msg in found)
        if line.strip():
            prev_code = line.strip()
    return problems


@app.command()
def main(
    files: Annotated[list[Path] | None, typer.Argument(help="Lean files to check")] = None,
) -> None:
    """Check ``files`` (default: all project Lean sources)."""
    targets = files or sorted(
        [*Path("FracLap").rglob("*.lean"), *Path("FracLapTest").rglob("*.lean")]
    )
    all_problems = [p for f in targets for p in check_file(f)]
    for problem in all_problems:
        print(problem)
    if all_problems:
        print(f"{len(all_problems)} style problem(s) found.", file=sys.stderr)
        raise typer.Exit(1)
    print(f"Lean style check clean ({len(targets)} file(s)).")


if __name__ == "__main__":
    init_logging(__file__)
    app()
