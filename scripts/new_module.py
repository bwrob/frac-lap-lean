#!/usr/bin/env python3
"""Scaffold a new FracLap module together with all files that must stay in 1-to-1 parity.

``just new-module WholeLine/Foo`` creates ``FracLap/WholeLine/Foo.lean``, the blueprint chapter
``blueprint/src/WholeLine/Foo.tex`` and the test module ``FracLapTest/FooTest.lean``, and registers
them in ``FracLap.lean``, ``FracLapTest.lean`` and ``blueprint/src/content.tex``, so that
``just check-imports`` passes immediately.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Annotated

import typer
from logsetup import init as init_logging

app = typer.Typer(add_completion=False, help=__doc__)

PATH_RE = re.compile(r"^[A-Z][A-Za-z0-9]*(/[A-Z][A-Za-z0-9]*)*$")

LEAN_HEADER = """/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module
"""


def lean_module(dotted: str) -> str:
    """Return the skeleton of a new library module."""
    return f"""{LEAN_HEADER}
public import Mathlib.Data.Real.Basic

/-!
# {dotted}

TODO: describe the definitions and theorems of this module.
-/

namespace FracLap

@[expose] public section

end

end FracLap
"""


def test_module(dotted: str, name: str) -> str:
    """Return the skeleton of the matching test module."""
    return f"""{LEAN_HEADER}
public import {dotted}

/-!
# FracLapTest.{name}Test

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`{dotted}`.
-/

namespace FracLapTest

open FracLap

end FracLapTest
"""


def blueprint_chapter(path: str, title: str) -> str:
    """Return the skeleton of the blueprint chapter."""
    return f"""\\chapter{{{title}}}

This chapter mirrors \\texttt{{FracLap/{path}.lean}}.
"""


def _insert_after_last(file: Path, prefix: str, new_line: str) -> None:
    lines = file.read_text(encoding="utf-8").splitlines()
    idx = max(i for i, line in enumerate(lines) if line.startswith(prefix))
    lines.insert(idx + 1, new_line)
    file.write_text("\n".join(lines) + "\n", encoding="utf-8")


def scaffold(path: str, root: Path, title: str | None = None) -> list[Path]:
    """Create the module files and register them; return the created paths."""
    if not PATH_RE.match(path):
        raise ValueError(f"module path must look like 'Dir/Name' (CamelCase), got {path!r}")
    name = path.rsplit("/", 1)[-1]
    dotted = "FracLap." + path.replace("/", ".")
    lean = root / "FracLap" / f"{path}.lean"
    tex = root / "blueprint" / "src" / f"{path}.tex"
    test = root / "FracLapTest" / f"{name}Test.lean"
    existing = [p for p in (lean, tex, test) if p.exists()]
    if existing:
        raise FileExistsError(f"refusing to overwrite: {', '.join(map(str, existing))}")
    for p in (lean, tex, test):
        p.parent.mkdir(parents=True, exist_ok=True)
    lean.write_text(lean_module(dotted), encoding="utf-8")
    tex.write_text(blueprint_chapter(path, title or name), encoding="utf-8")
    test.write_text(test_module(dotted, name), encoding="utf-8")
    _insert_after_last(root / "FracLap.lean", "public import FracLap.", f"public import {dotted}")
    _insert_after_last(
        root / "FracLapTest.lean",
        "public import FracLapTest.",
        f"public import FracLapTest.{name}Test",
    )
    content = root / "blueprint" / "src" / "content.tex"
    content.write_text(
        content.read_text(encoding="utf-8").rstrip("\n") + f"\n\\input{{{path}}}\n",
        encoding="utf-8",
    )
    return [lean, tex, test]


@app.command()
def main(
    path: Annotated[str, typer.Argument(help="Module path such as WholeLine/Foo")],
    title: Annotated[str | None, typer.Option(help="Blueprint chapter title")] = None,
) -> None:
    """Scaffold ``FracLap/<path>.lean`` with its blueprint chapter and test module."""
    for created in scaffold(path, Path.cwd(), title):
        print(f"created {created}")


if __name__ == "__main__":
    init_logging(__file__)
    app()
