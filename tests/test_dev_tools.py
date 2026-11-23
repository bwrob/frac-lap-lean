"""Tests for the developer tooling: module scaffolder and fast Lean style checker."""

from __future__ import annotations

from pathlib import Path

import pytest
from check_imports import find_blueprint_parity_errors, find_missing_imports
from lean_style_check import check_file
from new_module import scaffold


def _mini_repo(root: Path) -> None:
    (root / "FracLap").mkdir()
    (root / "FracLapTest").mkdir()
    (root / "blueprint" / "src").mkdir(parents=True)
    (root / "FracLap" / "Basic.lean").write_text("-- basic\n", encoding="utf-8")
    (root / "blueprint" / "src" / "Basic.tex").write_text("% basic\n", encoding="utf-8")
    (root / "FracLap.lean").write_text("module\n\npublic import FracLap.Basic\n", encoding="utf-8")
    (root / "FracLapTest.lean").write_text(
        "module\n\npublic import FracLapTest.BasicTest\n", encoding="utf-8"
    )
    (root / "blueprint" / "src" / "content.tex").write_text("\\input{Basic}\n", encoding="utf-8")


def test_scaffold_keeps_one_to_one_parity(tmp_path: Path) -> None:
    _mini_repo(tmp_path)
    created = scaffold("WholeLine/Foo", tmp_path)
    assert [p.name for p in created] == ["Foo.lean", "Foo.tex", "FooTest.lean"]
    assert find_missing_imports(tmp_path / "FracLap", tmp_path / "FracLap.lean") == []
    assert find_blueprint_parity_errors(tmp_path / "FracLap", tmp_path / "blueprint" / "src") == []
    assert "FracLapTest.FooTest" in (tmp_path / "FracLapTest.lean").read_text(encoding="utf-8")


def test_scaffold_rejects_bad_paths_and_overwrites(tmp_path: Path) -> None:
    _mini_repo(tmp_path)
    with pytest.raises(ValueError):
        scaffold("whole_line/foo", tmp_path)
    scaffold("Core/Bar", tmp_path)
    with pytest.raises(FileExistsError):
        scaffold("Core/Bar", tmp_path)


def test_style_checker_flags_known_problems(tmp_path: Path) -> None:
    bad = tmp_path / "Bad.lean"
    bad.write_text(
        "public def foo := 1\n"
        + "-- "
        + "x" * 120
        + "\nexample : True := by\n  show True\n  push_neg\n  rw [if_true]\n",
        encoding="utf-8",
    )
    problems = "\n".join(check_file(bad))
    for needle in ("docstring", "characters", "`change`", "push_neg", "ite_true"):
        assert needle in problems


def test_style_checker_accepts_clean_file_and_ignores_comments(tmp_path: Path) -> None:
    good = tmp_path / "Good.lean"
    good.write_text(
        "/-- Documented. -/\n"
        "public noncomputable def foo := 1\n"
        "-- push_neg and if_true in comments are ignored\n"
        "/- block comment mentioning haveI and show Foo -/\n",
        encoding="utf-8",
    )
    assert check_file(good) == []
