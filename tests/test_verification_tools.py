"""Tests for Lean import checking and formalization status utilities."""

from __future__ import annotations

from pathlib import Path

from check_commit_msg import validate_commit_message
from check_imports import find_blueprint_parity_errors, find_missing_imports
from formalization_status import collect_metrics, find_uncovered_nodes


def test_check_imports_detects_missing_and_passes_complete(tmp_path: Path) -> None:
    lib_dir = tmp_path / "FracLap"
    sub_dir = lib_dir / "Analysis"
    sub_dir.mkdir(parents=True)
    (lib_dir / "Basic.lean").write_text("-- basic\n", encoding="utf-8")
    (sub_dir / "Sobolev.lean").write_text("-- sobolev\n", encoding="utf-8")

    root = tmp_path / "FracLap.lean"
    root.write_text("public import FracLap.Basic\n", encoding="utf-8")
    assert find_missing_imports(lib_dir, root) == ["FracLap.Analysis.Sobolev"]

    root.write_text(
        "public import FracLap.Basic\npublic import FracLap.Analysis.Sobolev\n",
        encoding="utf-8",
    )
    assert find_missing_imports(lib_dir, root) == []

    test_lib = tmp_path / "FracLapTest"
    test_lib.mkdir()
    (test_lib / "BasicTest.lean").write_text("-- test\n", encoding="utf-8")
    test_root = tmp_path / "FracLapTest.lean"
    test_root.write_text("-- empty\n", encoding="utf-8")
    assert find_missing_imports(test_lib, test_root, prefix="FracLapTest") == [
        "FracLapTest.BasicTest"
    ]
    test_root.write_text("public import FracLapTest.BasicTest\n", encoding="utf-8")
    assert find_missing_imports(test_lib, test_root, prefix="FracLapTest") == []

    bp_src = tmp_path / "blueprint" / "src"
    (bp_src / "Analysis").mkdir(parents=True)
    (bp_src / "Basic.tex").write_text("% basic\n", encoding="utf-8")
    (bp_src / "content.tex").write_text("\\input{Basic}\n", encoding="utf-8")
    bp_errs = find_blueprint_parity_errors(lib_dir, bp_src)
    assert len(bp_errs) == 2

    (bp_src / "Analysis" / "Sobolev.tex").write_text("% sobolev\n", encoding="utf-8")
    (bp_src / "content.tex").write_text(
        "\\input{Basic}\n\\input{Analysis/Sobolev}\n", encoding="utf-8"
    )
    assert find_blueprint_parity_errors(lib_dir, bp_src) == []

    # The standard-results appendix has no Lean module and must not count as an orphan.
    (bp_src / "StandardResults.tex").write_text("% standard results\n", encoding="utf-8")
    assert find_blueprint_parity_errors(lib_dir, bp_src) == []

    # Inline theorem block in content.tex or orphan \input should fail parity check
    (bp_src / "content.tex").write_text(
        "\\input{Basic}\n\\input{Analysis/Sobolev}\n\\input{Orphan}\n"
        "\\begin{theorem}Inline\\end{theorem}\n",
        encoding="utf-8",
    )
    inline_errs = find_blueprint_parity_errors(lib_dir, bp_src)
    assert any("Orphan \\input{Orphan}" in e for e in inline_errs)
    assert any("Inline theorem/definition" in e for e in inline_errs)


def test_collect_metrics_counts_declarations_sorries_and_leanok(tmp_path: Path) -> None:
    lean_dir = tmp_path / "FracLap"
    lean_dir.mkdir()
    (lean_dir / "Basic.lean").write_text(
        "def Foo := 1\ntheorem bar : Foo = 1 := rfl\ntheorem wip : True := by sorry\n",
        encoding="utf-8",
    )

    bp_dir = tmp_path / "blueprint" / "src"
    bp_dir.mkdir(parents=True)
    (bp_dir / "content.tex").write_text(
        "\\begin{definition}\\lean{FracLap.Foo}\\leanok\nFoo.\n\\end{definition}\n"
        "\\begin{lemma}\\mathlibok\nStd.\n\\end{lemma}\n"
        "\\begin{theorem}\\lean{FracLap.wip}\nWIP.\n\\end{theorem}\n"
        "\\begin{proof}\n% \\leanok\nPending.\n\\end{proof}\n",
        encoding="utf-8",
    )

    metrics = collect_metrics(lean_dir, bp_dir)
    assert metrics.lean_files == 1
    assert metrics.declarations == 3
    assert metrics.sorries == 1
    assert metrics.blueprint_nodes == 3
    assert metrics.lean_tagged_nodes == 2
    assert metrics.leanok_statements == 1
    assert metrics.mathlibok_statements == 1
    assert metrics.covered_statements == 2
    assert metrics.proofs_total == 1
    assert metrics.leanok_proofs == 0
    uncovered = find_uncovered_nodes(bp_dir)
    assert uncovered == [(Path("content.tex"), 7, "theorem")]


def test_validate_commit_message_accepts_and_rejects() -> None:
    assert validate_commit_message("feat(lean): prove Sobolev embedding\n\n- details") is None
    assert validate_commit_message("fix(blueprint): sync label for energy lemma") is None
    assert validate_commit_message("Merge branch 'main' into feat/sobolev") is None
    assert validate_commit_message("wip stuff") is not None
    assert validate_commit_message("feat(lean): " + "x" * 70) is not None
    assert validate_commit_message("# comment only\n") is not None
