"""Tests for the documentation generator (blueprint LaTeX to Markdown, Lean chunk lookup)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from gen_docs import (  # noqa: E402
    _extract_cmd,
    _split_list,
    classify,
    index_lean,
    load_provenance,
    tex_to_md,
)


def test_math_and_text_conversion() -> None:
    md = tex_to_md(r"Let $x \in \mathbb{R}$ and \emph{fix} \texttt{a\_b}.", lambda k: k)
    assert r"\(x \in \mathbb{R}\)" in md
    assert "*fix*" in md
    assert "`a_b`" in md


def test_display_math_is_its_own_block() -> None:
    md = tex_to_md(r"so \[ a = b \] holds", lambda k: k)
    assert "\n\n\\[a = b\\]\n\n" in md


def test_refs_are_resolved() -> None:
    assert tex_to_md(r"see \ref{thm:x}", lambda k: f"<{k}>") == "see <thm:x>"


def test_extract_cmd_and_list_split() -> None:
    rest, args = _extract_cmd(r"A \lean{FracLap.a, FracLap.b} B", "lean")
    assert args == ["FracLap.a, FracLap.b"]
    assert "lean" not in rest
    assert _split_list("FracLap.a,\n FracLap.b") == ["FracLap.a", "FracLap.b"]


def test_lean_index_finds_known_declaration() -> None:
    chunks = index_lean()["chain_rule_integral"]
    assert chunks
    assert "chain_rule_integral" in chunks[0].text


def test_provenance_classification() -> None:
    prov = load_provenance()
    assert classify("Tools/ChainRule", prov) == ("corpus", [])
    assert classify("Core/C0Semigroup", prov)[0] == "corpus"  # type: ignore[index]
    assert classify("WholeLine/StableKernel", prov)[0] == "thesis"  # type: ignore[index]
    assert classify("Nonexistent/Module", prov) is None
