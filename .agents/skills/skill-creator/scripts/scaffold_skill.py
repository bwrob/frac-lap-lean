#!/usr/bin/env python3
"""Skill Scaffolding Utility for .agents/skills/<name>/."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Annotated

import typer
from _logbridge import init_logging

app = typer.Typer(
    add_completion=False,
    help="Scaffold a new Antigravity skill with standardized directory layout.",
)


def validate_skill_name(name: str) -> str:
    """Validate and normalize a skill name to kebab-case."""
    clean = name.strip().lower()
    if not re.match(r"^[a-z0-9]+(-[a-z0-9]+)*$", clean):
        raise ValueError(
            f"Invalid skill name '{name}'. "
            "Must be lowercase kebab-case (e.g. 'lean-formalization')."
        )
    return clean


def to_title(name: str) -> str:
    """Convert kebab-case name into a human-readable title."""
    return " ".join(word.capitalize() for word in name.split("-"))


def scaffold_skill(
    skill_name: str,
    description: str | None = None,
    target_dir: Path | None = None,
) -> Path:
    """Scaffold a new skill directory with templates and subdirectories."""
    validated_name = validate_skill_name(skill_name)
    skill_title = to_title(validated_name)

    base_dir = Path(".agents/skills") if target_dir is None else target_dir
    out_dir = base_dir / validated_name

    if out_dir.exists():
        raise FileExistsError(f"Skill directory already exists: {out_dir}")

    (out_dir / "resources").mkdir(parents=True, exist_ok=True)
    (out_dir / "references").mkdir(parents=True, exist_ok=True)
    (out_dir / "scripts").mkdir(parents=True, exist_ok=True)

    desc = description or f"Provides workflows, patterns, and procedures for {skill_title.lower()}."
    summary = (
        "This skill defines the methodology, procedures, and quality standards for "
        f"{skill_title.lower()}."
    )

    template_path = Path(__file__).resolve().parent.parent / "resources" / "skill_template.md"
    if template_path.exists():
        content = template_path.read_text(encoding="utf-8")
    else:
        content = (
            "---\n"
            "name: ${SKILL_NAME}\n"
            "description: >-\n"
            "  ${SKILL_DESCRIPTION}\n"
            "---\n\n"
            "# ${SKILL_TITLE} Skill (`${SKILL_NAME}`)\n\n"
            "${SKILL_SUMMARY}\n"
        )

    content = (
        content.replace("${SKILL_NAME}", validated_name)
        .replace("${SKILL_TITLE}", skill_title)
        .replace("${SKILL_DESCRIPTION}", desc)
        .replace("${SKILL_SUMMARY}", summary)
    )

    (out_dir / "SKILL.md").write_text(content, encoding="utf-8")
    return out_dir


@app.command()
def main(
    name: Annotated[str, typer.Argument(help="Skill name in kebab-case")],
    description: Annotated[
        str | None,
        typer.Option("--description", "-d", help="Skill frontmatter description"),
    ] = None,
    path: Annotated[
        Path | None,
        typer.Option("--path", "-p", help="Base directory (default: .agents/skills/)"),
    ] = None,
) -> None:
    """Scaffold a new Antigravity skill with standardized directory layout."""
    try:
        created_path = scaffold_skill(name, description, path)
        typer.echo(f"Successfully scaffolded new skill at: {created_path}")
    except Exception as exc:
        typer.echo(f"Error: {exc}", err=True)
        raise typer.Exit(code=1) from exc


if __name__ == "__main__":
    init_logging(__file__)
    app()
