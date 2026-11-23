#!/usr/bin/env python3
"""Validate Git commit messages against Conventional Commits standards."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Annotated

import typer
from logsetup import init as init_logging

app = typer.Typer(
    add_completion=False,
    help="Validate commit message subject line against Conventional Commits.",
)

ALLOWED_TYPES = "feat|fix|refactor|docs|test|chore|ci|perf|style|build"
_CONVENTIONAL_RE = re.compile(
    rf"^(?:{ALLOWED_TYPES})(?:\([a-z0-9][a-z0-9_-]*\))?!?: [^\s].{{0,71}}$"
)


def validate_commit_message(message: str) -> str | None:
    """Return an error string if invalid, or None if the commit message passes."""
    lines = [
        line.strip()
        for line in message.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if not lines:
        return "Commit message is empty."

    subject = lines[0]
    if subject.startswith(("Merge ", "Revert ")):
        return None
    if len(subject) > 72:
        return f"Commit subject exceeds 72 characters ({len(subject)}): {subject!r}"
    if not _CONVENTIONAL_RE.match(subject):
        return (
            f"Invalid Conventional Commit subject: {subject!r}\n"
            "Expected: <type>(<scope>): <imperative summary <= 72 chars>\n"
            f"Allowed types: {ALLOWED_TYPES}"
        )
    return None


@app.command()
def main(
    msg_file: Annotated[Path, typer.Argument(help="Path to commit message file")],
) -> None:
    """Validate commit message file for git commit-msg hook."""
    if not msg_file.is_file():
        typer.secho(f"Commit message file not found: {msg_file}", fg="red", err=True)
        raise typer.Exit(code=1)

    err = validate_commit_message(msg_file.read_text(encoding="utf-8", errors="replace"))
    if err is not None:
        typer.secho(f"ERROR: {err}", fg="red", err=True)
        raise typer.Exit(code=1)


if __name__ == "__main__":
    init_logging(__file__)
    app()
