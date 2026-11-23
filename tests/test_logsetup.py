"""Tests for the shared loguru setup (scripts/logsetup.py)."""

from __future__ import annotations

import io
import sys
from collections.abc import Iterator
from pathlib import Path

import logsetup
import pytest
from loguru import logger


@pytest.fixture(autouse=True)
def _restore_logging() -> Iterator[None]:
    yield
    logsetup.reset()
    logger.remove()


def test_init_writes_start_line_and_mirrors_stdout_and_stderr(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    path = logsetup.init("scripts/example.py", log_dir=tmp_path)
    assert path == tmp_path / "example.log"
    print("hello \x1b[31mred\x1b[0m world")
    print("progress 10%\rprogress 100%")
    print("to stderr", file=sys.stderr)
    logger.info("direct {}", "call")
    text = path.read_text(encoding="utf-8")
    assert "start example" in text
    assert "stdout | hello red world" in text  # ANSI stripped
    assert "progress 100%" in text
    assert "progress 10%" not in text  # redraw of a progress line is dropped
    assert "stderr | to stderr" in text
    assert "test_logsetup" in text and "direct call" in text
    out = capsys.readouterr()
    assert "hello" in out.out and "to stderr" in out.err  # the console still sees everything


def test_tee_forwards_unknown_attributes_and_returns_length() -> None:
    sink = io.StringIO()
    tee = logsetup.Tee(sink, "stdout", "INFO")
    assert tee.write("abc") == 3
    tee.flush()
    assert tee.getvalue() == "abc"  # delegated to the wrapped stream


def test_second_init_is_a_no_op(tmp_path: Path) -> None:
    first = logsetup.init("a.py", log_dir=tmp_path)
    second = logsetup.init("b.py", log_dir=tmp_path)
    assert first == second
    assert not (tmp_path / "b.log").exists()


def test_uncaught_exception_is_logged_with_traceback(tmp_path: Path) -> None:
    path = logsetup.init("boom.py", log_dir=tmp_path)
    assert path is not None
    try:
        raise ValueError("kaboom")
    except ValueError:
        logsetup._excepthook(*sys.exc_info())  # type: ignore[arg-type]  # noqa: SLF001
    text = path.read_text(encoding="utf-8")
    assert "CRITICAL" in text and "ValueError: kaboom" in text


def test_disabled_by_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("FRACLAP_NO_LOG", "1")
    assert logsetup.init("quiet.py", log_dir=tmp_path) is None
    assert not list(tmp_path.iterdir())


def test_tee_false_leaves_streams_alone(tmp_path: Path) -> None:
    before = sys.stdout
    logsetup.init("proto.py", log_dir=tmp_path, tee=False)
    assert sys.stdout is before
