"""Shared logging for every Python script of the repository (loguru).

``init(__file__)`` in a script's ``__main__`` block gives that run

* a rotating log file ``.logs/<script>.log`` (git-ignored) with timestamps, levels and the source
  of every direct ``logger`` call;
* a mirror of everything written to stdout and stderr (``print``, ``typer.echo``, rich, tracebacks
  printed by libraries), with ANSI colours and progress-bar redraws stripped;
* a record of uncaught exceptions with their traceback, and of standard-library ``logging``
  warnings (httpx, lancedb, ...), which are routed through loguru.

The console is left untouched: only warnings and errors logged *directly* through ``logger`` are
echoed to stderr. Set ``FRACLAP_NO_LOG=1`` to disable the file entirely and
``FRACLAP_LOG_LEVEL=DEBUG`` to change the file level. If loguru is not installed ``init`` does
nothing, so a script never fails because of logging.
"""

from __future__ import annotations

import atexit
import logging
import os
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from types import TracebackType
from typing import Any, TextIO, override

try:
    from loguru import logger
except ImportError:  # pragma: no cover - logging is optional
    logger = None  # type: ignore[assignment]

ROOT = Path(__file__).resolve().parent.parent
LOG_DIR = ROOT / ".logs"
ANSI = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]|\x1b\][^\x07]*\x07")
FILE_LINE = "{time:YYYY-MM-DD HH:mm:ss.SSS} | {level: <8} | "


def _format(record: Any) -> str:
    """Per-record format: mirrored stream lines are plain, direct calls show their source."""
    if record["extra"].get("stream") in ("stdout", "stderr"):
        return FILE_LINE + "{extra[stream]: <6} | {message}\n"
    return FILE_LINE + "log    | {name}:{function}:{line} - {message}\n{exception}"


def _is_direct(record: Any) -> bool:
    """True for records logged through ``logger`` directly (not mirrored stream lines)."""
    return bool(record["extra"].get("stream") == "log")


class Tee:
    """File-like wrapper that forwards writes unchanged and mirrors complete lines to loguru."""

    def __init__(self, stream: TextIO, name: str, level: str) -> None:
        self._stream = stream
        self._name = name
        self._level = level
        self._pending = ""

    def write(self, text: str) -> int:
        written = self._stream.write(text)
        self._pending += text
        while "\n" in self._pending:
            line, self._pending = self._pending.split("\n", 1)
            self._emit(line)
        return written

    def _emit(self, line: str) -> None:
        clean = ANSI.sub("", line.split("\r")[-1]).rstrip()
        if clean and logger is not None:
            logger.bind(stream=self._name).log(self._level, clean)

    def flush(self) -> None:
        self._stream.flush()

    def __getattr__(self, item: str) -> Any:
        return getattr(self._stream, item)


class _InterceptHandler(logging.Handler):
    """Route standard-library logging records into loguru."""

    @override
    def emit(self, record: logging.LogRecord) -> None:
        if logger is None:
            return
        try:
            level: str | int = logger.level(record.levelname).name
        except ValueError:
            level = record.levelno
        logger.bind(stream="lib").opt(exception=record.exc_info).log(
            level, f"{record.name}: {record.getMessage()}"
        )


@dataclass
class _State:
    """What ``init`` changed, so that ``reset`` can undo it."""

    installed: bool = False
    stdout: TextIO | None = None
    stderr: TextIO | None = None
    excepthook: Any = None
    path: Path | None = None
    started: float = field(default=0.0)


_STATE = _State()


def _excepthook(
    exc_type: type[BaseException], exc: BaseException, tb: TracebackType | None
) -> None:
    """Log an uncaught exception, then fall through to the default hook."""
    if logger is not None:
        if issubclass(exc_type, KeyboardInterrupt):
            logger.warning("interrupted (KeyboardInterrupt)")
        else:
            logger.opt(exception=(exc_type, exc, tb)).critical("uncaught exception")
    sys.__excepthook__(exc_type, exc, tb)


def _finish(script: str) -> None:
    """Log the end of a run (registered with ``atexit``)."""
    if logger is not None and _STATE.installed:
        logger.info("end {} after {:.1f}s", script, time.time() - _STATE.started)


def init(
    script: str | Path,
    *,
    log_dir: Path | None = None,
    level: str | None = None,
    tee: bool = True,
) -> Path | None:
    """Start logging for ``script``; return the log file path (``None`` if disabled).

    ``tee=False`` leaves stdout and stderr alone (needed by programs that use them as a protocol
    channel, such as the MCP server). Calling ``init`` twice is a no-op.
    """
    if logger is None or os.environ.get("FRACLAP_NO_LOG") or _STATE.installed:
        return _STATE.path
    name = Path(script).stem
    directory = log_dir or LOG_DIR
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.log"
    logger.remove()
    logger.configure(extra={"stream": "log"})
    logger.add(
        path,
        level=level or os.environ.get("FRACLAP_LOG_LEVEL", "DEBUG"),
        format=_format,
        rotation="5 MB",
        retention=10,
        encoding="utf-8",
        backtrace=True,
        diagnose=False,
    )
    logger.add(
        sys.__stderr__ or sys.stderr,
        level="WARNING",
        format="<level>{level}</level>: {message}",
        filter=_is_direct,
    )
    _STATE.installed = True
    _STATE.path = path
    _STATE.started = time.time()
    _STATE.excepthook = sys.excepthook
    sys.excepthook = _excepthook
    logging.basicConfig(handlers=[_InterceptHandler()], level=logging.WARNING, force=True)
    if tee:
        _STATE.stdout, _STATE.stderr = sys.stdout, sys.stderr
        sys.stdout = Tee(sys.stdout, "stdout", "INFO")  # type: ignore[assignment]
        sys.stderr = Tee(sys.stderr, "stderr", "WARNING")  # type: ignore[assignment]
    logger.info("start {} argv={} cwd={}", name, sys.argv[1:], Path.cwd())
    atexit.register(_finish, name)
    return path


def reset() -> None:
    """Undo ``init`` (used by the tests)."""
    if logger is None or not _STATE.installed:
        return
    if _STATE.stdout is not None:
        sys.stdout, sys.stderr = _STATE.stdout, _STATE.stderr  # type: ignore[assignment]
    sys.excepthook = _STATE.excepthook or sys.__excepthook__
    logger.remove()
    atexit.unregister(_finish)
    _STATE.installed = False
    _STATE.stdout = _STATE.stderr = None
    _STATE.path = None
