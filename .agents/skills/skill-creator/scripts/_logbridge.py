"""Bridge to ``scripts/logsetup.py`` for scripts outside ``scripts/`` (identical copies)."""

import sys
from pathlib import Path

_HERE = Path(__file__).resolve()
_SCRIPTS = next(p / "scripts" for p in _HERE.parents if (p / "scripts" / "logsetup.py").is_file())
sys.path.insert(0, str(_SCRIPTS))

from logsetup import init as init_logging  # noqa: E402

__all__ = ["init_logging"]
