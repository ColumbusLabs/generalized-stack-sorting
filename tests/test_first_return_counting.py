"""Expose the bounded research-script tests to repository discovery."""
from pathlib import Path
import sys

_SCRIPT_DIR = Path(__file__).resolve().parents[1] / "scripts" / "two_push_counting"
sys.path.insert(0, str(_SCRIPT_DIR))
try:
    from test_counting_first_returns import FirstReturnTests
finally:
    sys.path.pop(0)
