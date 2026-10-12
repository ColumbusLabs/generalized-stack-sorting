"""Bounded status command; never starts a research run implicitly."""
import argparse
import json
from . import MODEL_DESCRIPTION, __version__


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version=__version__)
    parser.parse_args(argv)
    print(json.dumps({
        "project": "stack-sorting",
        "version": __version__,
        "status": "mechanism derivation and reproducible checks",
        "model": MODEL_DESCRIPTION,
        "goal": "A direct structural derivation of the known generating function",
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
