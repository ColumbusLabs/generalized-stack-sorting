"""Setup/contract checks only; these are not research experiments."""
import contextlib
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from stack_sorting import MODEL_DESCRIPTION, __version__, validate_permutation
from stack_sorting.__main__ import main


class ScaffoldTests(unittest.TestCase):
    def test_valid_inputs(self):
        self.assertEqual(validate_permutation(()), ())
        self.assertEqual(validate_permutation([3, 1, 2]), (3, 1, 2))

    def test_invalid_inputs(self):
        for values in ([1, 1], [0], [2], [True], [1.0], ["1"]):
            with self.subTest(values=values), self.assertRaises(ValueError):
                validate_permutation(values)

    def test_status_command(self):
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            self.assertEqual(main([]), 0)
        result = json.loads(stream.getvalue())
        self.assertEqual(result["version"], __version__)
        self.assertIn("reproducible checks", result["status"])
        self.assertEqual(result["model"], MODEL_DESCRIPTION)

    def test_no_hosted_ci(self):
        workflows = Path(__file__).resolve().parents[1] / ".github" / "workflows"
        self.assertEqual(list(workflows.glob("*.yml")) + list(workflows.glob("*.yaml")), [])

    def test_experiment_bounds(self):
        from stack_sorting.experiments import run
        for maximum, generation in ((9, 0), (-1, 0), (6, 7), (1, 2), (True, 0)):
            with self.subTest(maximum=maximum, generation=generation), self.assertRaises(ValueError):
                run(maximum, generation)
        self.assertEqual(run(0, 0)["status"], "passed")

    def test_version_command(self):
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream), self.assertRaises(SystemExit) as exit:
            main(["--version"])
        self.assertEqual(exit.exception.code, 0)
        self.assertEqual(stream.getvalue().strip(), __version__)


if __name__ == "__main__":
    unittest.main()
