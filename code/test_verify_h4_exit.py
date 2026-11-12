"""Regression tests for verify_h4.py's process exit status and mode labels."""

import subprocess
import sys
import unittest
from pathlib import Path


CODE_DIR = Path(__file__).resolve().parent
SCRIPT = CODE_DIR / "verify_h4.py"


class VerifyH4ExitStatusTests(unittest.TestCase):
    def run_script(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            cwd=CODE_DIR,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_clean_exact_run_exits_zero(self):
        result = self.run_script("--nmax", "11")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("[result] PASS: exact integer verification checks are clean", result.stdout)

    def test_detected_window_failure_exits_nonzero(self):
        controlled_failure = r"""
import sys
import verify_h4
verify_h4.window_sweep = lambda *args, **kwargs: [(11, 3, 999, 1)]
verify_h4.tail_check = lambda *args, **kwargs: 0
verify_h4.enumerate_h4 = lambda n, callback: None
sys.argv = ["verify_h4.py", "--nmax", "11"]
sys.exit(verify_h4.main())
"""
        result = subprocess.run(
            [sys.executable, "-c", controlled_failure],
            cwd=CODE_DIR,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("[result] FAIL: 1 verification failures", result.stdout)

    def test_fast_run_is_not_labelled_exact(self):
        result = self.run_script("--nmax", "11", "--fast")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("fast float stress checks (not exact verification)", result.stdout)
        self.assertIn("not exact verification", result.stdout)


if __name__ == "__main__":
    unittest.main()
