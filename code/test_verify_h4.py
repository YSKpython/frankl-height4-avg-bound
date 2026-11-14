"""Boundary checks for the exact corrected-envelope verifier (standard library)."""
import unittest
from math import isqrt
from verify_h4 import Qbound, candidate_test, fmax, joint_domain, weight_parameters


class CorrectedEnvelopeTests(unittest.TestCase):
    def test_strict_square_test_and_equality(self):
        self.assertTrue(candidate_test(10, 1, 0, 1, 0, 3))
        self.assertFalse(candidate_test(10, 1, 0, 1, 0, 2))

    def test_zero_lines_and_negative_discriminant(self):
        self.assertTrue(candidate_test(3, 1, 2, 0, 0, 4))
        self.assertFalse(candidate_test(3, 1, 2, 0, 0, 3))
        self.assertFalse(candidate_test(3, 1, 0, 1, -1, 100))

    def test_full_domain_and_empty_case(self):
        self.assertEqual(list(joint_domain(0, 5)), [])
        self.assertIn((0, 6), list(joint_domain(7, 3)))
        self.assertNotIn((3, 6), list(joint_domain(7, 3)))
        for q in range(10):
            for E in range(10):
                expected = {(e, r) for e in range(E+1) for r in range(q)
                            if r+e+1 <= q}
                self.assertEqual(set(joint_domain(q, E)), expected)

    def test_global_q_and_parameter_signs(self):
        # Independent completed-square formula vs the implemented scalar scan.
        for n in range(4, 201):
            for t in range(1, n+1):
                H = t*(t-1)+2*t*(n-t)
                q = ((1+isqrt(1+4*H))//2 if n % 2 == 0 else
                     1+isqrt(1+H+3*fmax(n,t)*((n-1)//2)))
                self.assertEqual(Qbound(n,t), q)
                for w in range(1,t+2):
                    if w % 2 == n % 2:
                        weight_parameters(n,t,w)
        self.assertEqual(fmax(11,3), 0)
        self.assertEqual(fmax(11,4), 5)

    def test_command_rejects_window_failure(self):
        from unittest.mock import patch
        import verify_h4
        with patch.object(verify_h4, 'window_sweep', return_value=[{'failed': True}]), \
             patch('sys.argv', ['verify_h4.py']), \
             patch('builtins.print'):
            with self.assertRaises(SystemExit) as result:
                verify_h4.main()
            self.assertEqual(result.exception.code, 1)

    def test_command_rejects_construction_failure(self):
        from unittest.mock import patch
        import verify_h4
        with patch.object(verify_h4, 'window_sweep', return_value=[]), \
             patch.object(verify_h4, 'tail_check', return_value=0), \
             patch.object(verify_h4, 'check_family', return_value=['failure']), \
             patch('sys.argv', ['verify_h4.py']), \
             patch('builtins.print'):
            with self.assertRaises(AssertionError):
                verify_h4.main()

    def test_scope_counterexample(self):
        from fractions import Fraction
        from verify_h4 import height, is_separating, is_union_closed, pc
        F = {0, 1, 2, 3, 7}
        self.assertTrue(is_union_closed(F))
        self.assertTrue(is_separating(F,3))
        self.assertEqual(height(F),4)
        self.assertEqual(Fraction(sum(map(pc,F)),len(F)), Fraction(7,5))
        self.assertLess(Fraction(7,5),Fraction(3,2))


if __name__ == '__main__':
    unittest.main()
