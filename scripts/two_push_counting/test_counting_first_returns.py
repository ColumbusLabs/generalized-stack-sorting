"""Small exact regression checks for first-return counting implementations."""
import unittest
from counting_first_returns import counts
from general_first_return_probe import first_return_counts

class FirstReturnTests(unittest.TestCase):
    def test_empty(self):
        self.assertEqual(counts(0),([1],[]))
    def test_two_three(self):
        expected=[1,1,2,6,24,120,708,4680,33312,248664,1915080,15068088,120406152]
        actual,bad=counts(12)
        self.assertEqual(actual,expected)
        self.assertEqual(bad,[])
    def test_explicit_bound(self):
        for n in (-1,27,True,2.0):
            with self.assertRaises(ValueError): counts(n)
    def test_general_specializations(self):
        expected={
            2:[1,1,2,6,24,116,628,3636,21956],
            3:[1,1,2,6,24,120,708,4680,33312],
            4:[1,1,2,6,24,120,720,4992,38544],
        }
        for s,ref in expected.items():
            with self.subTest(s=s):
                actual,bad,d=first_return_counts(s,8)
                self.assertEqual(actual,ref)
                self.assertEqual(bad,[])
                self.assertEqual(d,2**(s-1))
    def test_general_empty(self):
        for s in (2,3,4):
            actual,bad,d=first_return_counts(s,0)
            self.assertEqual((actual,bad),([1],[]))
    def test_general_explicit_bound(self):
        for s,n in ((1,4),(5,4),(2,9),(2,-1),(2,True)):
            with self.assertRaises(ValueError): first_return_counts(s,n)

if __name__=='__main__': unittest.main()
