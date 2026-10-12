"""Regressions for the (3,3) decorated normal form."""
import itertools
import unittest
from stack_sorting import three_push as d

class ThreePushNormalFormTests(unittest.TestCase):
    def test_initial_records(self):
        self.assertEqual(d.record((),1),())
        self.assertEqual(d.record((),6),('Z','B','T','T','T'))

    def test_bounded_literal_deletions(self):
        def syntax(n):
            if not n:
                yield ();return
            for a in ('Z','O','B','T'):
                for tail in syntax(n-1):yield (a,)+tail
            for m in range(2,n+1):
                for tail in syntax(n-m):yield (m,)+tail
        for n in range(1,7):
            for tail in syntax(n-1):
                state=('Z',)+tail;codes=d.expand(state)
                if n>1 and any(c[1]>1 for c in codes):continue
                physical=[d.decode(c) for c in codes]
                for k in range(1,n+1):
                    expected=frozenset(tuple(v-(v>k) for v in st if v!=k)
                        for st in physical if st.index(k)<3)
                    actual=frozenset(map(d.decode,d.expand(d.pop(state,k))))
                    self.assertEqual(actual,expected,(state,k))

    def test_single_zero_obstruction_family(self):
        for m in range(1,9):
            state=()
            for tag,k in [('N',6),('H',1),('H',1),('H',2),('N',m+2),('H',m+2),('H',2)]:
                state=d.record(state,k) if tag=='N' else d.pop(state,k)
            self.assertEqual(state,('Z',)+d.clause(m))
            self.assertEqual(len(d.expand(state)),2**m-1)

    def test_reachable_long_suffix_regression(self):
        state=()
        for tag,k in [('N',6),('H',1),('H',1),('H',2),('N',1101),('H',1)]:
            state=d.record(state,k) if tag=='N' else d.pop(state,k)
        self.assertEqual(state,('Z',)+('O',)*1099+('B',))
        self.assertEqual(d.pop(state,1),('Z',)*1100)

    def test_distinct_permutation_counts(self):
        self.assertEqual(d.counts_through(10)[0],
            [1,1,2,6,24,120,720,5004,38844,325692,2874096])

    def test_short_membership(self):
        for n in range(7):
            self.assertTrue(all(d.generated_member(p) for p in itertools.permutations(range(1,n+1))))
        self.assertFalse(d.generated_member((7,1,2,3,4,5,6)))

if __name__=='__main__':unittest.main()
