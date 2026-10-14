import ActualCountsDegreeTwelve
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
open Polynomial
example (q : (RatFunc ℚ)[X])
    (hq : Polynomial.aeval sortableCountsLaurent q = 0) : 12 ≤ q.natDegree :=
  sortableCounts_annihilator_degree q hq
