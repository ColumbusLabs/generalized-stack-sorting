import ActualCountsDegreeTwelve
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
example (a : LaurentSeries ℚ) : (minpoly (RatFunc ℚ) a).natDegree = 12 :=
  sortableCounts_minpoly_degree
