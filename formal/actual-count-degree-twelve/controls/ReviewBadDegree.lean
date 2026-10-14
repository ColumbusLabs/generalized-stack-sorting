import ActualCountsDegreeTwelve
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
example : (minpoly (RatFunc ℚ) sortableCountsLaurent).natDegree = 13 :=
  sortableCounts_minpoly_degree
