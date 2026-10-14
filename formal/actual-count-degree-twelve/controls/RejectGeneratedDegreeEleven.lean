import ActualCountsDegreeTwelve
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
example : (minpoly (RatFunc ℚ) generatedCountsLaurent).natDegree = 11 :=
  generatedCounts_minpoly_degree
