import ActualCountsDegreeTwelve
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
example (q : Polynomial (RatFunc ℚ)) : Polynomial.aeval generatedCountsLaurent q = 0 :=
  generatedCountsLaurent_root
