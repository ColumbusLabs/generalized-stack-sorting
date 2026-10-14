import ActualCountsDegreeTwelve
open StackSorting.MathlibSeriesBridge
example : generatedCountsLaurent.coeff (-1 : ℤ) = 1 :=
  generatedCountsLaurent_coeff_neg (-1) (by decide)
