import ScalarBranchUnique

namespace StackSorting.ScalarJet
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics
open StackSorting.ConcreteScalar
set_option maxRecDepth 10000
set_option maxHeartbeats 30000000

/-- Degree-twelve center, certified below by the full scalar polynomial. -/
def center12 : QPoly.Poly := [1, 1, 2, 6, 24, 120, 720, 5004, 38844, 325692, 2874096, 26225388, 244673064]
def family12 : Fin 7 → QPoly.Poly := fun _ => center12
def A0 : Expr := (splitAt 24 family12 f0).high
def A1 : Expr := (splitAt 12 family12 f1).high
def A2 : Expr := (splitAt 2 family12 f2).high

theorem low0 : (splitAt 24 family12 f0).low = List.replicate 24 0 := by
  decide +kernel

theorem low1 : (splitAt 12 family12 f1).low = List.replicate 11 0 ++ [(-576 : Rat)] := by
  decide +kernel

theorem low2 : (splitAt 2 family12 f2).low = List.replicate 2 0 := by
  decide +kernel

#print axioms low0
#print axioms low1
#print axioms low2
end StackSorting.ScalarJet
