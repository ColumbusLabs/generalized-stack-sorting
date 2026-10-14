import DegreeTwelveRabinCriterion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.ReduceModChar

namespace StackSorting.DegreeTwelve
open Polynomial
noncomputable section
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Exact degree-twelve specialization of the stack certificate at x=3 mod 17. -/
def specialized : (ZMod 17)[X] := 5 + 14 * X + 9 * X^2 + 10 * X^3 + 4 * X^4 + 3 * X^5 + 14 * X^6 + 7 * X^7 + 14 * X^8 + 3 * X^9 + 14 * X^10 + 7 * X^11 + 5 * X^12

def rem0 : (ZMod 17)[X] := X
def rem1 : (ZMod 17)[X] := 10 + 11 * X + 15 * X^2 + 7 * X^3 + 2 * X^4 + 13 * X^5 + 10 * X^6 + X^8 + 8 * X^9 + 9 * X^10 + 8 * X^11
def rem2 : (ZMod 17)[X] := 5 + 12 * X + 9 * X^2 + 5 * X^3 + 8 * X^4 + 8 * X^5 + 10 * X^6 + 13 * X^7 + 14 * X^8 + 8 * X^9 + 11 * X^10 + 15 * X^11
def rem3 : (ZMod 17)[X] := 9 + 9 * X + 6 * X^2 + 2 * X^3 + 5 * X^4 + 10 * X^5 + X^6 + 14 * X^7 + 4 * X^8 + 3 * X^9 + 9 * X^10 + 7 * X^11
def rem4 : (ZMod 17)[X] := 6 + 13 * X + 12 * X^3 + 12 * X^4 + 7 * X^5 + 5 * X^7 + 4 * X^8 + X^9 + 2 * X^10 + 3 * X^11
def rem5 : (ZMod 17)[X] := 13 + 12 * X + 3 * X^2 + 12 * X^3 + 15 * X^4 + 3 * X^5 + 11 * X^6 + 3 * X^7 + 15 * X^8 + 15 * X^9 + 2 * X^10 + 2 * X^11
def rem6 : (ZMod 17)[X] := 12 * X + 6 * X^2 + 7 * X^3 + 4 * X^4 + 5 * X^5 + 9 * X^6 + 13 * X^7 + 5 * X^8 + 14 * X^9 + 10 * X^10 + 4 * X^11
def rem7 : (ZMod 17)[X] := 9 + 11 * X + 11 * X^2 + X^3 + 7 * X^4 + 14 * X^5 + 9 * X^6 + 2 * X^7 + 16 * X^8 + 10 * X^9 + 6 * X^10 + 15 * X^11
def rem8 : (ZMod 17)[X] := 15 + 11 * X + 11 * X^2 + 5 * X^3 + 3 * X^4 + 3 * X^5 + 2 * X^6 + X^7 + 3 * X^9 + 7 * X^10 + 4 * X^11
def rem9 : (ZMod 17)[X] := 9 + X + 5 * X^2 + 11 * X^3 + 8 * X^4 + 14 * X^5 + 12 * X^6 + 7 * X^7 + 4 * X^8 + 16 * X^9 + 8 * X^10 + 16 * X^11
def rem10 : (ZMod 17)[X] := 5 + 14 * X + 5 * X^2 + 15 * X^4 + 15 * X^5 + 13 * X^6 + 4 * X^8 + 9 * X^9 + 4 * X^10 + 12 * X^11
def rem11 : (ZMod 17)[X] := 6 + 12 * X + 14 * X^2 + 6 * X^3 + 6 * X^4 + 10 * X^5 + 8 * X^6 + 10 * X^7 + X^8 + 15 * X^9 + 16 * X^11
def rem12 : (ZMod 17)[X] := X

theorem specialized_degree : specialized.natDegree = 12 := by
  unfold specialized
  compute_degree!

#print axioms specialized_degree
end
end StackSorting.DegreeTwelve
