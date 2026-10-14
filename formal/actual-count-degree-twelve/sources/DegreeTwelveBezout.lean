import DegreeTwelveData
namespace StackSorting.DegreeTwelve
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def bezoutLeft4 : (ZMod 17)[X] := 7 + 12 * X + 15 * X^2 + 2 * X^3 + 13 * X^4 + 6 * X^5 + 3 * X^6 + 6 * X^7 + 4 * X^8 + 10 * X^9 + 14 * X^10
def bezoutRight4 : (ZMod 17)[X] := 2 * X + 13 * X^2 + 4 * X^3 + 16 * X^4 + 2 * X^5 + 7 * X^6 + 16 * X^7 + 3 * X^8 + 8 * X^9 + 4 * X^10 + 5 * X^11
theorem bezout_4 : bezoutLeft4*specialized + bezoutRight4*(rem4-X) = 1 := by
  unfold bezoutLeft4 bezoutRight4 specialized rem4
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem coprime_remainder_4 : IsCoprime specialized (rem4-X) :=
  ⟨bezoutLeft4, bezoutRight4, bezout_4⟩
#print axioms bezout_4
#print axioms coprime_remainder_4

def bezoutLeft6 : (ZMod 17)[X] := 7 + 13 * X + 9 * X^2 + 9 * X^3 + 4 * X^4 + 6 * X^5 + 6 * X^6 + 9 * X^7 + 5 * X^8 + 6 * X^9 + 13 * X^10
def bezoutRight6 : (ZMod 17)[X] := 13 + 16 * X + 3 * X^2 + X^3 + 13 * X^4 + 13 * X^5 + 11 * X^6 + 11 * X^7 + 11 * X^8 + 8 * X^9 + 4 * X^10 + 5 * X^11
theorem bezout_6 : bezoutLeft6*specialized + bezoutRight6*(rem6-X) = 1 := by
  unfold bezoutLeft6 bezoutRight6 specialized rem6
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem coprime_remainder_6 : IsCoprime specialized (rem6-X) :=
  ⟨bezoutLeft6, bezoutRight6, bezout_6⟩
#print axioms bezout_6
#print axioms coprime_remainder_6
end
end StackSorting.DegreeTwelve
