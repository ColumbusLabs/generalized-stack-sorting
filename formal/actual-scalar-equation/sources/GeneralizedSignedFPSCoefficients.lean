import SignedWordAlgebra
import FormalResolvent

/-! Coefficient extraction respects literal finite signed word sums. -/
namespace StackSorting.SignedWord
open StackSorting.CauchyRing StackSorting.ProperSeries
attribute [local instance] Lean.Grind.Ring.intCast

theorem eval_coefficient (phi : Word → FPS) (poly : Poly) (n : Nat) :
    (eval phi poly) n = eval (fun word => phi word n) poly := by
  induction poly with
  | nil =>
    change const 0 n = 0
    unfold const
    split <;> rfl
  | cons term poly ih =>
    rcases term with ⟨c,word⟩
    change (C (c : Rat)*phi word + eval phi poly) n =
      (c : Rat)*phi word n + eval (fun word => phi word n) poly
    rw [add_apply, mul_apply]
    change cauchy (const (c : Rat)) (phi word).coeff n + (eval phi poly) n = _
    rw [cauchy_const_left, ih]

theorem list_sum_coefficient (values : List FPS) (n : Nat) :
    values.sum n = (values.map (fun value => value n)).sum := by
  induction values with
  | nil =>
    change const 0 n = 0
    unfold const
    split <;> rfl
  | cons value values ih => simp only [List.sum_cons, List.map_cons, add_apply, ih]

#print axioms eval_coefficient
#print axioms list_sum_coefficient
end StackSorting.SignedWord
