import SignedWordAlgebra

namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false

/-- Selected held rank. B and T use U; Z uses F. -/
def selected : Letter → Word → Poly
  | .z, w => F w
  | .b, w => U w
  | .t, w => U w

/-- The list has one summand per selected coordinate, before algebraic
cancellations; equal successor words are never deduplicated. -/
def heldDelete : Word → Poly
  | [] => []
  | a::w => selected a w ++ prefixLetter a (heldDelete w)

variable {R : Type} [Lean.Grind.CommRing R]

theorem heldDelete_cons_eval (phi : Word → R) (a : Letter) (w : Word) :
    eval phi (heldDelete (a::w)) = eval phi (selected a w) +
      eval (fun v => phi (a::v)) (heldDelete w) := by
  simp only [heldDelete, eval_append, eval_prefix]

theorem selected_z_eval (phi : Word → R) (w : Word) :
    eval phi (selected .z w) = eval phi (F w) := rfl

theorem selected_b_eval (phi : Word → R) (w : Word) :
    eval phi (selected .b w) = eval phi (F w) + eval phi (K w) := eval_U phi w

theorem selected_t_eval (phi : Word → R) (w : Word) :
    eval phi (selected .t w) = eval phi (F w) + eval phi (K w) := eval_U phi w

/-- Exact boundary-plus-internal decomposition, with multiplicity two. -/
theorem heldDelete_zb (phi : Word → R) (w : Word) :
    eval phi (heldDelete (.z::.b::w)) =
      2 * eval (fun v => phi (.z::v)) (U w) +
      eval (fun v => phi (.z::.b::v)) (heldDelete w) := by
  simp only [heldDelete_cons_eval, selected, F, eval_append, eval_prefix, eval_U]
  grind

/-- The ZZ boundary retains distinct F and J terms. -/
theorem heldDelete_zz (phi : Word → R) (w : Word) :
    eval phi (heldDelete (.z::.z::w)) =
      eval (fun v => phi (.z::v)) (J w) + eval (fun v => phi (.z::v)) (F w) +
      eval (fun v => phi (.z::.z::v)) (heldDelete w) := by
  simp only [heldDelete_cons_eval, selected, F, eval_append, eval_prefix]
  grind

theorem heldDelete_zbt (phi : Word → R) :
    eval phi (heldDelete [.z,.b,.t]) = 3 * phi [.z,.b] := by
  simp only [heldDelete_zb, U, F, K, prefix_nil, List.append_nil,
    eval_prefix, eval_one, heldDelete, selected, eval_append, eval_nil, difference_nil]
  grind

#print axioms heldDelete_zb
#print axioms heldDelete_zz
#print axioms heldDelete_zbt
end StackSorting.SignedWord
