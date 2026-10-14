import Std

namespace StackSorting.FiniteState

/-- A finite configuration walk, with an explicit number of steps implicit in
its inductive derivation. Reflexivity includes the empty walk. -/
inductive Walk {Q : Type} (R : Q → Q → Prop) : Q → Q → Prop
  | refl (x) : Walk R x x
  | step {x y z} : R x y → Walk R y z → Walk R x z

namespace Walk

theorem trans {Q : Type} {R : Q → Q → Prop} {x y z : Q}
    (h : Walk R x y) (g : Walk R y z) : Walk R x z := by
  induction h with
  | refl => exact g
  | step h _ ih => exact .step h (ih g)

theorem closed {Q : Type} {R : Q → Q → Prop} {x y : Q}
    (h : Walk R x y) (S : Q → Prop) (hx : S x)
    (hs : ∀ a b, S a → R a b → S b) : S y := by
  induction h with
  | refl => exact hx
  | step hab _ ih => exact ih (hs _ _ hx hab)

end Walk

/-- One arbitrary unary Boolean set per state suffices to define exactly
finite reachability on the configuration carrier. No finiteness assumption on
vertices, determinism, or semantic recognizability assumption is used. -/
theorem walk_iff_all_closed {P : Type} {k : Nat}
    (R : (P × Fin k) → (P × Fin k) → Prop) (x y : P × Fin k) :
    Walk R x y ↔ ∀ S : Fin k → P → Bool,
      S x.2 x.1 = true →
      (∀ a b, S a.2 a.1 = true → R a b → S b.2 b.1 = true) →
      S y.2 y.1 = true := by
  classical
  constructor
  · intro h S hx hs
    exact h.closed (fun a => S a.2 a.1 = true) hx hs
  · intro h
    have hh := h (fun i p => decide (Walk R x (p,i)))
      (by simp only [decide_eq_true_eq]; exact .refl x)
      (by
        intro a b ha hab
        simp only [decide_eq_true_eq] at ha ⊢
        exact ha.trans (.step hab (.refl b)))
    exact of_decide_eq_true hh

#print axioms walk_iff_all_closed
end StackSorting.FiniteState
