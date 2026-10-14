import GuidanceComponents
import Mathlib.SetTheory.Cardinal.Finite

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}

/-- The color bound is a genuine bag-cardinality bound: two distinct roots
captured at the same vertex cannot use the same color. -/
theorem capture_card_le (C : System G P c) {B : Set V} (h : Captures G C B) :
    Nat.card B ≤ c := by
  classical
  by_cases hb : B.Nonempty
  · obtain ⟨x,hx⟩ := h hb
    let f : B → Fin c := fun r => Classical.choose (hx r r.property)
    have hf : Function.Injective f := by
      intro r s he
      have hr : x ∈ (C (f r)).support r := Classical.choose_spec (hx r r.property)
      have hs : x ∈ (C (f s)).support s := Classical.choose_spec (hx s s.property)
      rw [← he] at hs
      exact Subtype.ext ((C (f r)).unique r s x hr hs)
    let : Fintype B := Fintype.ofInjective f hf
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hb
    subst B
    simp

#print axioms capture_card_le
end StackSorting.GuidedPathwidth
