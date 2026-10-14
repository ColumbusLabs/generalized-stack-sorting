import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

namespace StackSorting.FiniteTupleBound

/-- A bounded first-order tuple test: every b+1 points in the set have a
repetition. This does not count duplicate entries in a presentation list. -/
def Repeats {α : Type} (P : α → Prop) (b : Nat) : Prop :=
  ∀ f : Fin (b+1) → α, (∀ i, P (f i)) → ¬ Function.Injective f

noncomputable def points {α : Type} [Fintype α] (P : α → Prop) : Finset α := by
  classical
  exact Finset.univ.filter P

@[simp] theorem mem_points {α : Type} [Fintype α] (P : α → Prop) (x : α) :
    x ∈ points P ↔ P x := by
  classical
  simp [points]

theorem repeats_iff_card_le {α : Type} [Fintype α] (P : α → Prop) (b : Nat) :
    Repeats P b ↔ (points P).card ≤ b := by
  classical
  constructor
  · intro h
    by_contra hn
    have hl : Fintype.card (Fin (b+1)) ≤ Fintype.card {x // x ∈ points P} := by
      simp only [Fintype.card_fin,Fintype.card_coe]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hl
    let f : Fin (b+1) → α := fun i => (e i).val
    have hf : ∀ i, P (f i) := fun i => (mem_points P (f i)).mp (e i).property
    apply h f hf
    intro i j he
    exact e.injective (Subtype.ext he)
  · intro hb f hf hi
    let g : Fin (b+1) → {x // x ∈ points P} := fun i => ⟨f i,(mem_points P (f i)).mpr (hf i)⟩
    have hg : Function.Injective g := fun i j he => hi (congrArg Subtype.val he)
    have hc := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin,Fintype.card_coe] at hc
    omega

#print axioms repeats_iff_card_le
end StackSorting.FiniteTupleBound
