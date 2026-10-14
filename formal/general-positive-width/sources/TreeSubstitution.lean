import FactorizationTree
import Mathlib.Data.List.Basic

namespace StackSorting.Simon.FactorizationTree

variable {A B M : Type*} [Monoid M]

private theorem le_foldr_max_of_mem (xs : List ℕ) {x : ℕ} (hx : x ∈ xs) :
    x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem prod_flatMap_substitute (φ : A → M) (ψ : B → M) (subst : A → List B)
    (hvalue : ∀ a, ((subst a).map ψ).prod = φ a) (w : List A) :
    ((w.flatMap subst).map ψ).prod = (w.map φ).prod := by
  induction w with
  | nil => simp
  | cons a w ih => simp [hvalue, ih]

/-- Substituting value-preserving trees for leaves adds at most the uniform
substitution height to the original tree height. -/
theorem hasTree_substitute_valid (φ : A → M) (ψ : B → M) (subst : A → List B)
    (H : ℕ) (hbase : ∀ a, HasTree ψ (subst a) H)
    (hvalue : ∀ a, ((subst a).map ψ).prod = φ a)
    (t : FactorizationTree A) (hv : Valid φ t) :
    HasTree ψ (t.leaves.flatMap subst) (t.height + H) := by
  induction hv with
  | leaf a => simpa only [leaves, height, List.flatMap_singleton, Nat.zero_add] using hbase a
  | node ts hchildren harity hbranch ih =>
    let K := (ts.map height).foldr max 0
    have hchild : ∀ r ∈ ts, HasTree ψ (r.leaves.flatMap subst) (K + H) := by
      intro r hr
      apply hasTree_mono (ih r hr)
      exact Nat.add_le_add_right (le_foldr_max_of_mem (ts.map height)
        (List.mem_map.mpr ⟨r, hr, rfl⟩)) H
    let words := ts.map (fun r => r.leaves.flatMap subst)
    have hwords : ∀ w ∈ words, HasTree ψ w (K + H) := by
      intro w hw
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact hchild r hr
    have hforest : HasTree ψ words.flatten (K + H + 1) := by
      rcases hbranch with hbinary | ⟨e, he, hall⟩
      · obtain ⟨r, s, hts⟩ := List.length_eq_two.mp hbinary
        subst ts
        simpa [words] using hasTree_binary (hchild r (by simp)) (hchild s (by simp))
      · refine hasTree_idempotent_blocks ψ words (K + H) ?_ hwords e he ?_
        · have htne : ts ≠ [] := by intro h; simp [h] at harity
          simpa [words] using htne
        · intro w hw
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
          rw [prod_flatMap_substitute φ ψ subst hvalue]
          exact hall r hr
    have heq : words.flatten = (node ts).leaves.flatMap subst := by
      rw [leaves, List.flatMap_assoc]
      change (ts.map (fun r => r.leaves.flatMap subst)).flatten =
        ts.flatMap (fun r => r.leaves.flatMap subst)
      exact List.flatMap_def.symm
    rw [← heq]
    apply hasTree_mono hforest
    rw [height]
    dsimp [K]
    omega

theorem hasTree_substitute (φ : A → M) (ψ : B → M) (subst : A → List B)
    (H : ℕ) (hbase : ∀ a, HasTree ψ (subst a) H)
    (hvalue : ∀ a, ((subst a).map ψ).prod = φ a)
    (w : List A) (h : ℕ) (ht : HasTree φ w h) :
    HasTree ψ (w.flatMap subst) (h + H) := by
  obtain ⟨t, hw, hv, hh⟩ := ht
  have hs := hasTree_substitute_valid φ ψ subst H hbase hvalue t hv
  rw [hw] at hs
  exact hasTree_mono hs (Nat.add_le_add_right hh H)

#print axioms hasTree_substitute
end StackSorting.Simon.FactorizationTree
