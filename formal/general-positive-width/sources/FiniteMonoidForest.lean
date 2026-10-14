import MarkedLocalReduction
import UnitImageForest

universe u v
namespace StackSorting.Simon
open FactorizationTree

/-- A coarse explicit cardinal-only bound. It is intentionally not the sharp
3|M| bound: its purpose is to make the local-divisor induction quantitative. -/
def monoidForestBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * ((3 * (n + 1) + 3) * monoidForestBound n + 2) + 3 * (n + 1)

/-- Simultaneous induction over all monoids of cardinality at most n and over
the finite support of the actual letter images. -/
theorem finiteMonoidForest_upTo (n : ℕ) :
    ∀ (M : Type v) [Monoid M] [Fintype M], Fintype.card M ≤ n →
      ∀ (A : Type u) (φ : A → M) (w : List A), w ≠ [] →
        HasTree φ w (monoidForestBound n) := by
  induction n with
  | zero =>
    intro M _ _ hcard A φ w hne
    have hp : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨1⟩
    omega
  | succ n ih =>
    intro M _ _ hcard A φ w hne
    classical
    let D := (3 * (n + 1) + 3) * monoidForestBound n + 2
    have build : ∀ F : Finset M, ∀ z : List A,
        z ≠ [] → (∀ a ∈ z, φ a ∈ F) →
        HasTree φ z (F.card * D + 3 * (n + 1)) := by
      intro F
      refine Finset.strongInductionOn F ?_
      intro F inner z hzne hvals
      by_cases hunit : ∀ a ∈ z, IsUnit (φ a)
      · apply hasTree_mono (exists_unit_image_forest φ z hzne hunit)
        omega
      · push Not at hunit
        obtain ⟨a,ha,hna⟩ := hunit
        have hac : φ a ∈ F := hvals a ha
        have hsmall : Fintype.card (LocalDivisor (φ a)) ≤ n := by
          have hs := LocalDivisor.card_lt hna
          omega
        have hlocal : ∀ (B : Type u) (ψ : B → LocalDivisor (φ a)) (u : List B),
            u ≠ [] → HasTree ψ u (monoidForestBound n) := by
          intro B ψ u hune
          exact ih (LocalDivisor (φ a)) hsmall B ψ u hune
        let H := (F.erase (φ a)).card * D + 3 * (n + 1)
        have hsmaller : ∀ u : List A, u ≠ [] →
            (∀ b ∈ u, φ b ∈ F.erase (φ a)) → HasTree φ u H := by
          intro u hune hu
          exact inner (F.erase (φ a)) (Finset.erase_ssubset hac) u hune hu
        have ht := marked_local_divisor_reduction φ F (φ a) z hvals ⟨a,ha,rfl⟩
          H (monoidForestBound n) hsmaller hlocal
        apply hasTree_mono ht
        have hc : (3 * Fintype.card M + 3) * monoidForestBound n ≤
            (3 * (n + 1) + 3) * monoidForestBound n :=
          Nat.mul_le_mul_right _ (by omega)
        have hsize := Finset.card_erase_add_one hac
        rw [← hsize, Nat.add_mul (F.erase (φ a)).card 1 D, one_mul]
        dsimp [H,D]
        omega
    have ht := build Finset.univ w hne (by intro a _; exact Finset.mem_univ (φ a))
    apply hasTree_mono ht
    simp only [Finset.card_univ, monoidForestBound]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right D hcard) _

/-- Genuine Simon existence for finite monoids, arbitrary alphabets, and
nonempty literal words. This is the target theorem, with an explicit uniform
bound depending only on the finite monoid cardinality. -/
theorem exists_finite_monoid_factorization_tree
    {A : Type u} {M : Type v} [Monoid M] [Fintype M]
    (φ : A → M) (w : List A) (hne : w ≠ []) :
    ∃ t : FactorizationTree A, t.leaves = w ∧ Valid φ t ∧
      t.height ≤ monoidForestBound (Fintype.card M) :=
  finiteMonoidForest_upTo (Fintype.card M) M (Nat.le_refl _) A φ w hne

#print axioms exists_finite_monoid_factorization_tree
end StackSorting.Simon
