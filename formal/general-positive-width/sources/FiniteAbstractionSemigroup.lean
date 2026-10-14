import AbstractionCongruence
import SemigroupForest
import Mathlib.Data.Fintype.BigOperators

namespace StackSorting.BiInterface

/-- Realizable finite interface tables. The carrier is a subtype of one fixed
finite Boolean table type; the representing graph is not part of its data. -/
def Abstract (k : ℕ) := {c : Code k // ∃ (V : Type) (G : Graph k V), abstraction G = c}

noncomputable instance (k : ℕ) : Fintype (Abstract k) :=
  Fintype.ofInjective (fun c : Abstract k => c.val) Subtype.val_injective

theorem abstract_card_le_code (k : ℕ) : Fintype.card (Abstract k) ≤ Fintype.card (Code k) :=
  Fintype.card_le_of_injective (fun c : Abstract k => c.val) Subtype.val_injective

/-- An explicit finite state bound. It is intentionally not optimized. -/
theorem code_card (k : ℕ) : Fintype.card (Code k) = 2 ^ (2 * k + 8 * k * k) := by
  simp only [Code,Port,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  ring

namespace Abstract
variable {k : ℕ}

noncomputable def representativeType (c : Abstract k) : Type := Classical.choose c.property
noncomputable def representative (c : Abstract k) : Graph k (representativeType c) :=
  Classical.choose (Classical.choose_spec c.property)

theorem representative_spec (c : Abstract k) : abstraction (representative c) = c.val :=
  Classical.choose_spec (Classical.choose_spec c.property)

noncomputable def multiply (a b : Abstract k) : Abstract k :=
  ⟨abstraction (glue (representative a) (representative b)),
    ⟨Glued (representative a) (representative b),glue (representative a) (representative b),rfl⟩⟩

noncomputable instance : Semigroup (Abstract k) where
  mul := multiply
  mul_assoc a b c := by
    apply Subtype.ext
    change abstraction (glue (representative (multiply a b)) (representative c)) =
      abstraction (glue (representative a) (representative (multiply b c)))
    calc
      _ = abstraction (glue (glue (representative a) (representative b)) (representative c)) :=
        abstraction_glue_congr _ _ _ _ (representative_spec (multiply a b)) rfl
      _ = abstraction (glue (representative a) (glue (representative b) (representative c))) :=
        abstraction_glue_assoc _ _ _
      _ = _ := abstraction_glue_congr _ _ _ _ rfl (representative_spec (multiply b c)).symm

end Abstract

noncomputable def abstractGraph {k : ℕ} {V : Type} (G : Graph k V) : Abstract k :=
  ⟨abstraction G,⟨V,G,rfl⟩⟩

/-- Multiplication is well-defined independently of the chosen representatives
and the abstraction map preserves actual partial-interface gluing. -/
theorem abstractGraph_glue {k : ℕ} {V W : Type} (G : Graph k V) (H : Graph k W) :
    abstractGraph (glue G H) = abstractGraph G * abstractGraph H := by
  apply Subtype.ext
  exact abstraction_glue_congr _ _ _ _
    (Abstract.representative_spec (abstractGraph G)).symm
    (Abstract.representative_spec (abstractGraph H)).symm

/-- A literal finite small graph letter. Labels and interface identities are
retained; no quotient is applied to the word's letters. -/
structure Piece (k : ℕ) where
  size : ℕ
  graph : Graph k (Fin size)

abbrev SmallPiece (k W : ℕ) := {p : Piece k // p.size ≤ W}

/-- Uniform factorization of actual small-piece words, using the proved finite
semigroup quotient and the proved adjoining-identity bridge. -/
theorem exists_small_piece_factorization (k W : ℕ) (w : List (SmallPiece k W)) (hne : w ≠ []) :
    ∃ t : Simon.FactorizationTree (SmallPiece k W), t.leaves = w ∧
      Simon.SemigroupValid (fun p : SmallPiece k W => abstractGraph p.val.graph) t ∧
      t.height ≤ Simon.monoidForestBound (Fintype.card (Abstract k) + 1) :=
  Simon.exists_finite_semigroup_factorization_tree _ w hne

#print axioms abstractGraph_glue
#print axioms exists_small_piece_factorization
end StackSorting.BiInterface
