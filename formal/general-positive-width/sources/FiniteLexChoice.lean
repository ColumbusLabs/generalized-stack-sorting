import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Bool.Basic

/-! Finite lexicographic selection of actual monadic annotation tuples.
The existence of an admissible tuple is the only existence premise. -/
namespace StackSorting.CanonicalChoice

variable {P : Type} {k : Nat}
abbrev Witness (P : Type) (k : Nat) := Fin k → P → Bool

/-- Annotation index first; within that set, the first differing actual node.
False precedes true. -/
def Before [LT P] (A B : Witness P k) : Prop :=
  ∃ i, (∀ j, j < i → A j = B j) ∧
    ∃ p, (∀ q, q < p → A i q = B i q) ∧ A i p < B i p

def Selected [LT P] (valid : Witness P k → Prop) (A : Witness P k) : Prop :=
  valid A ∧ ∀ B, valid B → ¬ Before B A

noncomputable def lexCode (A : Witness P k) : Lex (Fin k → Lex (P → Bool)) :=
  toLex (fun i => toLex (A i))

theorem before_iff_lexCode [LT P] (A B : Witness P k) :
    Before A B ↔ lexCode A < lexCode B := Iff.rfl

theorem lexCode_injective : Function.Injective (lexCode (P := P) (k := k)) := by
  intro A B h
  exact h

theorem before_explicit [LT P] (A B : Witness P k) :
    Before A B ↔ ∃ i, (∀ j, j < i → A j = B j) ∧
      ∃ p, (∀ q, q < p → A i q = B i q) ∧ A i p = false ∧ B i p = true := by
  simp only [Before, Bool.lt_iff]

/-- An arbitrary nonempty admissible subset of the finite annotation space
has one lexicographically least member. Uniqueness is proved, not supplied. -/
theorem exists_unique_selected [Fintype P] [LinearOrder P]
    (valid : Witness P k → Prop) (hex : ∃ A, valid A) :
    ∃! A, Selected valid A := by
  classical
  obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {A | valid A} lexCode
    (Set.toFinite _) hex
  refine ⟨A, ⟨hA, ?_⟩, ?_⟩
  · intro B hB hBA
    exact not_lt_of_ge (hmin B hB) ((before_iff_lexCode B A).mp hBA)
  · intro B hB
    apply lexCode_injective
    apply le_antisymm
    · exact le_of_not_gt (fun h => hB.2 A hA ((before_iff_lexCode A B).mpr h))
    · exact hmin B hB.1

/-- Selection cannot manufacture a witness when the underlying relation is empty. -/
theorem selected_exists_iff [Fintype P] [LinearOrder P]
    (valid : Witness P k → Prop) :
    (∃ A, Selected valid A) ↔ ∃ A, valid A := by
  constructor
  · rintro ⟨A, hA⟩; exact ⟨A, hA.1⟩
  · intro h; obtain ⟨A, hA, _⟩ := exists_unique_selected valid h; exact ⟨A, hA⟩

#print axioms exists_unique_selected
#print axioms selected_exists_iff
end StackSorting.CanonicalChoice
