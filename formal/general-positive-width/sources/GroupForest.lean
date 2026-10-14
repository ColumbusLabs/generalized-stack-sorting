import GroupPathForest
import TreeRelabel

namespace StackSorting.Simon
open FactorizationTree

variable {A G : Type*} [Group G]

/-- Prefix-list vertices distinguish equal group values carried by different
original letters; redecoration therefore preserves the literal input word. -/
def decoratedEdges (p : List A) : List A → List (List A × List A)
  | [] => []
  | a :: w => (p, p ++ [a]) :: decoratedEdges (p ++ [a]) w

def internalPrefixLists (p : List A) : List A → List (List A)
  | [] => []
  | [_] => []
  | a :: b :: w => (p ++ [a]) :: internalPrefixLists (p ++ [a]) (b :: w)

def edgeLetter (fallback : A) (edge : List A × List A) : A :=
  edge.2.getLastD fallback

theorem decoratedEdges_map (fallback : A) (p w : List A) :
    (decoratedEdges p w).map (edgeLetter fallback) = w := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp [decoratedEdges, edgeLetter, ih]

theorem pathLetters_internalPrefixLists (p w : List A) (hne : w ≠ []) :
    pathLetters p (internalPrefixLists p w) (p ++ w) = decoratedEdges p w := by
  induction w generalizing p with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil => simp [internalPrefixLists, pathLetters, decoratedEdges]
    | cons b rest =>
      simpa [internalPrefixLists, pathLetters, decoratedEdges, List.append_assoc]
        using congrArg (List.cons (p, p ++ [a])) (ih (p ++ [a]) (by simp))

theorem decoratedEdges_value (φ : A → G) (fallback : A) (p w : List A) :
    ∀ edge ∈ decoratedEdges p w,
      φ (edgeLetter fallback edge) =
        pathValue (fun v : List A => (v.map φ).prod) edge := by
  induction w generalizing p with
  | nil => simp [decoratedEdges]
  | cons a w ih =>
    intro edge he
    simp only [decoratedEdges, List.mem_cons] at he
    rcases he with rfl | he
    · simp [edgeLetter, pathValue]
    · exact ih (p ++ [a]) edge he

/-- Simon's factorization-forest existence for an arbitrary letter map into a
finite group. This constructs a tree with the exact original leaf word. -/
theorem exists_finite_group_factorization_tree [Fintype G]
    (φ : A → G) (w : List A) (hne : w ≠ []) :
    HasTree φ w (3 * Fintype.card G) := by
  obtain ⟨a, tail, hw⟩ := List.exists_cons_of_ne_nil hne
  let color : List A → G := fun p => (p.map φ).prod
  have ht := exists_group_path_tree color ([] : List A) w (internalPrefixLists [] w)
  have heq : pathLetters ([] : List A) (internalPrefixLists [] w) w =
      decoratedEdges [] w := by
    simpa using pathLetters_internalPrefixLists ([] : List A) w hne
  rw [heq] at ht
  have hm := hasTree_map (pathValue color) φ (edgeLetter a)
    (decoratedEdges [] w) (3 * Fintype.card G) ht
    (decoratedEdges_value φ a [] w)
  simpa only [decoratedEdges_map] using hm

#print axioms exists_finite_group_factorization_tree
end StackSorting.Simon
