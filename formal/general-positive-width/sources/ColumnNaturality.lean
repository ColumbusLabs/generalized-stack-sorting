import RestrictedWindow
import ColumnSeparation

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}
namespace Occurrence
variable {P : Packed k} {ps : List (Packed k)}

/-- Appending letters does not change an occurrence's index. -/
def append : {ps : List (Packed k)} → (h : Occurrence P ps) → (ys : List (Packed k)) → Occurrence P (ps ++ ys)
  | _, .head xs, ys => .head (xs ++ ys)
  | _, .tail h, ys => .tail (h.append ys)

@[simp] theorem append_index (h : Occurrence P ps) (ys : List (Packed k)) :
    (h.append ys).index = h.index := by
  induction h with
  | head xs => rfl
  | tail h ih => simp only [append,index,ih]

/-- Every occurrence determines a literal prepend-center-suffix cut. -/
theorem exists_cut (h : Occurrence P ps) :
    ∃ ls rs, ps = ls ++ P :: rs ∧ h.index = ls.length := by
  induction h with
  | head rs => exact ⟨[],rs,rfl,rfl⟩
  | @tail Q ps h ih =>
    obtain ⟨ls,rs,hps,hi⟩ := ih
    exact ⟨Q :: ls,rs,by simp [hps],by simp [index,hi]⟩

theorem eq_of_index_eq (h h' : Occurrence P ps) (hi : h.index = h'.index) : h = h' := by
  induction ps with
  | nil => exact (h.ne_nil rfl).elim
  | cons Q ps ih =>
    cases h with
    | head _ =>
      cases h' with
      | head _ => rfl
      | tail h' => simp [index] at hi
    | tail h =>
      cases h' with
      | head _ => simp [index] at hi
      | tail h' =>
        have he : h = h' := ih h h' (by simpa [index] using hi)
        exact congrArg Occurrence.tail he
end Occurrence

/-- Reassociation commutes with every actual column in the left block. -/
theorem evalAppendIso_column_left (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ [])
    {P : Packed k} (h : Occurrence P xs) (v : P.Vertex) :
    (evalAppendIso xs ys hx hy).vertex ((h.append ys).column v) =
      inLeft (Packed.eval xs).graph (Packed.eval ys).graph (h.column v) := by
  induction xs with
  | nil => exact (hx rfl).elim
  | cons A xs ih =>
    cases xs with
    | nil =>
      cases h with
      | head _ =>
        cases ys with
        | nil => exact (hy rfl).elim
        | cons Q qs => rfl
      | tail h => exact (h.ne_nil rfl).elim
    | cons B bs =>
      cases h with
      | head _ => rfl
      | tail h =>
        change assocReverse A.graph (Packed.eval (B :: bs)).graph (Packed.eval ys).graph
          (inRight A.graph (glue (Packed.eval (B :: bs)).graph (Packed.eval ys).graph)
            ((evalAppendIso (B :: bs) ys (by simp) hy).vertex ((h.append ys).column v))) = _
        rw [ih (by simp) h]
        rfl

/-- Reassociation commutes with every actual column in the right block. -/
theorem evalAppendIso_column_right (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ [])
    {P : Packed k} (h : Occurrence P ys) (v : P.Vertex) :
    (evalAppendIso xs ys hx hy).vertex ((h.prepend xs).column v) =
      inRight (Packed.eval xs).graph (Packed.eval ys).graph (h.column v) := by
  induction xs with
  | nil => exact (hx rfl).elim
  | cons A xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact (hy rfl).elim
      | cons Q qs => rfl
    | cons B bs =>
      change assocReverse A.graph (Packed.eval (B :: bs)).graph (Packed.eval ys).graph
        (inRight A.graph (glue (Packed.eval (B :: bs)).graph (Packed.eval ys).graph)
          ((evalAppendIso (B :: bs) ys (by simp) hy).vertex ((h.prepend (B :: bs)).column v))) = _
      rw [ih (by simp)]
      rfl

/-- The last-column block injection is the same map as its literal ordered
occurrence. This connects the three-factor window to numerical indices. -/
theorem lastColumn_eq_occurrence (xs : List (Packed k)) (P : Packed k) (v : P.Vertex) :
    lastColumn xs P v = ((Occurrence.head []).prepend xs).column v := by
  cases xs with
  | nil => rfl
  | cons Q qs =>
    apply (evalAppendIso (Q :: qs) [P] (by simp) (by simp)).vertex.injective
    change (evalAppendIso (Q :: qs) [P] (by simp) (by simp)).vertex
      ((evalAppendIso (Q :: qs) [P] (by simp) (by simp)).vertex.symm
        (inRight _ _ v)) = _
    rw [Equiv.apply_symm_apply]
    exact (evalAppendIso_column_right (Q :: qs) [P] (by simp) (by simp)
      (Occurrence.head []) v).symm

#print axioms evalAppendIso_column_left
#print axioms evalAppendIso_column_right
#print axioms lastColumn_eq_occurrence
end StackSorting.BiInterface.RepeatedColumn
