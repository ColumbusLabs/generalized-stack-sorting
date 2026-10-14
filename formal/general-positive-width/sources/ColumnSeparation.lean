import OrderedColumns

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

def DisjointInterfaces {V : Type*} (G : Graph k V) : Prop :=
  ∀ i j v, G.left i = some v → G.right j = some v → False

/-- When every letter has disjoint interfaces, an outer left port can occur
only in the first column. This fails without the disjointness hypothesis. -/
theorem leftPort_index_zero {P : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (hd : ∀ Q ∈ ps, DisjointInterfaces Q.graph)
    (i : Fin k) (x : P.Vertex)
    (hp : (Packed.eval ps).graph.left i = some (h.column x)) : h.index = 0 := by
  cases h with
  | head ps => rfl
  | @tail Q ps h =>
    cases ps with
    | nil => exact (h.ne_nil rfl).elim
    | cons R rs =>
      change (Q.graph.left i).map (inLeft Q.graph (Packed.eval (R :: rs)).graph) =
        some (inRight Q.graph (Packed.eval (R :: rs)).graph (h.column x)) at hp
      obtain ⟨v,hv,he⟩ := Option.map_eq_some_iff.mp hp
      obtain ⟨j,hj,_⟩ := (inLeft_eq_inRight Q.graph (Packed.eval (R :: rs)).graph _ _).mp he
      exact (hd Q (by simp) i j v hv hj).elim

/-- Actual quotient column images overlap only at equal or consecutive
indices. The proof uses the genuine seam relation and the disjoint interfaces,
not an assumed interval decomposition. -/
theorem column_overlap_indices {P Q : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (h' : Occurrence Q ps)
    (hd : ∀ R ∈ ps, DisjointInterfaces R.graph)
    (x : P.Vertex) (y : Q.Vertex) (he : h.column x = h'.column y) :
    h.index ≤ h'.index + 1 ∧ h'.index ≤ h.index + 1 := by
  induction ps generalizing P Q with
  | nil => exact (h.ne_nil rfl).elim
  | cons A ps ih =>
    have hdt : ∀ R ∈ ps, DisjointInterfaces R.graph := by
      intro R hR
      exact hd R (by simp [hR])
    cases h with
    | head _ =>
      cases h' with
      | head _ => simp [Occurrence.index]
      | tail h' =>
        cases ps with
        | nil => exact (h'.ne_nil rfl).elim
        | cons B bs =>
          obtain ⟨i,_,hi⟩ := (inLeft_eq_inRight A.graph (Packed.eval (B :: bs)).graph _ _).mp he
          have hz := leftPort_index_zero h' hdt i y hi
          simp [Occurrence.index,hz]
    | tail h =>
      cases h' with
      | head _ =>
        cases ps with
        | nil => exact (h.ne_nil rfl).elim
        | cons B bs =>
          obtain ⟨i,_,hi⟩ := (inLeft_eq_inRight A.graph (Packed.eval (B :: bs)).graph _ _).mp he.symm
          have hz := leftPort_index_zero h hdt i x hi
          simp [Occurrence.index,hz]
      | tail h' =>
        cases ps with
        | nil => exact (h.ne_nil rfl).elim
        | cons B bs =>
          have he' := inRight_injective A.graph (Packed.eval (B :: bs)).graph he
          have hh := ih h h' hdt x y he'
          simp only [Occurrence.index]
          omega

/-- A radius-r window is the union of the actual ordered column images whose
index is at distance at most r from its center. -/
def columnWindow (ps : List (Packed k)) (center radius : ℕ) : Set (Packed.eval ps).Vertex :=
  {q | ∃ (P : Packed k) (h : Occurrence P ps) (x : P.Vertex),
    h.index ≤ center + radius ∧ center ≤ h.index + radius ∧ h.column x = q}

theorem mem_columnWindow {P : Packed k} {ps : List (Packed k)} (h : Occurrence P ps)
    (x : P.Vertex) (c r : ℕ) (hl : h.index ≤ c + r) (hr : c ≤ h.index + r) :
    h.column x ∈ columnWindow ps c r := ⟨P,h,x,hl,hr,rfl⟩

/-- Adjacent column images can share vertices, so the safe separation bound
for radius-r windows is 2r+1, not 2r. -/
theorem window_overlap_indices (ps : List (Packed k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) (i j r : ℕ)
    {v : (Packed.eval ps).Vertex}
    (hi : v ∈ columnWindow ps i r) (hj : v ∈ columnWindow ps j r) :
    i ≤ j + 2 * r + 1 ∧ j ≤ i + 2 * r + 1 := by
  obtain ⟨P,h,x,hxi,hix,hx⟩ := hi
  obtain ⟨Q,h',y,hyj,hjy,hy⟩ := hj
  have hh := column_overlap_indices h h' hd x y (hx.trans hy.symm)
  omega

/-- Windows whose centers differ by at least 2r+2 are disjoint. -/
theorem windows_disjoint (ps : List (Packed k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) (i j r : ℕ)
    (hsep : i + 2 * r + 1 < j ∨ j + 2 * r + 1 < i) :
    Disjoint (columnWindow ps i r) (columnWindow ps j r) := by
  rw [Set.disjoint_left]
  intro v hi hj
  have hh := window_overlap_indices ps hd i j r hi hj
  omega

/-- Four residue classes safely separate radius-one windows. The constant
4 includes the extra possible overlap between consecutive endpoint columns. -/
theorem radius_one_same_residue_disjoint (ps : List (Packed k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) (i j : ℕ)
    (hne : i ≠ j) (hmod : i % 4 = j % 4) :
    Disjoint (columnWindow ps i 1) (columnWindow ps j 1) := by
  apply windows_disjoint ps hd i j 1
  omega

#print axioms column_overlap_indices
#print axioms windows_disjoint
end StackSorting.BiInterface.RepeatedColumn
