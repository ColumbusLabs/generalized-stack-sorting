import ColumnNaturality

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

/-- A middle occurrence in its literal left-to-right word. -/
def middleOccurrence (ls : List (Packed k)) (L H R : Packed k) (rs : List (Packed k)) :
    Occurrence H ((ls ++ [L]) ++ H :: R :: rs) :=
  (Occurrence.head (R :: rs)).prepend (ls ++ [L])

private theorem middleOccurrence_map (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) (v : H.Vertex) :
    (evalAppendIso (ls ++ [L]) (H :: R :: rs) (by simp) (by simp)).vertex
      ((middleOccurrence ls L H R rs).column v) =
      middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph v :=
  evalAppendIso_column_right _ _ _ _ (Occurrence.head (R :: rs)) v

private theorem threeColumnSet_indexed (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) (q)
    (hq : q ∈ threeColumnSet ls L H R rs) :
    (evalAppendIso (ls ++ [L]) (H :: R :: rs) (by simp) (by simp)).vertex.symm q ∈
      columnWindow ((ls ++ [L]) ++ H :: R :: rs) (ls.length + 1) 1 := by
  let E : Iso (Packed.eval ((ls ++ [L]) ++ H :: R :: rs)).graph
      (glue (Packed.eval (ls ++ [L])).graph (glue H.graph (Packed.eval (R :: rs)).graph)) :=
    evalAppendIso (ls ++ [L]) (H :: R :: rs) (by simp) (by simp)
  rcases hq with (⟨v,rfl⟩ | ⟨v,rfl⟩) | ⟨v,rfl⟩
  · let h : Occurrence L ((ls ++ [L]) ++ H :: R :: rs) :=
      ((Occurrence.head []).prepend ls).append (H :: R :: rs)
    have hm : E.vertex (h.column v) = inLeft (Packed.eval (ls ++ [L])).graph
        (glue H.graph (Packed.eval (R :: rs)).graph) (lastColumn ls L v) := by
      rw [lastColumn_eq_occurrence]
      exact evalAppendIso_column_left _ _ _ _ ((Occurrence.head []).prepend ls) v
    change E.vertex.symm _ ∈ _
    have hh := (E.vertex.symm_apply_eq).mpr hm.symm
    apply hh.symm ▸ mem_columnWindow h v
    · simp [h,Occurrence.index] ; omega
    · simp [h,Occurrence.index]
  · change E.vertex.symm _ ∈ _
    have hm : E.vertex ((middleOccurrence ls L H R rs).column v) =
        middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph v :=
      middleOccurrence_map ls L H R rs v
    have hh := (E.vertex.symm_apply_eq).mpr hm.symm
    apply hh.symm ▸ mem_columnWindow (middleOccurrence ls L H R rs) v
    · simp [middleOccurrence,Occurrence.index]
    · simp [middleOccurrence,Occurrence.index]
  · let h : Occurrence R ((ls ++ [L]) ++ H :: R :: rs) :=
      (Occurrence.tail (Q := H) (Occurrence.head rs)).prepend (ls ++ [L])
    have hm : E.vertex (h.column v) = inRight (Packed.eval (ls ++ [L])).graph
        (glue H.graph (Packed.eval (R :: rs)).graph)
        (inRight H.graph (Packed.eval (R :: rs)).graph (firstColumn R rs v)) :=
      evalAppendIso_column_right _ _ _ _ (Occurrence.tail (Q := H) (Occurrence.head rs)) v
    change E.vertex.symm _ ∈ _
    have hh := (E.vertex.symm_apply_eq).mpr hm.symm
    apply hh.symm ▸ mem_columnWindow h v
    · simp [h,Occurrence.index, Nat.add_assoc]
    · simp [h,Occurrence.index, Nat.add_assoc]

/-- Actual indexed radius-one locality at every interior position of a word
with homogeneous idempotent padding. Both endpoints may be unnamed vertices
of the middle graph. The output walk lies in the original evaluated graph. -/
theorem indexed_middle_locality (e : Abstract k) (he : e * e = e)
    (ls rs : List (Packed.{0} k)) (L H R : Packed.{0} k)
    (hls : ∀ P ∈ ls ++ [L], abstractGraph P.graph = e)
    (hrs : ∀ P ∈ R :: rs, abstractGraph P.graph = e)
    (x y : H.Vertex)
    (hxy : Reach (Packed.eval ((ls ++ [L]) ++ H :: R :: rs)).graph.Adj
      ((middleOccurrence ls L H R rs).column x) ((middleOccurrence ls L H R rs).column y)) :
    Through (Packed.eval ((ls ++ [L]) ++ H :: R :: rs)).graph.Adj
      (columnWindow ((ls ++ [L]) ++ H :: R :: rs) (ls.length + 1) 1)
      ((middleOccurrence ls L H R rs).column x) ((middleOccurrence ls L H R rs).column y) := by
  let E : Iso (Packed.eval ((ls ++ [L]) ++ H :: R :: rs)).graph
      (glue (Packed.eval (ls ++ [L])).graph (glue H.graph (Packed.eval (R :: rs)).graph)) :=
    evalAppendIso (ls ++ [L]) (H :: R :: rs) (by simp) (by simp)
  have hg := (reach_iso_iff E _ _).mpr hxy
  have hgm : Reach (glue (Packed.eval (ls ++ [L])).graph
      (glue H.graph (Packed.eval (R :: rs)).graph)).Adj
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph x)
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph y) := by
    have hm (v : H.Vertex) : E.vertex ((middleOccurrence ls L H R rs).column v) =
        middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph v :=
      middleOccurrence_map ls L H R rs v
    exact hm x ▸ hm y ▸ hg
  have hw := idempotent_restricted_three_column_walk e he ls rs L H R hls hrs x y hgm
  have hout := hw.map E.vertex.symm
    (by intro a b hab; exact (E.adj _ _).mp (by simpa using hab))
    (fun q hq => threeColumnSet_indexed ls L H R rs q hq)
  have hx : E.vertex.symm (middleColumn (Packed.eval (ls ++ [L])).graph H.graph
      (Packed.eval (R :: rs)).graph x) = (middleOccurrence ls L H R rs).column x := by
    exact (E.vertex.symm_apply_eq).mpr (middleOccurrence_map ls L H R rs x).symm
  have hy : E.vertex.symm (middleColumn (Packed.eval (ls ++ [L])).graph H.graph
      (Packed.eval (R :: rs)).graph y) = (middleOccurrence ls L H R rs).column y := by
    exact (E.vertex.symm_apply_eq).mpr (middleOccurrence_map ls L H R rs y).symm
  simpa only [hx,hy] using hout

#print axioms indexed_middle_locality
end StackSorting.BiInterface.RepeatedColumn
