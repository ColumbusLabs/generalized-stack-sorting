import IndexedLocality

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

/-- Radius-one locality at the first position, including arbitrary unnamed
endpoints and a completely unrestricted suffix length. -/
theorem indexed_first_locality (e : Abstract k) (he : e * e = e)
    (H R : Packed.{0} k) (rs : List (Packed.{0} k))
    (hrs : ∀ P ∈ R :: rs, abstractGraph P.graph = e) (x y : H.Vertex)
    (hxy : Reach (Packed.eval (H :: R :: rs)).graph.Adj
      ((Occurrence.head (R :: rs)).column x) ((Occurrence.head (R :: rs)).column y)) :
    Through (Packed.eval (H :: R :: rs)).graph.Adj (columnWindow (H :: R :: rs) 0 1)
      ((Occurrence.head (R :: rs)).column x) ((Occurrence.head (R :: rs)).column y) := by
  have hp := (idempotent_first_factor_locality e he (R :: rs) (by simp) hrs
    H R (by simp) x y).mp hxy
  apply hp.map (rightWindowEmbed H R rs)
  · intro a b hab
    exact mapSeam_adj _ _ _ _ _ _ _ _ (by intros; assumption)
      (fun _ _ h => firstColumn_adj R rs h) hab
  · intro q _
    induction q using Quotient.inductionOn with | h q =>
      cases q with
      | inl v => exact mem_columnWindow (Occurrence.head (R :: rs)) v 0 1 (by simp [Occurrence.index]) (by simp [Occurrence.index])
      | inr v => exact mem_columnWindow (Occurrence.tail (Q := H) (Occurrence.head rs)) v 0 1 (by simp [Occurrence.index]) (by simp [Occurrence.index])

/-- Radius-one locality at the last position of a literal word. -/
theorem indexed_last_locality (e : Abstract k) (he : e * e = e)
    (ls : List (Packed.{0} k)) (L H : Packed.{0} k)
    (hls : ∀ P ∈ ls ++ [L], abstractGraph P.graph = e) (x y : H.Vertex)
    (hxy : Reach (Packed.eval ((ls ++ [L]) ++ [H])).graph.Adj
      (((Occurrence.head []).prepend (ls ++ [L])).column x)
      (((Occurrence.head []).prepend (ls ++ [L])).column y)) :
    Through (Packed.eval ((ls ++ [L]) ++ [H])).graph.Adj
      (columnWindow ((ls ++ [L]) ++ [H]) (ls.length + 1) 1)
      (((Occurrence.head []).prepend (ls ++ [L])).column x)
      (((Occurrence.head []).prepend (ls ++ [L])).column y) := by
  let E : Iso (Packed.eval ((ls ++ [L]) ++ [H])).graph
      (glue (Packed.eval (ls ++ [L])).graph H.graph) :=
    evalAppendIso (ls ++ [L]) [H] (by simp) (by simp)
  let m := mapSeam L.graph H.graph (Packed.eval (ls ++ [L])).graph H.graph
    (lastColumn ls L) id (lastColumn_right ls L) (by intro i; simp)
  have hmAdj : ∀ a b, (glue L.graph H.graph).Adj a b →
      (glue (Packed.eval (ls ++ [L])).graph H.graph).Adj (m a) (m b) := by
    intro a b hab
    exact mapSeam_adj _ _ _ _ _ _ _ _ (fun _ _ h => lastColumn_adj ls L h) (by intros; assumption) hab
  have hc (v : H.Vertex) : E.vertex (((Occurrence.head []).prepend (ls ++ [L])).column v) =
      inRight (Packed.eval (ls ++ [L])).graph H.graph v :=
    evalAppendIso_column_right _ _ _ _ (Occurrence.head []) v
  have hg := (reach_iso_iff E _ _).mpr hxy
  rw [hc x,hc y] at hg
  have hp := (idempotent_last_factor_locality e he (ls ++ [L]) (by simp) hls
    L H (by simp) x y).mp hg
  have hout := hp.map (fun q => E.vertex.symm (m q))
    (by intro a b hab; exact (E.adj _ _).mp (by simpa using hmAdj a b hab))
    (J := columnWindow ((ls ++ [L]) ++ [H]) (ls.length + 1) 1)
    (by
      intro q _
      induction q using Quotient.inductionOn with | h q =>
        cases q with
        | inl v =>
          let h : Occurrence L ((ls ++ [L]) ++ [H]) :=
            ((Occurrence.head []).prepend ls).append [H]
          have hcol : E.vertex (h.column v) = m (inLeft L.graph H.graph v) := by
            change E.vertex (h.column v) = inLeft (Packed.eval (ls ++ [L])).graph H.graph
              (lastColumn ls L v)
            rw [lastColumn_eq_occurrence]
            exact evalAppendIso_column_left _ _ _ _ ((Occurrence.head []).prepend ls) v
          have hh := (E.vertex.symm_apply_eq).mpr hcol.symm
          exact hh.symm ▸ mem_columnWindow h v _ _
            (by simp [h,Occurrence.index] ; omega) (by simp [h,Occurrence.index])
        | inr v =>
          change E.vertex.symm (inRight (Packed.eval (ls ++ [L])).graph H.graph v) ∈ _
          have hh := (E.vertex.symm_apply_eq).mpr (hc v).symm
          exact hh.symm ▸ mem_columnWindow ((Occurrence.head []).prepend (ls ++ [L])) v _ _
            (by simp [Occurrence.index]) (by simp [Occurrence.index]))
  have hx : E.vertex.symm (m (inRight L.graph H.graph x)) =
      ((Occurrence.head []).prepend (ls ++ [L])).column x := by
    change E.vertex.symm (inRight (Packed.eval (ls ++ [L])).graph H.graph x) = _
    exact (E.vertex.symm_apply_eq).mpr (hc x).symm
  have hy : E.vertex.symm (m (inRight L.graph H.graph y)) =
      ((Occurrence.head []).prepend (ls ++ [L])).column y := by
    change E.vertex.symm (inRight (Packed.eval (ls ++ [L])).graph H.graph y) = _
    exact (E.vertex.symm_apply_eq).mpr (hc y).symm
  simpa only [hx,hy] using hout

/-- Uniform radius one for every actual ordered column of a homogeneous
idempotent word, including first/last/singleton words. No separation assumption
is needed for the locality itself; disjoint interfaces enter only in coloring. -/
theorem idempotent_column_locality (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k))
    (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    {P : Packed.{0} k} (h : Occurrence P ps) (x y : P.Vertex)
    (hxy : Reach (Packed.eval ps).graph.Adj (h.column x) (h.column y)) :
    Through (Packed.eval ps).graph.Adj (columnWindow ps h.index 1) (h.column x) (h.column y) := by
  obtain ⟨ls,rs,hps,hindex⟩ := h.exists_cut
  subst ps
  have hh : h = (Occurrence.head rs).prepend ls := by
    apply Occurrence.eq_of_index_eq
    simpa [Occurrence.index] using hindex
  subst h
  clear hindex
  cases ls using List.reverseRecOn with
  | nil =>
    cases rs with
    | nil =>
      exact hxy.mono (by intros; assumption) (by
        intro v _
        exact mem_columnWindow (Occurrence.head []) v 0 1 (by simp [Occurrence.index]) (by simp [Occurrence.index]))
    | cons R rs =>
      exact indexed_first_locality e he P R rs
        (fun Q hQ => hp Q (List.mem_cons_of_mem P hQ)) x y hxy
  | append_singleton ls L =>
    cases rs with
    | nil =>
      simpa [Occurrence.index] using indexed_last_locality e he ls L P
        (fun Q hQ => hp Q (List.mem_append_left [P] hQ)) x y hxy
    | cons R rs =>
      simpa [middleOccurrence,Occurrence.index] using indexed_middle_locality e he ls rs L P R
        (fun Q hQ => hp Q (List.mem_append_left (P :: R :: rs) hQ))
        (fun Q hQ => hp Q (List.mem_append_right (ls ++ [L]) (List.mem_cons_of_mem P hQ))) x y hxy

#print axioms idempotent_column_locality
end StackSorting.BiInterface.RepeatedColumn
