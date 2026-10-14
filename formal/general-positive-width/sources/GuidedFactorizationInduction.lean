import GuidedBinaryGluing
import GuidedIdempotentWord
import WordBlockReassociation
import GuidanceBounds

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth Simon Simon.FactorizationTree
variable {k : Nat}

private theorem child_height_le {A : Type*} {t : FactorizationTree A}
    {ts : List (FactorizationTree A)} (ht : t ∈ ts) :
    t.height ≤ (ts.map height).foldr max 0 := by
  induction ts with
  | nil => simp at ht
  | cons s ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

/-- Construct a captured decomposition by induction on a genuine Simon tree.
The leaf bound is actual vertex cardinality; binary and idempotent nodes use
the proved graph constructions rather than a supplied capture witness. -/
theorem exists_guided_factorization (t : FactorizationTree (Packed.{0} k))
    (hv : SemigroupValid (fun P : Packed.{0} k => abstractGraph P.graph) t)
    (hsmall : ∀ P ∈ t.leaves, Nat.card P.Vertex ≤ k) :
    Nonempty (GuidedDecomposition (Packed.eval t.leaves).graph.simple Set.univ
      (paletteBound k t.height)) := by
  revert hsmall
  induction hv with
  | leaf P =>
    intro hs
    rw [leaves, height, paletteBound, Packed.eval_singleton]
    exact GuidedDecomposition.exists_bounded P.graph.simple (hs P (by simp [leaves]))
  | node ts hc ha hb ih =>
    intro hs
    rw [leaves] at hs
    rw [leaves, height]
    let H := (ts.map height).foldr max 0
    have htne : ts ≠ [] := by intro he; simp [he] at ha
    have hleaf : ∀ t ∈ ts, t.leaves ≠ [] := fun t ht => semigroupValid_leaves_ne_nil (hc t ht)
    have children : ∀ t ∈ ts,
        Nonempty (GuidedDecomposition (Packed.eval t.leaves).graph.simple Set.univ
          (paletteBound k H)) := by
      intro t ht
      obtain ⟨D⟩ := ih t ht (fun P hP => hs P (by
        exact List.mem_flatMap.mpr ⟨t,ht,hP⟩))
      exact ⟨D.pad (paletteBound_mono k (child_height_le ht))⟩
    change Nonempty (GuidedDecomposition (Packed.eval (ts.flatMap leaves)).graph.simple Set.univ
      (paletteBound k (H+1)))
    rcases hb with hbinary | ⟨e,he,hvalues⟩
    · obtain ⟨s,t,rfl⟩ := List.length_eq_two.mp hbinary
      obtain ⟨D⟩ := children s (by simp)
      obtain ⟨E⟩ := children t (by simp)
      obtain ⟨F⟩ := exists_guided_glue (Packed.eval s.leaves).graph (Packed.eval t.leaves).graph D E
      let F' := (evalAppendIso s.leaves t.leaves (hleaf s (by simp)) (hleaf t (by simp))).symm.mapGuided F
      have F'' := F'.pad (binaryCost_le_step k H)
      have hw : [s,t].flatMap leaves = s.leaves ++ t.leaves := by simp
      rw [hw]
      exact ⟨F''⟩
    · let ps := ts.map (fun t => Packed.eval t.leaves)
      have hps : ps ≠ [] := by simpa [ps] using htne
      have hp : ∀ P ∈ ps, abstractGraph P.graph = e := by
        intro P hP
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hP
        exact abstraction_of_wordValue t.leaves (hleaf t ht) e (hvalues t ht)
      have hD : ∀ P ∈ ps,
          Nonempty (GuidedDecomposition P.graph.simple Set.univ (paletteBound k H)) := by
        intro P hP
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hP
        exact children t ht
      obtain ⟨F⟩ := exists_guided_idempotent_word e he ps hps hp hD
      have hblocks : ∀ w ∈ ts.map leaves, w ≠ [] := by
        intro w hw
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
        exact hleaf t ht
      let iso := evalFlattenIso (ts.map leaves) hblocks
      have F' : GuidedDecomposition (Packed.eval ((ts.map leaves).map Packed.eval)).graph.simple
          Set.univ (2^(3*k)*paletteBound k H+9*k) := by
        rw [List.map_map]
        exact F
      let F'' := iso.symm.mapGuided F'
      have F''' := F''.pad (idempotentCost_le_step k H)
      rw [List.flatMap_def]
      exact ⟨F'''⟩

#print axioms exists_guided_factorization
end StackSorting.BiInterface.RepeatedColumn
