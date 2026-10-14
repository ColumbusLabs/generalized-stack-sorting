import FiniteListPaths

namespace StackSorting.GraphWidth.UCurve
open Generalized

def crossingNode {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) (hc : Crosses D e v) : Node D :=
  ⟨(vertices D).idxOf (.crossing e v),
    List.idxOf_lt_length_of_mem ((mem_vertices D (.crossing e v)).mpr hc)⟩

@[simp] theorem nodeVertex_crossingNode {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) (hc : Crosses D e v) :
    nodeVertex D (crossingNode D e v hc) = .crossing e v := List.getElem_idxOf _

/-- The directed prefix to a stem crossing uses only that stem's endpoint and
its crossing vertices, so its actual number of edges is bounded by the number
of stem crossings. Horizontal segments may have arbitrarily many crossings. -/
theorem stem_counted_path {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {v : Fin tokens} (hc : Crosses D e v)
    {q : Node D} (hq : nodeVertex D q = .crossing e v) :
    ∃ length, length ≤ (stemCrossings D e).length ∧
      CountWalk (sourceGraph D).Adj length (anchor D e) q := by
  have hqmem : q ∈ directedNodes D e := by
    apply (mem_directedNodes D e q).mpr
    simp [labels, hq, Vertex.labels]
  have hqdist : nodeDistance D e q = D.depth v := by
    change endpointDistance D e ((nodeVertex D q).point D) = D.depth v
    rw [hq]
    exact endpointDistance_crossing D hc
  let path := prefixThrough (directedNodes D e) q
  have hnpath : path.Nodup := prefixThrough_nodup (directedNodes_nodup D e) q
  have hnmap : (path.map (nodeVertex D)).Nodup :=
    hnpath.map (nodeVertex D) (fun i j hn he => hn (nodeVertex_injective D he))
  have hsub : path.map (nodeVertex D) ⊆
      Vertex.endpoint e :: (stemCrossings D e).map (Vertex.crossing e) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hid : i ∈ directedNodes D e := prefixThrough_subset _ _ hi
    have hicurve : OnCurve D (E.owner e) ((nodeVertex D i).point D) :=
      (vertex_labels_exact D (nodeVertex_valid D i) _).mp
        ((mem_directedNodes D e i).mp hid)
    have hibound := prefixThrough_ordered_bound (nodeDistance D e)
      (directedNodes_sorted D e) hqmem i hi
    have hshort : nodeDistance D e i < D.depth (E.owner e) := by
      have hd := hc.2.2
      omega
    have htime := (near_endpoint_on_stem D hicurve hshort).1
    cases hix : nodeVertex D i with
    | endpoint f =>
      rw [hix] at htime
      have heq : f = e := Fin.ext htime
      simp [heq]
    | crossing f u =>
      rw [hix] at htime
      have heq : f = e := Fin.ext htime
      subst f
      have hvalid : Crosses D e u := by simpa [hix, Vertex.Valid] using nodeVertex_valid D i
      exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨u, (mem_stemCrossings D e u).mpr hvalid, rfl⟩)
  have hlength := hnmap.length_le_of_subset hsub
  simp only [List.length_map, List.length_cons] at hlength
  refine ⟨path.length - 1, by omega, ?_⟩
  obtain ⟨tail, htail⟩ := directedNodes_starts_at_anchor D e
  dsimp only [path]
  rw [htail]
  exact prefixThrough_countWalk (anchor D e) tail (htail ▸ hqmem)
    (fun i j hij => directedNodes_edge D e (htail.symm ▸ hij))

/-- Every source vertex has a short graph path from an endpoint on its stem.
This is a graph-distance statement, not an outer-face or planarity assertion. -/
theorem source_radius_from_stems {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (k : Nat)
    (hbound : ∀ e, (stemCrossings D e).length < k) (q : Node D) :
    ∃ e : Fin events, ∃ length, length ≤ k-1 ∧
      CountWalk (sourceGraph D).Adj length (anchor D e) q := by
  cases hq : nodeVertex D q with
  | endpoint e =>
    have hqe : q = anchor D e := nodeVertex_injective D (hq.trans (nodeVertex_anchor D e).symm)
    subst q
    exact ⟨e, 0, Nat.zero_le _, CountWalk.refl (anchor D e)⟩
  | crossing e v =>
    have hc : Crosses D e v := by simpa [hq, Vertex.Valid] using nodeVertex_valid D q
    obtain ⟨length, hlen, hwalk⟩ := stem_counted_path D hc hq
    exact ⟨e, length, by have := hbound e; omega, hwalk⟩

/-- Original-machine generation now supplies an explicit finite source graph
whose every vertex has distance at most max(r,s)-1 from a baseline endpoint. -/
theorem generated_source_radius {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Run r s [] (List.range n) output []) :
    ∃ D : Drawing (canonicalPairing hp), ∀ q : Node D,
      ∃ e : Fin (canonicalEvents 0 output).length, ∃ length, length ≤ max r s - 1 ∧
        CountWalk (sourceGraph D).Adj length (anchor D e) q := by
  obtain ⟨D, hstems⟩ := generated_drawing hp hrun
  refine ⟨D, source_radius_from_stems D (max r s) ?_⟩
  intro e
  obtain he | he := (canonicalPairing hp).complete e
  · have h := (hstems ((canonicalPairing hp).owner e)).1
    rw [← he] at h
    exact Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)
  · have h := (hstems ((canonicalPairing hp).owner e)).2
    rw [← he] at h
    exact Nat.lt_of_lt_of_le h (Nat.le_max_right _ _)

end StackSorting.GraphWidth.UCurve
