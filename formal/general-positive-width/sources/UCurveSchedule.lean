import UCurveGraph

namespace StackSorting.GraphWidth.UCurve
open Generalized IntervalCritical SparseEndpointMSO

theorem idxOf_injective_mem {xs : List Nat} {u v : Nat}
    (hu : u ∈ xs) (hv : v ∈ xs) (h : xs.idxOf u = xs.idxOf v) : u = v := by
  have hlu := List.idxOf_lt_length_of_mem hu
  have hlv := List.idxOf_lt_length_of_mem hv
  have hgu : xs[xs.idxOf u]? = some u :=
    List.getElem?_eq_some_iff.mpr ⟨hlu, List.getElem_idxOf hlu⟩
  have hgv : xs[xs.idxOf v]? = some v :=
    List.getElem?_eq_some_iff.mpr ⟨hlv, List.getElem_idxOf hlv⟩
  rw [h] at hgu
  exact Option.some.inj (hgu.symm.trans hgv)

def rankDrawing {events : List EndpointEvent} {n : Nat}
    (hn : events.Nodup) (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n))
    (hw : WellFormed (extractedEndpoints events) (List.range n))
    (order : List Nat) (hp : order.Perm (List.range n)) : Drawing (eventPairing hn hi ho) where
  depth := fun v => order.idxOf v.val + 1
  positive := fun _ => by omega
  injective := by
    intro u v he
    apply Fin.ext
    apply idxOf_injective_mem
      (hp.mem_iff.mpr (List.mem_range.mpr u.isLt))
      (hp.mem_iff.mpr (List.mem_range.mpr v.isLt))
    omega
  proper := fun v => hw.proper v.val (List.mem_range.mpr v.isLt)

theorem idxOf_lt_split {order pre post : List Nat} {v u : Nat}
    (hn : order.Nodup) (hs : order = pre ++ v :: post) :
    order.idxOf u < order.idxOf v ↔ u ∈ pre := by
  subst order
  have hv : v ∉ pre := by
    have hdis := (List.nodup_append.mp hn).2.2
    exact fun hv => hdis v hv v (by simp) rfl
  have hvidx : (pre ++ v :: post).idxOf v = pre.length := by
    simp only [List.idxOf_append, ite_eq_right hv, List.idxOf_cons_self, Nat.zero_add]
  rw [hvidx, List.idxOf_append]
  by_cases hu : u ∈ pre
  · simp [hu, List.idxOf_lt_length_of_mem hu]
  · simp [hu]

/-- This finite list counts precisely the transverse crossings on one stem. -/
def stemCrossings {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : List (Fin tokens) :=
  (List.finRange tokens).filter (fun v => decide (Crosses D e v))

@[simp] theorem mem_stemCrossings {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) :
    v ∈ stemCrossings D e ↔ Crosses D e v := by simp [stemCrossings]

theorem stemCrossings_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : (stemCrossings D e).Nodup :=
  (List.nodup_finRange _).filter _

theorem rank_stem_le_endpointCount {events : List EndpointEvent} {n : Nat}
    (hn : events.Nodup) (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n))
    (hw : WellFormed (extractedEndpoints events) (List.range n))
    (order : List Nat) (hp : order.Perm (List.range n))
    (e : Fin events.length) (pre post : List Nat)
    (hs : order = pre ++ (eventOwner hi ho e).val :: post) :
    (stemCrossings (rankDrawing hn hi ho hw order hp) e).length ≤
      endpointCount (extractedEndpoints events) pre e.val := by
  let D := rankDrawing hn hi ho hw order hp
  have hnodup : ((stemCrossings D e).map Fin.val).Nodup :=
    (stemCrossings_nodup D e).map Fin.val (fun u v h he => h (Fin.ext he))
  have hsub : (stemCrossings D e).map Fin.val ⊆
      pre.filter (fun v => decide (Covers (extractedEndpoints events) v e.val)) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have hc := (mem_stemCrossings D e u).mp hu
    have hidx : order.idxOf u.val < order.idxOf (eventOwner hi ho e).val := by
      have hh := hc.2.2
      change order.idxOf u.val + 1 < order.idxOf (eventOwner hi ho e).val + 1 at hh
      omega
    have hupre := (idxOf_lt_split (hp.nodup_iff.mpr List.nodup_range) hs).mp hidx
    apply List.mem_filter.mpr
    refine ⟨hupre, ?_⟩
    apply decide_eq_true
    exact ⟨hc.1, hc.2.1⟩
  have hlen := hnodup.length_le_of_subset hsub
  simpa [endpointCount, List.countP_eq_length_filter] using hlen

theorem rank_stem_bounds {events : List EndpointEvent} {n r s : Nat}
    (hn : events.Nodup) (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n))
    (hw : WellFormed (extractedEndpoints events) (List.range n))
    (order : List Nat) (hp : order.Perm (List.range n))
    (hf : FeasibleEndpointOrder (extractedEndpoints events) r s order)
    (v : Fin n) :
    (stemCrossings (rankDrawing hn hi ho hw order hp) (eventLeft hi v)).length < r ∧
    (stemCrossings (rankDrawing hn hi ho hw order hp) (eventRight ho v)).length < s := by
  have hv : v.val ∈ order := hp.mem_iff.mpr (List.mem_range.mpr v.isLt)
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hv
  have he := (feasibleOrder_iff_prefixes _ _ _ _).mp hf pre v.val post hs
  have hleft : eventOwner hi ho (eventLeft hi v) = v := (eventPairing hn hi ho).owner_left v
  have hright : eventOwner hi ho (eventRight ho v) = v := (eventPairing hn hi ho).owner_right v
  have hl := rank_stem_le_endpointCount hn hi ho hw order hp (eventLeft hi v) pre post
    (by simpa only [hleft] using hs)
  have hr := rank_stem_le_endpointCount hn hi ho hw order hp (eventRight ho v) pre post
    (by simpa only [hright] using hs)
  exact ⟨Nat.lt_of_le_of_lt hl he.1, Nat.lt_of_le_of_lt hr he.2⟩

end StackSorting.GraphWidth.UCurve
