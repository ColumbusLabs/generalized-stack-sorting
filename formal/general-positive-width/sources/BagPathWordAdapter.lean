import HypergraphBagPath
import PathWordConstruction

namespace StackSorting.LowPathwidthParts

/-- Finite index interval convexity implies the literal list-cut convention
used by the accepted pathwidth-guidance endpoint. -/
theorem convex_of_index_interval {V : Type} (bs : List (Finset V))
    (h : ∀ (i j k : Nat) (hk : k < bs.length) (hij : i ≤ j) (hjk : j ≤ k),
      ∀ v, v ∈ bs[i]'(by omega) → v ∈ bs[k] → v ∈ bs[j]'(by omega)) : BiInterface.PathWord.Convex bs := by
  intro before middle after he v hb ha
  obtain ⟨B,hB,hvB⟩ := hb
  obtain ⟨C,hC,hvC⟩ := ha
  obtain ⟨i,hi,hiB⟩ := List.getElem_of_mem hB
  obtain ⟨k,hk,hkC⟩ := List.getElem_of_mem hC
  subst bs
  have htotal : before.length + 1 + k < (before ++ middle :: after).length := by
    simp only [List.length_append,List.length_cons]
    omega
  have hleft : v ∈ (before ++ middle :: after)[i]'(by
      simp only [List.length_append,List.length_cons]; omega) := by
    simpa only [List.getElem_append_left hi,hiB] using hvB
  have hright : v ∈ (before ++ middle :: after)[before.length + 1 + k] := by
    rw [List.getElem_append_right (by omega)]
    simpa only [show before.length + 1 + k - before.length = k+1 by omega,
      List.getElem_cons_succ, hkC] using hvC
  have hm := h i before.length (before.length+1+k) htotal (by omega) (by omega) v hleft hright
  simpa [List.getElem_append_right] using hm

/-- A full finite BagPath is converted to actual ordered bags, with coverage
and interval proofs preserved. Graph-edge coverage is supplied literally as a
common-bag fact, suitable for both original and completed marginal edges. -/
noncomputable def bagPathToPathWord {V : Type} [Fintype V] [DecidableEq V]
    {b : Nat} (D : FiniteFlow.Hypergraph.BagPath (Finset.univ : Finset V) b)
    (G : BiInterface.PathWord.Original V)
    (edge : ∀ {u v}, G.Adj u v → ∃ i, i ≤ D.last ∧ u ∈ D.bag i ∧ v ∈ D.bag i) :
    BiInterface.PathWord.Decomposition G b where
  bags := List.ofFn (fun i : Fin (D.last+1) => D.bag i.val)
  bound := by
    intro B hB
    obtain ⟨i,hi,hBi⟩ := List.getElem_of_mem hB
    have hi' : i ≤ D.last := by
      have : i < D.last+1 := by simpa only [List.length_ofFn] using hi
      omega
    have he : D.bag i = B := by simpa only [List.getElem_ofFn] using hBi
    exact he ▸ D.bounded i hi'
  vertex := by
    intro v
    obtain ⟨i,hi,hv⟩ := D.vertex v (Finset.mem_univ v)
    refine ⟨D.bag i,?_,hv⟩
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp only [List.length_ofFn]; omega,by simp only [List.getElem_ofFn]⟩
  edge := by
    intro u v huv
    obtain ⟨i,hi,hu,hv⟩ := edge huv
    refine ⟨D.bag i,?_,hu,hv⟩
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp only [List.length_ofFn]; omega,by simp only [List.getElem_ofFn]⟩
  interval := by
    apply convex_of_index_interval
    intro i j k hk hij hjk v hi hv
    have hk' : k ≤ D.last := by
      have : k < D.last+1 := by simpa only [List.length_ofFn] using hk
      omega
    simp only [List.getElem_ofFn] at hi hv ⊢
    exact D.interval i j k hij hjk hk' v hi hv

end StackSorting.LowPathwidthParts
