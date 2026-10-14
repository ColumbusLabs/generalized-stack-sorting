import PrunedPrefixSeparation
import Mathlib.Data.Finset.Max

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- Connectivity under an arbitrary legitimate prefix expansion needs no
cutedge premise; local cone connectivity supplies the inserted walks. -/
theorem expand_prefix_connected (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (connected : ∀ x ∈ prefixVertices G O r Z,
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r Z)) x r)) :
    ∀ x ∈ prefixVertices G O r (insert z Z),
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r (insert z Z))) x r) := by
  classical
  have hzdata := relative_frontier_cone O r Z hp z hz
  have had : RegionAdhesion G O z (O.parent z) :=
    ⟨hzdata.2.2,connected_parent_in_bag G O helim cones hzdata.2.2,Or.inl rfl⟩
  let e : ActiveEdge (PrefixHypertorsoInc G O r Z) := ⟨.inr z,⟨O.parent z,hz,had⟩⟩
  have incident : ActiveIncidence (PrefixHypertorsoInc G O r Z) (O.parent z) e := ⟨hz,had⟩
  have inbag : ∀ x, ActiveIncidence (PrefixHypertorsoInc G O r Z) x e → x ∈ regionBagSet G O z := by
    intro x hx
    exact (mem_regionBagSet G O z x).mpr hx.2.2.1
  have connects : ∀ a b, ActiveIncidence (PrefixHypertorsoInc G O r Z) a e →
      ActiveIncidence (PrefixHypertorsoInc G O r Z) b e →
      Nonempty (HWalk (ActiveIncidence (LocalHypertorsoInc G O z)) a b) := by
    intro a b ha hb
    obtain ⟨w⟩ := localHypertorso_connected G O helim cones z a b (inbag a ha) (inbag b hb)
    exact ⟨w.activate⟩
  let Q := prefixReplacementEquiv G O helim r Z hp z hz e rfl
  intro x hx
  rw [frontier_visible_union G O r Z hp z hz] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨w⟩ := connected x hx
    exact ⟨Q.mapWalk (liftReplacement e connects w)⟩
  · obtain ⟨w⟩ := localHypertorso_connected G O helim cones z x (O.parent z) hx (inbag _ incident)
    obtain ⟨v⟩ := connected (O.parent z) (prefixHypertorso_support G O r Z hp _ e.val incident)
    let w' := w.activate.mapEdges (inc := ActiveIncidence (LocalHypertorsoInc G O z))
      (inc' := ReplacementIncidence (ActiveIncidence (PrefixHypertorsoInc G O r Z))
        (ActiveIncidence (LocalHypertorsoInc G O z)) e) Sum.inr (fun _ _ h => h)
    exact ⟨Q.mapWalk (w'.append (liftReplacement e connects v))⟩

/-- A maximal-rank nonroot prefix node is a removable leaf. -/
theorem relative_prefix_erase_max (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : z ∈ Z) (hzr : z ≠ r)
    (hmax : ∀ x ∈ Z, O.rank x ≤ O.rank z) :
    RelativePrefix O r (Z.erase z) ∧ Frontier (clippedParent O r) (Z.erase z) z := by
  classical
  have hrz := (hp.2.2 z hz).resolve_right (Ne.symm hzr)
  have hpz := O.parent_ne_of_pred hrz
  have hcp : clippedParent O r z = O.parent z := by simp [clippedParent,hzr]
  have herase : RelativePrefix O r (Z.erase z) := by
    refine ⟨?_,Finset.mem_erase.mpr ⟨Ne.symm hzr,hp.2.1⟩,?_⟩
    · intro x hx
      obtain ⟨hxz,hx⟩ := Finset.mem_erase.mp hx
      refine Finset.mem_erase.mpr ⟨?_,hp.1 x hx⟩
      intro he
      by_cases hxr : x = r
      · have hcr : clippedParent O r x = r := by simp [clippedParent,hxr]
        exact hzr (he.symm.trans hcr)
      · have hpx : O.parent x = z := by simpa [clippedParent,hxr] using he
        have hpne : O.parent x ≠ x := fun h => hxz (h.symm.trans hpx)
        have hlt := O.parent_rank_lt hpne
        rw [hpx] at hlt
        exact (Nat.not_lt_of_ge (hmax x hx)) hlt
    · intro x hx
      exact hp.2.2 x (Finset.mem_of_mem_erase hx)
  refine ⟨herase,by simp,?_⟩
  rw [hcp]
  exact Finset.mem_erase.mpr ⟨hpz,by simpa [hcp] using hp.1 z hz⟩

/-- Every actual prefix hypertorso is connected on its exposed vertices. -/
theorem arbitrary_prefix_connected (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) :
    ∀ x ∈ prefixVertices G O r Z,
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r Z)) x r) := by
  classical
  by_cases hsingle : Z = {r}
  · subst Z
    intro x hx
    exact singleton_prefix_connected G O helim cones r x r hx (by
      rw [singleton_prefix_vertices]
      exact (mem_regionBagSet G O r r).mpr (Or.inl rfl))
  · obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image Z O.rank ⟨r,hp.2.1⟩
    have hzr : z ≠ r := by
      intro he
      apply hsingle
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hc := hp.2.2 x hx
        rcases hc with hc | hc
        · have hl := O.increasing hc
          have hm := hmax x hx
          rw [he] at hm
          omega
        · exact Finset.mem_singleton.mpr hc.symm
      · intro hx
        exact (Finset.mem_singleton.mp hx).symm ▸ hp.2.1
    obtain ⟨hp',hz'⟩ := relative_prefix_erase_max O r Z hp z hz hzr hmax
    have conn := arbitrary_prefix_connected G O helim cones r (Z.erase z) hp'
    have hconn := expand_prefix_connected G O helim cones r (Z.erase z) hp' z hz' conn
    exact Eq.mp (congrArg (fun W : Finset (Fin n) =>
      ∀ x ∈ prefixVertices G O r W,
        Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r W)) x r))
      (Finset.insert_erase hz)) hconn
termination_by Z.card
decreasing_by exact Finset.card_erase_lt_of_mem hz

end StackSorting.LowPathwidthParts
