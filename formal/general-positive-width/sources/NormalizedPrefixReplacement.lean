import ActiveReplacementPresentation
import NormalizedPrefixIncidence

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}

/-- The actual frontier adhesion is removed, and the actual newly exposed bag
is inserted. All frame obligations come from prefix geometry and local walks. -/
noncomputable def prefixReplacementFrame (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (s t : Fin n) (hs : s ∈ prefixVertices G O r Z) (ht : t ∈ prefixVertices G O r Z)
    (removed : ActiveEdge (PrefixHypertorsoInc G O r Z)) (hremoved : removed.val = .inr z)
    (hcut : Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t removed) :
    ReplacementFrame (ActiveIncidence (PrefixHypertorsoInc G O r Z))
      (ActiveIncidence (LocalHypertorsoInc G O z)) s t removed := by
  classical
  let anchor := Classical.choose removed.property
  have ha := Classical.choose_spec removed.property
  have removed_bag : ∀ x, ActiveIncidence (PrefixHypertorsoInc G O r Z) x removed →
      x ∈ regionBagSet G O z := by
    intro x hx
    change PrefixHypertorsoInc G O r Z x removed.val at hx
    rw [hremoved] at hx
    exact (mem_regionBagSet G O z x).mpr hx.2.2.1
  refine ⟨↑(prefixVertices G O r Z),↑(regionBagSet G O z),anchor,ha,?_,?_,?_,hs,ht,hcut,?_⟩
  · intro x e hx
    exact prefixHypertorso_support G O r Z hp x e.val hx
  · intro x e hx
    exact localHypertorso_support G O z x e.val hx
  · intro x hx hy
    have had : x ∈ regionAdhesionSet G O z := by
      rw [← frontier_overlap G O r Z hp z hz]
      exact Finset.mem_inter.mpr ⟨hx,hy⟩
    change PrefixHypertorsoInc G O r Z x removed.val
    rw [hremoved]
    exact ⟨hz,(mem_regionAdhesionSet G O z x).mp had⟩
  · intro a b ha hb
    obtain ⟨w⟩ := localHypertorso_connected G O helim cones z a b (removed_bag a ha) (removed_bag b hb)
    exact ⟨w.activate⟩

noncomputable def prefixReplacementEquiv (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (removed : ActiveEdge (PrefixHypertorsoInc G O r Z)) (hremoved : removed.val = .inr z) :
    IncidenceEquiv
      (ReplacementIncidence (ActiveIncidence (PrefixHypertorsoInc G O r Z))
        (ActiveIncidence (LocalHypertorsoInc G O z)) removed)
      (ActiveIncidence (PrefixHypertorsoInc G O r (insert z Z))) := by
  apply activeReplacementEquiv
  · intro x e
    simpa only [hremoved] using prefix_incidence_step G O helim r Z hp z hz x e
  · intro x y e hold hnew
    exact old_local_identifiers_disjoint G O r Z hp z hz e x y hold hnew

/-- A concrete frontier cutedge can be expanded while retaining local thinness.
No output path or thinness oracle is assumed. -/
theorem prefix_expansion_preserves_thinness (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (s t : Fin n) (hs : s ∈ prefixVertices G O r Z) (ht : t ∈ prefixVertices G O r Z)
    (connected : ∀ x ∈ prefixVertices G O r Z,
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r Z)) x s))
    (removed : ActiveEdge (PrefixHypertorsoInc G O r Z)) (hremoved : removed.val = .inr z)
    (hcut : Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t removed)
    (p : Path (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t)
    (T : ThinNetworkLocalWitnesses p k) :
    ∃ q : Path (ActiveIncidence (PrefixHypertorsoInc G O r (insert z Z))) s t,
      ThinNetworkLocalWitnesses q k := by
  classical
  let R := prefixReplacementFrame G O helim cones r Z hp z hz s t hs ht removed hremoved hcut
  have removed_bag : ∀ x, ActiveIncidence (PrefixHypertorsoInc G O r Z) x removed →
      x ∈ R.newVertices := by
    intro x hx
    change PrefixHypertorsoInc G O r Z x removed.val at hx
    rw [hremoved] at hx
    exact (mem_regionBagSet G O z x).mpr hx.2.2.1
  have new_connected : ∀ x ∈ R.newVertices,
      Nonempty (HWalk (ActiveIncidence (LocalHypertorsoInc G O z)) x R.anchor) := by
    intro x hx
    obtain ⟨w⟩ := localHypertorso_connected G O helim cones z x R.anchor hx
      (removed_bag R.anchor R.anchor_incident)
    exact ⟨w.activate⟩
  obtain ⟨q,_⟩ := (liftReplacement removed R.inserted_connects p.walk).exists_path
  have hq := R.replacement_preserves_supported_local_thinness p k T
    (regionBagSet G O z) (width z) (fun _ => Iff.rfl) connected new_connected removed_bag q
  let Q := prefixReplacementEquiv G O helim r Z hp z hz removed hremoved
  exact ⟨Q.mapPath q,Q.local_thinness_transport q (Q.mapPath q) k hq⟩

/-- Connectivity is maintained on the exact growing prefix support. -/
theorem prefix_expansion_connected (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (s t : Fin n) (hs : s ∈ prefixVertices G O r Z) (ht : t ∈ prefixVertices G O r Z)
    (connected : ∀ x ∈ prefixVertices G O r Z,
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r Z)) x s))
    (removed : ActiveEdge (PrefixHypertorsoInc G O r Z)) (hremoved : removed.val = .inr z)
    (hcut : Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t removed) :
    ∀ x ∈ prefixVertices G O r (insert z Z),
      Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r (insert z Z))) x s) := by
  classical
  let R := prefixReplacementFrame G O helim cones r Z hp z hz s t hs ht removed hremoved hcut
  let Q := prefixReplacementEquiv G O helim r Z hp z hz removed hremoved
  have ha : R.anchor ∈ regionBagSet G O z := by
    have h := R.anchor_incident
    change PrefixHypertorsoInc G O r Z R.anchor removed.val at h
    rw [hremoved] at h
    exact (mem_regionBagSet G O z R.anchor).mpr h.2.2.1
  intro x hx
  rw [frontier_visible_union G O r Z hp z hz] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨w⟩ := connected x hx
    exact ⟨Q.mapWalk (liftReplacement removed R.inserted_connects w)⟩
  · obtain ⟨w⟩ := localHypertorso_connected G O helim cones z x R.anchor hx ha
    obtain ⟨v⟩ := connected R.anchor (R.old_support R.anchor removed R.anchor_incident)
    let w' := w.activate.mapEdges (inc := ActiveIncidence (LocalHypertorsoInc G O z))
      (inc' := ReplacementIncidence (ActiveIncidence (PrefixHypertorsoInc G O r Z))
        (ActiveIncidence (LocalHypertorsoInc G O z)) removed) Sum.inr (fun _ _ h => h)
    exact ⟨Q.mapWalk (w'.append (liftReplacement removed R.inserted_connects v))⟩

end StackSorting.PrefixGrowth
