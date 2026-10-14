import CanonicalComponentHomes
import RadiusOneBagAssembly
import BagPathRestriction

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop} {s t : V}

noncomputable def oneBoundaryVertices (p : Path inc s t) (i : Fin (boundaryTrace p).length) : Finset V := by
  classical
  exact Finset.univ.filter (OneBoundaryRegion (inc := inc) (s := s) (t := t) ((boundaryTrace p).get i))

noncomputable def bridgeVertices (p : Path inc s t) (i j : Fin (boundaryTrace p).length) : Finset V := by
  classical
  exact Finset.univ.filter (BridgeRegion (inc := inc) (s := s) (t := t)
    ((boundaryTrace p).get i) ((boundaryTrace p).get j))

noncomputable def boundaryVertices (p : Path inc s t) (i : Fin (boundaryTrace p).length) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => BoundaryIncidence (inc := inc) (s := s) (t := t) x ((boundaryTrace p).get i))

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_oneBoundaryVertices (p : Path inc s t) (i : Fin (boundaryTrace p).length) (x : V) :
    x ∈ oneBoundaryVertices p i ↔ OneBoundaryRegion (inc := inc) (s := s) (t := t) ((boundaryTrace p).get i) x := by
  classical
  simp [oneBoundaryVertices]

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_bridgeVertices (p : Path inc s t) (i j : Fin (boundaryTrace p).length) (x : V) :
    x ∈ bridgeVertices p i j ↔ BridgeRegion (inc := inc) (s := s) (t := t)
      ((boundaryTrace p).get i) ((boundaryTrace p).get j) x := by
  classical
  simp [bridgeVertices]

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_boundaryVertices (p : Path inc s t) (i : Fin (boundaryTrace p).length) (x : V) :
    x ∈ boundaryVertices p i ↔ BoundaryIncidence (inc := inc) (s := s) (t := t) x ((boundaryTrace p).get i) := by
  classical
  simp [boundaryVertices]

/-- Local thinness certificates on the actual component unions. The source and
sink one-boundary regions are empty; a separate constructor can supply their
trivial certificates. No global decomposition is a field. -/
structure ThinBagCertificates (p : Path inc s t) (k : Nat) where
  appendix : ∀ i, BagPath (oneBoundaryVertices p i) (k+1)
  appendix_cover : ∀ i, (appendix i).Covers inc
  bridge : ∀ i j : Fin (boundaryTrace p).length, i.val+1=j.val →
    BagPath (bridgeVertices p i j) (2*k+2)
  bridge_cover : ∀ i j h, (bridge i j h).Covers inc
  bridge_first : ∀ i j h x, x ∈ bridgeVertices p i j → x ∈ boundaryVertices p i →
    x ∈ (bridge i j h).bag 0
  bridge_last : ∀ i j h x, x ∈ bridgeVertices p i j → x ∈ boundaryVertices p j →
    x ∈ (bridge i j h).bag (bridge i j h).last

omit [DecidableEq E] in
theorem networkExtra_even_eq (p : Path inc s t)
    (h : Fin (2*(boundaryTrace p).length-1)) (i : Fin (boundaryTrace p).length)
    (hi : h.val=2*i.val) : networkExtra p h = boundaryVertices p i := by
  ext x
  rw [mem_networkExtra,mem_boundaryVertices]
  constructor
  · rintro ⟨j,hj,hx⟩
    have heq : j = i := Fin.ext (by omega)
    exact heq ▸ hx
  · exact fun hx => ⟨i,hi,hx⟩

omit [DecidableEq E] in
theorem networkExtra_odd_empty (p : Path inc s t)
    (h : Fin (2*(boundaryTrace p).length-1)) (i : Nat) (hi : h.val=2*i+1) :
    networkExtra p h = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨j,hj,_⟩ := (mem_networkExtra p h x).mp hx
  omega

omit [DecidableEq V] in
theorem networkHome_even_region
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t)
    (x : V) (i : Fin (boundaryTrace p).length)
    (hi : (networkHome connected p x).val=2*i.val) : x ∈ oneBoundaryVertices p i := by
  apply (mem_oneBoundaryVertices p i x).mpr
  rcases networkHome_descriptor connected p x with ⟨j,hj,hr⟩ | ⟨j,k,hstep,hj,hr⟩
  · have heq : j = i := Fin.ext (by omega)
    exact heq ▸ hr
  · omega

omit [DecidableEq V] in
theorem networkHome_odd_region
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t)
    (x : V) (i j : Fin (boundaryTrace p).length) (hstep : i.val+1=j.val)
    (hi : (networkHome connected p x).val=2*i.val+1) : x ∈ bridgeVertices p i j := by
  apply (mem_bridgeVertices p i j x).mpr
  rcases networkHome_descriptor connected p x with ⟨a,ha,hr⟩ | ⟨a,b,hab,ha,hr⟩
  · omega
  · have hea : a = i := Fin.ext (by omega)
    have heb : b = j := Fin.ext (by omega)
    simpa only [hea,heb] using hr

noncomputable def hyperedgeVertices (inc : V → E → Prop) (e : E) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => inc x e)

/- Rank on actual cutedge incidence sets implies the separator rank used by
the bag surgery; terminal separators are singleton sets. -/
omit [DecidableEq V] [DecidableEq E] in
theorem boundaryVertices_rank (p : Path inc s t) (k : Nat)
    (rank : ∀ e, Cutedge inc s t e →
      (hyperedgeVertices inc e).card ≤ k+1)
    (i : Fin (boundaryTrace p).length) : (boundaryVertices p i).card ≤ k+1 := by
  classical
  have hv := (mem_boundaryTrace p _).mp (List.get_mem _ i)
  cases hb : (boundaryTrace p).get i with
  | source =>
    have hsub : boundaryVertices p i ⊆ {s} := by
      intro x hx
      have heq := (mem_boundaryVertices p i x).mp hx
      simpa only [hb,BoundaryIncidence,Finset.mem_singleton] using heq
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  | sink =>
    have hsub : boundaryVertices p i ⊆ {t} := by
      intro x hx
      have heq := (mem_boundaryVertices p i x).mp hx
      simpa only [hb,BoundaryIncidence,Finset.mem_singleton] using heq
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  | cut e =>
    have he : Cutedge inc s t e := by simpa only [hb,BoundaryValid] using hv
    have heq : boundaryVertices p i = Finset.univ.filter (fun x => inc x e) := by
      ext x
      simp only [mem_boundaryVertices,hb,BoundaryIncidence,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [heq]
    simpa only [hyperedgeVertices] using rank e he

end FiniteFlow.Hypergraph
