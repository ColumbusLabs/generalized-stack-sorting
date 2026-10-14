import CutedgeRegionLocalization
import Mathlib.Data.Quot
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic

namespace FiniteFlow.Hypergraph
variable {V E : Type*} {inc : V → E → Prop} {s t : V}

def BoundaryIncidence (x : V) : CutBoundary E → Prop
  | .source => x = s
  | .cut e => inc x e
  | .sink => x = t

def OneBoundaryRegion (b : CutBoundary E) (x : V) : Prop :=
  ∀ c, BoundaryValid (inc := inc) (s := s) (t := t) c →
    (ComponentTouches (inc := inc) (s := s) (t := t) x c ↔ c = b)

theorem boundary_incidence_touches (x : V) (b : CutBoundary E)
    (h : BoundaryIncidence (inc := inc) (s := s) (t := t) x b) :
    ComponentTouches (inc := inc) (s := s) (t := t) x b := by
  cases b with
  | source => exact h ▸ sameCutedgeComponent_refl inc s t x
  | sink => exact h ▸ sameCutedgeComponent_refl inc s t x
  | cut e => exact ⟨x,h,sameCutedgeComponent_refl inc s t x⟩

theorem boundaryTrace_length_ge_two (p : Path inc s t) : 2 ≤ (boundaryTrace p).length := by
  simp only [boundaryTrace,List.length_cons,List.length_append,List.length_map]
  omega

/-- A core position is even for an appendix and odd for a bridge. Boundary
separator positions are even; a bridge sits between its two separators. -/
def HomeDescriptor (p : Path inc s t) (x : V) (h : Nat) : Prop :=
  (∃ i : Fin (boundaryTrace p).length, h = 2*i.val ∧
    OneBoundaryRegion (inc := inc) (s := s) (t := t) ((boundaryTrace p).get i) x) ∨
  (∃ i j : Fin (boundaryTrace p).length, i.val+1=j.val ∧ h=2*i.val+1 ∧
    BridgeRegion (inc := inc) (s := s) (t := t)
      ((boundaryTrace p).get i) ((boundaryTrace p).get j) x)

theorem homeDescriptor_exists [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    ∃ h, HomeDescriptor p x h := by
  rcases indexed_cutedge_component_classification connected p x with ha | hb
  · obtain ⟨e,he,hregion⟩ := ha
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p (.cut e)).mpr he)
    refine ⟨2*i.val,Or.inl ⟨i,rfl,?_⟩⟩
    simpa only [OneBoundaryRegion,hi] using hregion
  · obtain ⟨i,j,hstep,hregion⟩ := hb
    exact ⟨2*i.val+1,Or.inr ⟨i,j,hstep,rfl,hregion⟩⟩

theorem homeDescriptor_bound (p : Path inc s t) {x : V} {h : Nat}
    (hh : HomeDescriptor p x h) : h < 2*(boundaryTrace p).length-1 := by
  rcases hh with ⟨i,hh,_⟩ | ⟨i,j,hstep,hh,_⟩
  · have := i.isLt
    omega
  · have := j.isLt
    omega

theorem homeDescriptor_congr (p : Path inc s t) {x y : V}
    (hxy : SameCutedgeComponent inc s t x y) {h : Nat}
    (hh : HomeDescriptor p x h) : HomeDescriptor p y h := by
  rcases hh with ⟨i,hh,hr⟩ | ⟨i,j,hstep,hh,hr⟩
  · refine Or.inl ⟨i,hh,?_⟩
    intro b hb
    exact (componentTouches_congr hxy b).symm.trans (hr b hb)
  · refine Or.inr ⟨i,j,hstep,hh,?_⟩
    intro b hb
    exact (componentTouches_congr hxy b).symm.trans (hr b hb)

noncomputable def componentRepresentative (inc : V → E → Prop) (s t x : V) : V :=
  Quotient.out (Quotient.mk (cutedgeComponentSetoid inc s t) x)

theorem componentRepresentative_same (x : V) :
    SameCutedgeComponent inc s t (componentRepresentative inc s t x) x :=
  by
    change (cutedgeComponentSetoid inc s t).r _ _
    exact Quotient.exact (Quotient.out_eq (Quotient.mk (cutedgeComponentSetoid inc s t) x))

theorem componentRepresentative_eq {x y : V} (h : SameCutedgeComponent inc s t x y) :
    componentRepresentative inc s t x = componentRepresentative inc s t y :=
  congrArg Quotient.out (Quotient.sound h)

/-- Choice is made once per actual cutedge component, so every noncutedge has
one core home. This does not assume uniqueness of classification witnesses. -/
noncomputable def componentHomeChoice [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    Fin (2*(boundaryTrace p).length-1) :=
  let h := homeDescriptor_exists connected p x
  ⟨Classical.choose h,homeDescriptor_bound p (Classical.choose_spec h)⟩

noncomputable def networkHome [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    Fin (2*(boundaryTrace p).length-1) :=
  componentHomeChoice connected p (componentRepresentative inc s t x)

theorem networkHome_descriptor [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    HomeDescriptor p x (networkHome connected p x).val :=
  homeDescriptor_congr p (componentRepresentative_same x)
    (Classical.choose_spec (homeDescriptor_exists connected p (componentRepresentative inc s t x)))

theorem networkHome_sameComponent [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t)
    {x y : V} (h : SameCutedgeComponent inc s t x y) :
    networkHome connected p x = networkHome connected p y := by
  exact congrArg (componentHomeChoice connected p) (componentRepresentative_eq h)

noncomputable def networkExtra [Fintype V] [DecidableEq V]
    (p : Path inc s t) (h : Fin (2*(boundaryTrace p).length-1)) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i : Fin (boundaryTrace p).length,
    h.val=2*i.val ∧ BoundaryIncidence (inc := inc) (s := s) (t := t) x ((boundaryTrace p).get i))

@[simp] theorem mem_networkExtra [Fintype V] [DecidableEq V]
    (p : Path inc s t) (h : Fin (2*(boundaryTrace p).length-1)) (x : V) :
    x ∈ networkExtra p h ↔ ∃ i : Fin (boundaryTrace p).length,
      h.val=2*i.val ∧ BoundaryIncidence (inc := inc) (s := s) (t := t) x ((boundaryTrace p).get i) := by
  classical
  simp [networkExtra]

/-- Actual separator incidence is confined to the home position or its immediate
neighbors. This is derived from the accepted component classification. -/
theorem networkExtra_radius [Fintype V] [DecidableEq V] [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t)
    (h : Fin (2*(boundaryTrace p).length-1)) (x : V) (hx : x ∈ networkExtra p h) :
    (networkHome connected p x).val ≤ h.val+1 ∧ h.val ≤ (networkHome connected p x).val+1 := by
  obtain ⟨i,hi,hxi⟩ := (mem_networkExtra p h x).mp hx
  have hv := (mem_boundaryTrace p _).mp (List.get_mem _ i)
  have ht := boundary_incidence_touches x _ hxi
  rcases networkHome_descriptor connected p x with ⟨j,hhome,hr⟩ | ⟨j,k,hstep,hhome,hr⟩
  · have hij := (boundaryTrace_nodup p).injective_get ((hr _ hv).mp ht)
    have hi' := congrArg Fin.val hij
    omega
  · rcases (hr _ hv).mp ht with hij | hik
    · have hi' := congrArg Fin.val ((boundaryTrace_nodup p).injective_get hij)
      omega
    · have hi' := congrArg Fin.val ((boundaryTrace_nodup p).injective_get hik)
      omega

/-- Each cutedge is wholly inside its separator piece, while every noncutedge
has a constant component home. This is the full-edge localization dichotomy. -/
theorem networkHome_edge_cases [Fintype V] [DecidableEq V] [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (e : E) :
    (∃ h, ∀ x, inc x e → x ∈ networkExtra p h) ∨
      (∀ x y, inc x e → inc y e → networkHome connected p x = networkHome connected p y) := by
  classical
  by_cases he : Cutedge inc s t e
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p (.cut e)).mpr he)
    have hbound : 2*i.val < 2*(boundaryTrace p).length-1 := by have := i.isLt; omega
    refine Or.inl ⟨⟨2*i.val,hbound⟩,?_⟩
    intro x hx
    apply (mem_networkExtra p _ x).mpr
    exact ⟨i,rfl,by simpa only [hi,BoundaryIncidence] using hx⟩
  · exact Or.inr (fun x y hx hy => networkHome_sameComponent connected p
      (sameCutedgeComponent_of_noncut_edge inc s t hx hy he))

end FiniteFlow.Hypergraph
