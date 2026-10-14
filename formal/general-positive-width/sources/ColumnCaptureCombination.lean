import ColumnGeometry
import GuidanceAddition

namespace StackSorting.GuidedPathwidth
variable {V : Type} {G : SimpleGraph V} {I : Set V} {n c b : Nat}

theorem componentFiber_of_reach {K : (G.induce I).ConnectedComponent} {x y : V}
    (h : ReachIn G I x y) (hy : y ∈ componentFiber G I K) :
    x ∈ componentFiber G I K := by
  obtain ⟨hy,hK⟩ := hy
  have he : (G.induce I).connectedComponentMk ⟨x,h.1⟩ =
      (G.induce I).connectedComponentMk ⟨y,hy⟩ :=
    SimpleGraph.ConnectedComponent.sound h.induced
  exact ⟨h.1,he.trans hK⟩

namespace ColumnGeometry
variable (C : ColumnGeometry G n) (R : System G Set.univ b)

/-- Routing is an explicit finite-walk property of the already constructed
regional guides. The idempotent-column palette supplies this property. -/
def Routes : Prop := ∀ (j : Fin n) (x : V), x ∈ C.part j →
  ∀ r ∈ C.boundary j, ReachIn G Set.univ x r → ∃ i, x ∈ (R i).support r

/-- Append the regional colors to the unchanged interior guides. -/
noncomputable def combinedGuides (A : System G C.inside c) : System G Set.univ (c+b) :=
  System.append (fun i => (A i).enlarge (Set.subset_univ _)) R

theorem captures_augmented (hR : C.Routes R) (A : System G C.inside c)
    (K : (G.induce C.inside).ConnectedComponent) (B : Set V)
    (hB : B ⊆ componentFiber G C.inside K) (hcap : Captures G A B) :
    Captures G (C.combinedGuides R A) (B ∪ C.neighbors K) := by
  classical
  have witness : ∃ x, x ∈ componentFiber G C.inside K ∧
      ∀ r ∈ B, ∃ i, x ∈ (A i).support r := by
    by_cases hb : B.Nonempty
    · obtain ⟨r,hr⟩ := hb
      obtain ⟨x,hx⟩ := hcap ⟨r,hr⟩
      obtain ⟨i,hi⟩ := hx r hr
      have hxr := ((A i).reaches r x hi).mono ((A i).inside r)
      exact ⟨x,componentFiber_of_reach hxr (hB hr),hx⟩
    · refine ⟨K.out.val,⟨K.out.property,K.out_eq⟩,?_⟩
      intro r hr
      exact (hb ⟨r,hr⟩).elim
  obtain ⟨x,hx,hroute⟩ := witness
  intro _
  refine ⟨x,?_⟩
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨i,hi⟩ := hroute r hr
    refine ⟨finSumFinEquiv (.inl i),?_⟩
    simpa only [combinedGuides,System.append_left,Color.enlarge] using hi
  · have hrb := C.neighbors_boundary K hr
    obtain ⟨_,y,hy,hyr⟩ := hr
    have hxy := (componentFiber_connected K hx hy).mono (Set.subset_univ _)
    have hxr : ReachIn G Set.univ x r :=
      hxy.trans ⟨trivial,trivial,.edge hyr⟩
    obtain ⟨i,hi⟩ := hR (C.componentLocation K) x (C.component_subset K hx).1 r hrb hxr
    refine ⟨finSumFinEquiv (.inr i),?_⟩
    simpa only [combinedGuides,System.append_right] using hi

theorem captures_boundary_component (hR : C.Routes R) (A : System G C.inside c)
    (j : Fin n) (K : (G.induce Set.univ).ConnectedComponent) :
    Captures G (C.combinedGuides R A) (C.boundary j ∩ componentFiber G Set.univ K) := by
  intro hb
  obtain ⟨x,hx,hxK⟩ := hb
  refine ⟨x,?_⟩
  rintro r ⟨hr,hrK⟩
  obtain ⟨i,hi⟩ := hR j x (C.boundaryInside j hx) r hr (componentFiber_connected K hxK hrK)
  refine ⟨finSumFinEquiv (.inr i),?_⟩
  simpa only [combinedGuides,System.append_right] using hi

/-- Construct the captured global decomposition from the actual interior
one and the explicit regional root routes. It performs the forest graft and
then actual global-component splitting, with palette c+b. -/
theorem exists_guided_graft [Finite V] (hR : C.Routes R)
    (D : GuidedDecomposition G C.inside c) :
    Nonempty (GuidedDecomposition G Set.univ (c+b)) := by
  let B := C.graftData D.decomposition
  let E := B.decomposition (pathGraph_acyclic n)
  let E' := E.restrictComponents (Set.Subset.refl Set.univ)
  refine ⟨⟨E',C.combinedGuides R D.guides,?_⟩⟩
  rintro ⟨K,a⟩
  cases a with
  | inl j => exact C.captures_boundary_component R hR D.guides j K
  | inr a =>
    apply captures_mono (C.combinedGuides R D.guides)
      (C.captures_augmented R hR D.guides a.1
        (D.decomposition.bag a.2 ∩ componentFiber G C.inside a.1)
        Set.inter_subset_right (captures_mono D.guides (D.captured a.2) Set.inter_subset_left))
    exact Set.inter_subset_left
end ColumnGeometry

#print axioms ColumnGeometry.exists_guided_graft
end StackSorting.GuidedPathwidth
