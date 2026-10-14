import DecompositionBoundaryGraft
import OrderedSpineForest

namespace StackSorting.GuidedPathwidth
variable {V : Type} {G : SimpleGraph V} {n : Nat}

/-- Actual column sets with a named boundary. The hypotheses concern vertex
and edge incidence, never an output decomposition or capture relation. -/
structure ColumnGeometry (G : SimpleGraph V) (n : Nat) where
  part : Fin n → Set V
  boundary : Fin n → Set V
  boundaryInside : ∀ i, boundary i ⊆ part i
  vertexCovered : ∀ x, ∃ i, x ∈ part i
  edgeCovered : ∀ {x y}, G.Adj x y → ∃ i, x ∈ part i ∧ y ∈ part i
  interiorUnique : ∀ {i j x}, x ∈ part i \ boundary i → x ∈ part j → i = j
  overlapConsecutive : ∀ {i j x}, x ∈ part i → x ∈ part j →
    i.val ≤ j.val+1 ∧ j.val ≤ i.val+1

namespace ColumnGeometry
variable (C : ColumnGeometry G n)
def interior (i : Fin n) : Set V := C.part i \ C.boundary i
def inside : Set V := {x | ∃ i, x ∈ C.interior i}

namespace ReachInAux
theorem closed {I R : Set V} {x y : V} (h : ReachIn G I x y) (hx : x ∈ R)
    (hc : ∀ {a b}, a ∈ I → b ∈ I → a ∈ R → G.Adj a b → b ∈ R) : y ∈ R := by
  obtain ⟨p⟩ := h.induced
  suffices ∀ {a b : I} (q : (G.induce I).Walk a b), a.val ∈ R → b.val ∈ R by
    exact this p hx
  intro a b q
  induction q with
  | nil => exact id
  | @cons a b z hab q ih => exact fun ha => ih (hc a.property b.property ha hab)
end ReachInAux

theorem interior_closed {i : Fin n} {x y : V} (hx : x ∈ C.interior i)
    (hy : y ∈ C.inside) (hxy : G.Adj x y) : y ∈ C.interior i := by
  obtain ⟨j,hxj,hyj⟩ := C.edgeCovered hxy
  have hij : i = j := C.interiorUnique hx hxj
  obtain ⟨l,hyl⟩ := hy
  have hlj : l = j := C.interiorUnique hyl hyj
  exact (hlj.trans hij.symm) ▸ hyl

noncomputable def componentLocation (K : (G.induce C.inside).ConnectedComponent) : Fin n :=
  Classical.choose K.out.property

theorem component_anchor (K : (G.induce C.inside).ConnectedComponent) :
    K.out.val ∈ C.interior (C.componentLocation K) := Classical.choose_spec K.out.property

theorem component_subset (K : (G.induce C.inside).ConnectedComponent) :
    componentFiber G C.inside K ⊆ C.interior (C.componentLocation K) := by
  intro y hy
  have hx : K.out.val ∈ componentFiber G C.inside K := ⟨K.out.property,K.out_eq⟩
  exact ReachInAux.closed (componentFiber_connected K hx hy) (C.component_anchor K)
    (fun _ hb ha hab => C.interior_closed ha hb hab)

def neighbors (K : (G.induce C.inside).ConnectedComponent) : Set V :=
  {y | y ∉ C.inside ∧ ∃ x ∈ componentFiber G C.inside K, G.Adj x y}

theorem neighbors_boundary (K : (G.induce C.inside).ConnectedComponent) :
    C.neighbors K ⊆ C.boundary (C.componentLocation K) := by
  rintro y ⟨hy,x,hx,hxy⟩
  have hxj := C.component_subset K hx
  obtain ⟨i,hxi,hyi⟩ := C.edgeCovered hxy
  have hji := C.interiorUnique hxj hxi
  have hyp : y ∈ C.part (C.componentLocation K) := hji.symm ▸ hyi
  by_contra hnb
  exact hy ⟨C.componentLocation K,hyp,hnb⟩

theorem boundary_not_inside {i : Fin n} {x : V} (hx : x ∈ C.boundary i) : x ∉ C.inside := by
  rintro ⟨j,hj⟩
  have hji := C.interiorUnique hj (C.boundaryInside i hx)
  exact hj.2 (hji.symm ▸ hx)

theorem boundary_running (x : V) (i j : Fin n)
    (hi : x ∈ C.boundary i) (hj : x ∈ C.boundary j) :
    ReachIn (SimpleGraph.pathGraph n) {i | x ∈ C.boundary i} i j := by
  by_cases he : i = j
  · subst j
    exact ReachIn.refl hi
  · refine ⟨hi,hj,.edge ?_⟩
    apply SimpleGraph.pathGraph_adj.mpr
    have h := C.overlapConsecutive (C.boundaryInside i hi) (C.boundaryInside j hj)
    have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
    omega

/-- All boundary neighbors are appended componentwise to actual interior
bags. The resulting graft data satisfies coverage and running requirements. -/
noncomputable def graftData [Finite V] (D : Decomposition G C.inside) :
    BoundaryGraftData (P := Set.univ) (D.restrictComponents (Set.Subset.refl C.inside)) (SimpleGraph.pathGraph n) where
  core := C.boundary
  extra := fun a => C.neighbors a.1
  location := fun a => C.componentLocation a.1
  interiorInside := Set.subset_univ _
  coreInside := fun i x hx => ⟨trivial,C.boundary_not_inside hx⟩
  extraInside := fun a => C.neighbors_boundary a.1
  locationStable := fun h => congrArg C.componentLocation h.1
  extraStable := by intro a b h x hx; exact h.1 ▸ hx
  boundaryCovered := by
    intro x hx
    obtain ⟨i,hi⟩ := C.vertexCovered x
    refine ⟨i,?_⟩
    by_contra hn
    exact hx.2 ⟨i,hi,hn⟩
  crossCovered := by
    intro x y hx hy hxy a ha
    exact ⟨hy.2,x,ha.2,hxy⟩
  boundaryEdges := by
    intro x y hx hy hxy
    obtain ⟨i,hxi,hyi⟩ := C.edgeCovered hxy
    refine ⟨i,?_,?_⟩
    · by_contra hn; exact hx.2 ⟨i,hxi,hn⟩
    · by_contra hn; exact hy.2 ⟨i,hyi,hn⟩
  coreRunning := C.boundary_running
end ColumnGeometry

#print axioms ColumnGeometry.graftData
end StackSorting.GuidedPathwidth
