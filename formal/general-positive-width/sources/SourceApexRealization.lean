import RealizationApex
import StemBoundedSourceTree
import SourceRectangle
import TriRectangleDecomposition

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
open SubdivisionTree

/-- The existing explicit triangulation, with its original vertex numbering. -/
def actualGraph {w h} (hw : 0<w) (hh : 0<h) : Graph ((w+1)*(h+1)+1) :=
  incidenceGraph (incidenceMap hw hh) (numbered_loopless hw hh (finCode _))

def rectangleVertexCode (w h : Nat) :
    FiniteCode (Option (Fin (w+1) × Fin (h+1))) ((w+1)*(h+1)+1) :=
  optionCode (productCode (w+1) (h+1) (by omega))

def boundedPoint {w h} (p : Point) (hp : p.time≤w ∧ p.depth≤h) :
    Fin ((w+1)*(h+1)+1) :=
  (rectangleVertexCode w h).encode (some (⟨p.time,by omega⟩,⟨p.depth,by omega⟩))

def exteriorApex (w h : Nat) : Fin ((w+1)*(h+1)+1) :=
  (rectangleVertexCode w h).encode none

theorem boundedPoint_eq {w h} {p q : Point}
    {hp : p.time≤w ∧ p.depth≤h} {hq : q.time≤w ∧ q.depth≤h} (he : p=q) :
    boundedPoint p hp=boundedPoint q hq := by subst q; rfl

theorem boundedPoint_injective {w h} {p q : Point}
    {hp : p.time≤w ∧ p.depth≤h} {hq : q.time≤w ∧ q.depth≤h}
    (he : boundedPoint p hp=boundedPoint q hq) : p=q := by
  have he' := congrArg (@vertexPoint w h) ((rectangleVertexCode w h).injective he)
  exact Option.some.inj he'

theorem boundedPoint_ne_apex {w h} (p : Point) (hp : p.time≤w ∧ p.depth≤h) :
    boundedPoint p hp≠exteriorApex w h := by
  intro he
  have he' := (rectangleVertexCode w h).injective he
  cases he'

theorem incidence_tail_boundedPoint {w h} (hw : 0<w) (hh : 0<h)
    (d : TDart w h) (p : Point) (hp : p.time≤w ∧ p.depth≤h)
    (he : d.tail hw hh=some p) : (incidenceMap hw hh).tail d=boundedPoint p hp := by
  change (rectangleVertexCode w h).encode (d.vertexLabel hw hh)=_
  apply congrArg (rectangleVertexCode w h).encode
  apply vertexPoint_injective
  change vertexPoint (d.vertexLabel hw hh)=some p
  exact (vertexLabel_point hw hh d).trans he

theorem incidence_tail_apex {w h} (hw : 0<w) (hh : 0<h)
    (d : TDart w h) (he : d.tail hw hh=none) :
    (incidenceMap hw hh).tail d=exteriorApex w h := by
  change (rectangleVertexCode w h).encode (d.vertexLabel hw hh)=_
  apply congrArg (rectangleVertexCode w h).encode
  apply vertexPoint_injective
  change vertexPoint (d.vertexLabel hw hh)=none
  exact (vertexLabel_point hw hh d).trans he

/-- Ordinary source routes retain every existing unit-grid step in the
actual triangulation. No new geometric assumption is supplied. -/
noncomputable def sourceRealization {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : Realization (sourceGraph D)
      (actualGraph (rectangleWidth_positive events) (rectangleHeight_positive D)) where
  length := fun e => ((sourceGridSubdivision D).route e).length
  positive := fun e => ((sourceGridSubdivision D).route e).positive
  point := fun v => boundedPoint (sourcePoint D v) (sourcePoint_in_rectangle D v)
  point_injective := by
    intro u v he
    exact sourcePoint_injective D (boundedPoint_injective he)
  pointAt := fun e i => boundedPoint (((sourceGridSubdivision D).route e).atPoint i.val)
    (source_route_in_rectangle D e ⟨i.val,by have := i.isLt; omega,rfl⟩)
  first := fun e => boundedPoint_eq ((sourceGridSubdivision D).route e).first
  last := fun e => boundedPoint_eq ((sourceGridSubdivision D).route e).last
  path_injective := by
    intro e i j he
    apply Fin.ext
    exact ((sourceGridSubdivision D).route e).injective (by have := i.isLt; omega)
      (by have := j.isLt; omega) (boundedPoint_injective he)
  step := by
    intro e i
    obtain ⟨d,hd,hh⟩ := source_route_step_has_rectangle_dart D e i.isLt
    refine ⟨TDart.grid d,?_,?_⟩
    · apply incidence_tail_boundedPoint
      exact congrArg some hd
    · apply incidence_tail_boundedPoint
      exact congrArg some hh
  avoids := by
    intro e i hi hi' v he
    exact (sourceGridSubdivision D).avoids_vertices e _ ⟨i.val,hi,hi',rfl⟩ v
      (boundedPoint_injective he)
  disjoint := by
    intro e f i j hi hi' hj hj' he
    exact (sourceGridSubdivision D).disjoint e f _ ⟨i.val,hi,hi',rfl⟩
      ⟨j.val,hj,hj',(boundedPoint_injective he).symm⟩

theorem source_anchor_apex_adj {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Node D) (hv : endpointAnchor D v) :
    (actualGraph (rectangleWidth_positive events) (rectangleHeight_positive D)).Adj
      (exteriorApex (rectangleWidth events) (rectangleHeight D)) ((sourceRealization D).point v) := by
  obtain ⟨e,rfl⟩ := hv
  let x : Fin (rectangleWidth events+1) := ⟨e.val,by
    have he := e.isLt
    have hw := Nat.le_max_right 1 events
    unfold rectangleWidth
    omega⟩
  let d := TDart.toApex (baselineIndex (rectangleWidth_positive events) (rectangleHeight_positive D) x)
  have hd := baseline_apex_edge (rectangleWidth_positive events) (rectangleHeight_positive D) x
  apply (actualGraph (rectangleWidth_positive events) (rectangleHeight_positive D)).symm
  refine ⟨d,?_,?_⟩
  · exact incidence_tail_boundedPoint _ _ d (sourcePoint D (anchor D e))
      (sourcePoint_in_rectangle D (anchor D e)) (by
        simpa only [sourcePoint,nodeVertex_anchor,Vertex.point,endpointPoint,x] using hd.1)
  · exact incidence_tail_apex _ _ d.reverse hd.2

/-- A fully constructed finite subdivision of the source graph with its
unlabeled anchor apex inside the explicit triangulated rectangle. -/
noncomputable def sourceApexRealization {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : Realization (SourceApex.graph (sourceGraph D) (endpointAnchor D))
      (actualGraph (rectangleWidth_positive events) (rectangleHeight_positive D)) :=
  (sourceRealization D).withApex (endpointAnchor D)
    (exteriorApex (rectangleWidth events) (rectangleHeight D))
    (fun v => boundedPoint_ne_apex _ (sourcePoint_in_rectangle D v))
    (fun e i => boundedPoint_ne_apex _
      (source_route_in_rectangle D e ⟨i.val,by
        have hi : i.val<((sourceGridSubdivision D).route e).length+1 := i.isLt
        omega,rfl⟩))
    (source_anchor_apex_adj D)

@[simp] theorem sourceApexRealization_zero {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : (sourceApexRealization D).point 0=
      exteriorApex (rectangleWidth events) (rectangleHeight D) := rfl

@[simp] theorem sourceApexRealization_succ {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Node D) : (sourceApexRealization D).point v.succ=
      boundedPoint (sourcePoint D v) (sourcePoint_in_rectangle D v) := rfl

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
