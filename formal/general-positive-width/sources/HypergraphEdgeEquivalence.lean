import OrientedBridgeCertificates

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {inc' : V → F → Prop} {s t : V}

namespace HWalk
@[simp] theorem vertices_mapEdges (f : E → F) (h : ∀ x e, inc x e → inc' x (f e))
    {a b : V} (w : HWalk inc a b) : (w.mapEdges f h).vertices = w.vertices := by
  induction w with
  | nil => rfl
  | cons e hx hy tail ih => exact congrArg (List.cons _) ih

/-- Activate each traversed identifier using the actual incidence at that step. -/
def activate {a b : V} : HWalk inc a b → HWalk (fun (x : V) (e : {e : E // ∃ y, inc y e}) => inc x e.val) a b
  | .nil x => .nil x
  | .cons (x := x) e hx hy tail => .cons ⟨e,⟨x,hx⟩⟩ hx hy tail.activate
end HWalk

/-- A vertex-preserving bijection of actual hyperedge identifiers. -/
structure IncidenceEquiv (inc : V → E → Prop) (inc' : V → F → Prop) where
  edge : E ≃ F
  incidence : ∀ x e, inc' x (edge e) ↔ inc x e

namespace IncidenceEquiv
variable (Q : IncidenceEquiv inc inc')

def symm : IncidenceEquiv inc' inc where
  edge := Q.edge.symm
  incidence x f := by simpa only [Equiv.apply_symm_apply] using (Q.incidence x (Q.edge.symm f)).symm

def mapWalk {a b : V} (w : HWalk inc a b) : HWalk inc' a b :=
  w.mapEdges (inc := inc) (inc' := inc') Q.edge (fun x e h => (Q.incidence x e).mpr h)

@[simp] theorem mapWalk_edges {a b : V} (w : HWalk inc a b) :
    (Q.mapWalk w).edges = w.edges.map Q.edge :=
  HWalk.edges_mapEdges (inc := inc) (inc' := inc') Q.edge (fun x e h => (Q.incidence x e).mpr h) w

@[simp] theorem mapWalk_vertices {a b : V} (w : HWalk inc a b) :
    (Q.mapWalk w).vertices = w.vertices :=
  HWalk.vertices_mapEdges Q.edge (fun x e h => (Q.incidence x e).mpr h) w

def mapPath (p : Path inc s t) : Path inc' s t where
  walk := Q.mapWalk p.walk
  vertices_nodup := by rw [mapWalk_vertices]; exact p.vertices_nodup
  edges_nodup := by rw [mapWalk_edges]; exact p.edges_nodup.map Q.edge.injective

theorem cutedge_iff (e : E) : Cutedge inc' s t (Q.edge e) ↔ Cutedge inc s t e := by
  constructor
  · intro h
    apply (cutedge_iff_every_walk inc s t e).mpr
    intro w
    have hm := (cutedge_iff_every_walk inc' s t (Q.edge e)).mp h (Q.mapWalk w)
    rw [mapWalk_edges] at hm
    obtain ⟨f,hf,heq⟩ := List.mem_map.mp hm
    exact Q.edge.injective heq ▸ hf
  · intro h
    apply (cutedge_iff_every_walk inc' s t (Q.edge e)).mpr
    intro w
    have hm := (cutedge_iff_every_walk inc s t e).mp h (Q.symm.mapWalk w)
    rw [mapWalk_edges] at hm
    obtain ⟨f,hf,heq⟩ := List.mem_map.mp hm
    have heq' : f = Q.edge e := by simpa only [symm,Equiv.apply_symm_apply] using congrArg Q.edge heq
    exact heq' ▸ hf

def noncut : IncidenceEquiv (NoncutIncidence inc s t) (NoncutIncidence inc' s t) where
  edge := Q.edge
  incidence x e := by
    simp only [NoncutIncidence,Q.incidence,Q.cutedge_iff]

include Q in
theorem component_iff (x y : V) : SameCutedgeComponent inc' s t x y ↔ SameCutedgeComponent inc s t x y := by
  constructor
  · rintro ⟨w⟩
    exact ⟨(Q.noncut (s := s) (t := t)).symm.mapWalk w⟩
  · rintro ⟨w⟩
    exact ⟨(Q.noncut (s := s) (t := t)).mapWalk w⟩

def boundary : CutBoundary E ≃ CutBoundary F where
  toFun := fun b => match b with | .source => .source | .sink => .sink | .cut e => .cut (Q.edge e)
  invFun := fun b => match b with | .source => .source | .sink => .sink | .cut e => .cut (Q.edge.symm e)
  left_inv := by intro b; cases b <;> simp
  right_inv := by intro b; cases b <;> simp

theorem boundary_valid_iff (b : CutBoundary E) :
    BoundaryValid (inc := inc') (s := s) (t := t) (Q.boundary b) ↔
      BoundaryValid (inc := inc) (s := s) (t := t) b := by
  cases b with
  | source => rfl
  | sink => rfl
  | cut e => exact Q.cutedge_iff e

theorem boundary_incidence_iff (x : V) (b : CutBoundary E) :
    BoundaryIncidence (inc := inc') (s := s) (t := t) x (Q.boundary b) ↔
      BoundaryIncidence (inc := inc) (s := s) (t := t) x b := by
  cases b with
  | source => rfl
  | sink => rfl
  | cut e => exact Q.incidence x e

theorem boundary_touch_iff (x : V) (b : CutBoundary E) :
    ComponentTouches (inc := inc') (s := s) (t := t) x (Q.boundary b) ↔
      ComponentTouches (inc := inc) (s := s) (t := t) x b := by
  cases b with
  | source => exact Q.component_iff x s
  | sink => exact Q.component_iff x t
  | cut e =>
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,(Q.incidence y e).mp hy,(Q.component_iff x y).mp hxy⟩
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,(Q.incidence y e).mpr hy,(Q.component_iff x y).mpr hxy⟩

include Q in
theorem covers [DecidableEq V] {P : Finset V} {w : Nat} (D : BagPath P w) (hD : D.Covers inc) : D.Covers inc' := by
  intro f
  obtain ⟨e,rfl⟩ := Q.edge.surjective f
  obtain ⟨i,hi,hcover⟩ := hD e
  exact ⟨i,hi,fun x hx hxe => hcover x hx ((Q.incidence x e).mp hxe)⟩

end IncidenceEquiv
end FiniteFlow.Hypergraph
