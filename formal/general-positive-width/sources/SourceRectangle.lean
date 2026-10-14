import RectangleIncidence

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def listMaximum : List Nat → Nat
  | [] => 0
  | x::xs => max x (listMaximum xs)

theorem mem_le_listMaximum {xs : List Nat} {x : Nat} (h : x∈xs) : x≤listMaximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    obtain rfl | h := List.mem_cons.mp h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

def rectangleWidth (events : Nat) : Nat := max 1 events

def rectangleHeight {tokens events} {E : EndpointPairing tokens events} (D : Drawing E) : Nat :=
  max 1 (listMaximum (List.ofFn D.depth))

theorem rectangleWidth_positive (events : Nat) : 0<rectangleWidth events := by
  have := Nat.le_max_left 1 events
  unfold rectangleWidth
  omega

theorem rectangleHeight_positive {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : 0<rectangleHeight D := by
  have := Nat.le_max_left 1 (listMaximum (List.ofFn D.depth))
  unfold rectangleHeight
  omega

theorem token_depth_bounded {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : D.depth v≤rectangleHeight D := by
  apply Nat.le_trans (mem_le_listMaximum (xs := List.ofFn D.depth) ?_)
    (Nat.le_max_right _ _)
  exact List.mem_ofFn.mpr ⟨v,rfl⟩

def InSourceRectangle {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (p : Point) : Prop := p.time≤rectangleWidth events ∧ p.depth≤rectangleHeight D

theorem onCurve_in_rectangle {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {p : Point} (hp : OnCurve D v p) : InSourceRectangle D p := by
  have hl := (E.left v).isLt
  have hr := (E.right v).isLt
  have hd := token_depth_bounded D v
  have hw := Nat.le_max_right 1 events
  unfold InSourceRectangle rectangleWidth
  rcases hp with ⟨ht,_⟩ | ⟨_,_,_⟩
  · rcases ht with ht | ht <;> omega
  · omega

theorem sourcePoint_in_rectangle {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Node D) : InSourceRectangle D (sourcePoint D v) := by
  have hw := Nat.le_max_right 1 events
  unfold sourcePoint
  generalize nodeVertex D v=x
  cases x with
  | endpoint e =>
    have he := e.isLt
    change e.val≤max 1 events ∧ 0≤rectangleHeight D
    exact ⟨by omega,Nat.zero_le _⟩
  | crossing e t =>
    have he := e.isLt
    change e.val≤max 1 events ∧ D.depth t≤rectangleHeight D
    exact ⟨by omega,token_depth_bounded D t⟩

theorem EdgeRoute.interior_in_rectangle {tokens events} {E : EndpointPairing tokens events}
    {D : Drawing E} {a b : Node D} (R : EdgeRoute D a b) {p : Point}
    (hp : R.arc.Interior p) : InSourceRectangle D p := by
  cases R with
  | forward h => exact onCurve_in_rectangle D (curveSourceArc_interior D h hp).1
  | backward h =>
    exact onCurve_in_rectangle D (curveSourceArc_interior D h
      ((curveSourceArc D h).interior_reverse.mp hp)).1
  | baseline h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h) hp)
  | baselineBack h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h).symm hp)

theorem source_route_in_rectangle {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : OrderedEdge (sourceGraph D)) {p : Point}
    (hp : ((sourceGridSubdivision D).route e).OnPath p) : InSourceRectangle D p := by
  rcases ((sourceGridSubdivision D).route e).onPath_cases hp with hp | hp | hp
  · rw [hp]; exact sourcePoint_in_rectangle D e.low
  · rw [hp]; exact sourcePoint_in_rectangle D e.high
  · exact EdgeRoute.interior_in_rectangle (chosenEdgeRoute D e) hp

/-- Every unit step of every chosen source route is an actual dart in a
finite rectangle whose face, vertex and edge orbits have been constructed. -/
theorem source_route_step_has_rectangle_dart {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : OrderedEdge (sourceGraph D)) {a : Nat}
    (ha : a<((sourceGridSubdivision D).route e).length) :
    ∃ d : Dart (rectangleWidth events) (rectangleHeight D),
      d.tail=((sourceGridSubdivision D).route e).atPoint a ∧
      d.head=((sourceGridSubdivision D).route e).atPoint (a+1) := by
  apply unit_step_has_dart
  · exact source_route_in_rectangle D e ⟨a,by omega,rfl⟩
  · exact source_route_in_rectangle D e ⟨a+1,by omega,rfl⟩
  · exact ((sourceGridSubdivision D).route e).step a ha

/-- Every source baseline anchor has a genuine exterior-face incidence in
the enclosing rectangle. Exterior incidence after deletion is not asserted. -/
theorem source_anchor_exterior_incidence {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) :
    ∃ d : Dart (rectangleWidth events) (rectangleHeight D),
      d.tail=sourcePoint D (anchor D e) ∧ d.toFaceDart.faceId=none := by
  let x : Fin (rectangleWidth events+1) := ⟨e.val,by
    have he:=e.isLt; have hw:=Nat.le_max_right 1 events; unfold rectangleWidth; omega⟩
  refine ⟨baselineDart (rectangleWidth_positive events) (rectangleHeight_positive D) x,?_,
    baselineDart_exterior _ _ x⟩
  rw [baselineDart_tail]
  simp only [sourcePoint,nodeVertex_anchor,Vertex.point,endpointPoint,x]

end StackSorting.GraphWidth.UCurve.PlaneGrid
