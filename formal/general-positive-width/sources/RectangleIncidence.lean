import RectangleEuler

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

theorem point_ext {p q : Point} (ht : p.time=q.time) (hd : p.depth=q.depth) : p=q := by
  cases p; cases q; simp_all

/-- Every bounded unit grid step is an actual dart of the rectangle. -/
theorem unit_step_has_dart {w h} {p q : Point}
    (hp : p.time≤w ∧ p.depth≤h) (hq : q.time≤w ∧ q.depth≤h)
    (hu : UnitAdjacent p q) : ∃ d : Dart w h, d.tail=p ∧ d.head=q := by
  rcases hu with ⟨ht,hd | hd⟩ | ⟨hd,ht | ht⟩
  · let d : Dart w h := .south ⟨p.time,by omega⟩ ⟨p.depth,by omega⟩
    exact ⟨d,rfl,point_ext ht hd⟩
  · let d : Dart w h := .north ⟨p.time,by omega⟩ ⟨q.depth,by omega⟩
    exact ⟨d,point_ext rfl hd,point_ext ht rfl⟩
  · let d : Dart w h := .east ⟨p.time,by omega⟩ ⟨p.depth,by omega⟩
    exact ⟨d,rfl,point_ext ht hd⟩
  · let d : Dart w h := .west ⟨q.time,by omega⟩ ⟨p.depth,by omega⟩
    exact ⟨d,point_ext ht rfl,point_ext rfl hd⟩

/-- Each unit directed edge has one rectangle dart, even at the boundary. -/
theorem Dart.endpoints_injective {w h} {d e : Dart w h}
    (ht : d.tail=e.tail) (hh : d.head=e.head) : d=e := by
  have tx := congrArg Point.time ht
  have ty := congrArg Point.depth ht
  have hx := congrArg Point.time hh
  have hy := congrArg Point.depth hh
  cases d <;> cases e
  all_goals simp only [Dart.tail,Dart.head,Dart.reverse] at tx ty hx hy
  all_goals first
    | (exfalso; omega)
    | (congr 1 <;> apply Fin.ext <;> (try dsimp only at *) <;> omega)

/-- An actual exterior-incidence witness at every baseline vertex. -/
def baselineDart {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) : Dart w h :=
  if hx : 0<x.val then .west ⟨x.val-1,by omega⟩ ⟨0,by omega⟩
  else .south ⟨0,by omega⟩ ⟨0,hh⟩

theorem baselineDart_tail {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) :
    (baselineDart hw hh x).tail=⟨x.val,0⟩ := by
  unfold baselineDart
  split
  · apply point_ext
    · change x.val-1+1=x.val
      exact Nat.sub_add_cancel (by omega)
    · rfl
  · apply point_ext
    · change 0=x.val
      omega
    · rfl

theorem baselineDart_exterior {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) :
    (baselineDart hw hh x).toFaceDart.faceId=none := by
  unfold baselineDart
  split <;> simp [Dart.toFaceDart,FaceDart.faceId]

/-- All baseline incidence darts lie in the same actual face component of
the full rectangle, rather than a face merely named exterior. -/
theorem baselineDarts_one_face {w h} (hw : 0<w) (hh : 0<h) (x y : Fin (w+1)) :
    Walk (OrbitStep (Dart.faceNext hw hh)) (fun _ => True)
      (baselineDart hw hh x) (baselineDart hw hh y) := by
  apply (Dart.face_orbits_exact hw hh _ _).mpr
  simp only [baselineDart_exterior]

end StackSorting.GraphWidth.UCurve.PlaneGrid
