import FourDirectionCycles

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

theorem rotate_east_direction {w h} (hw : 0<w) (hh : 0<h) (x : Fin w) (y : Fin (h+1)) :
    ((Dart.east x y).rotate hw hh).direction = if 0<y.val then 1 else if 0<x.val then 2 else 3 := by
  by_cases hy : 0<y.val <;> by_cases hx : 0<x.val
  all_goals simp [Dart.rotate,Dart.faceNext,Dart.reverse,Dart.toFaceDart,hy,hx,
    FaceDart.faceNext,FaceDart.toDart,Dart.direction,show (3 : Fin 4).val=3 by decide]

theorem rotate_north_direction {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) (y : Fin h) :
    ((Dart.north x y).rotate hw hh).direction = if 0<x.val then 2 else if y.val+1<h then 3 else 0 := by
  by_cases hx : 0<x.val <;> by_cases hy : y.val+1<h
  all_goals simp [Dart.rotate,Dart.faceNext,Dart.reverse,Dart.toFaceDart,hy,hx,
    FaceDart.faceNext,FaceDart.toDart,Dart.direction,show (3 : Fin 4).val=3 by decide]

theorem rotate_west_direction {w h} (hw : 0<w) (hh : 0<h) (x : Fin w) (y : Fin (h+1)) :
    ((Dart.west x y).rotate hw hh).direction = if y.val<h then 3 else if x.val+1<w then 0 else 1 := by
  by_cases hy : y.val<h <;> by_cases hx : x.val+1<w
  all_goals simp [Dart.rotate,Dart.faceNext,Dart.reverse,Dart.toFaceDart,hy,hx,
    FaceDart.faceNext,FaceDart.toDart,Dart.direction,show (3 : Fin 4).val=3 by decide]

theorem rotate_south_direction {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) (y : Fin h) :
    ((Dart.south x y).rotate hw hh).direction = if x.val<w then 0 else if 0<y.val then 1 else 2 := by
  by_cases hx : x.val<w <;> by_cases hy : 0<y.val
  all_goals simp [Dart.rotate,Dart.faceNext,Dart.reverse,Dart.toFaceDart,hy,hx,
    FaceDart.faceNext,FaceDart.toDart,Dart.direction,show (3 : Fin 4).val=3 by decide]

theorem Dart.rotate_direction {w h} (hw : 0<w) (hh : 0<h) (d : Dart w h) :
    (d.rotate hw hh).direction = pointDirectionNext (w := w) (h := h) d.tail d.direction := by
  cases d with
  | east x y =>
    rw [rotate_east_direction]
    by_cases hy : 0<y.val
    · simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hy]
    · have hy0 : y.val=0 := by omega
      simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hy0,hh,
        show (3 : Fin 4).val=3 by decide]
  | north x y =>
    rw [rotate_north_direction]
    by_cases hx : 0<x.val
    · simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hx]
    · have hx0 : x.val=0 := by omega
      simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hx0,hw,
        show (3 : Fin 4).val=3 by decide]
  | west x y =>
    rw [rotate_west_direction]
    by_cases hy : y.val<h
    · simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hy,
        show (3 : Fin 4).val=3 by decide]
    · have hp : 0<y.val := by omega
      by_cases hx : x.val+1<w <;>
        simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hy,hp,hx,
        show (3 : Fin 4).val=3 by decide]
  | south x y =>
    rw [rotate_south_direction]
    by_cases hx : x.val<w
    · simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hx,
        show (3 : Fin 4).val=3 by decide]
    · have hp : 0<x.val := by omega
      by_cases hy : 0<y.val <;>
        simp [pointDirectionNext,nextActive,directionActive,Dart.tail,Dart.direction,hx,hp,hy,
        show (3 : Fin 4).val=3 by decide]

/-- The explicitly defined rotation visits every outgoing dart at a vertex
in at most three steps. This supplies the local one-cycle property. -/
theorem Dart.same_tail_rotate_steps {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h)
    (ht : d.tail=e.tail) :
    e=d ∨ e=d.rotate hw hh ∨ e=(d.rotate hw hh).rotate hw hh ∨
      e=((d.rotate hw hh).rotate hw hh).rotate hw hh := by
  have he := e.direction_active
  rw [← ht] at he
  have hc := nextActive_connected (decide (d.tail.time<w)) (decide (0<d.tail.depth))
    (decide (0<d.tail.time)) (decide (d.tail.depth<h)) d.direction e.direction
    d.direction_active he
  let f := pointDirectionNext (w := w) (h := h) d.tail
  change e.direction=d.direction ∨ e.direction=f d.direction ∨
    e.direction=f (f d.direction) ∨ e.direction=f (f (f d.direction)) at hc
  have h1 : (d.rotate hw hh).direction=f d.direction := d.rotate_direction hw hh
  have h2 : ((d.rotate hw hh).rotate hw hh).direction=f (f d.direction) := by
    rw [Dart.rotate_direction,Dart.rotate_preserves_vertex,Dart.rotate_direction]
  have h3 : (((d.rotate hw hh).rotate hw hh).rotate hw hh).direction=f (f (f d.direction)) := by
    rw [Dart.rotate_direction,Dart.rotate_preserves_vertex,Dart.rotate_preserves_vertex,h2]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (Dart.tail_direction_injective ht.symm hc)
  · right; left
    exact Dart.tail_direction_injective (by simpa only [Dart.rotate_preserves_vertex] using ht.symm)
      (hc.trans h1.symm)
  · right; right; left
    exact Dart.tail_direction_injective (by simpa only [Dart.rotate_preserves_vertex] using ht.symm)
      (hc.trans h2.symm)
  · right; right; right
    exact Dart.tail_direction_injective (by simpa only [Dart.rotate_preserves_vertex] using ht.symm)
      (hc.trans h3.symm)

theorem Dart.same_vertex_connected {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h)
    (ht : d.tail=e.tail) : Walk (OrbitStep (Dart.rotate hw hh)) (fun _ => True) d e := by
  rcases Dart.same_tail_rotate_steps hw hh d e ht with rfl | rfl | rfl | rfl
  · exact .refl trivial
  · exact .step trivial (Or.inl rfl) (.refl trivial)
  · exact .step trivial (Or.inl rfl) (.step trivial (Or.inl rfl) (.refl trivial))
  · exact .step trivial (Or.inl rfl) (.step trivial (Or.inl rfl)
      (.step trivial (Or.inl rfl) (.refl trivial)))

theorem Dart.connected_same_vertex {w h} (hw : 0<w) (hh : 0<h) {d e : Dart w h}
    (he : Walk (OrbitStep (Dart.rotate hw hh)) (fun _ => True) d e) : d.tail=e.tail := by
  induction he with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have ht : a.tail=b.tail := by
      obtain hs | hs := hs
      · exact (Dart.rotate_preserves_vertex hw hh a).symm.trans (congrArg Dart.tail hs)
      · exact (congrArg Dart.tail hs).symm.trans (Dart.rotate_preserves_vertex hw hh b)
    exact ht.trans ih

theorem Dart.vertex_orbits_exact {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h) :
    Walk (OrbitStep (Dart.rotate hw hh)) (fun _ => True) d e ↔ d.tail=e.tail :=
  ⟨Dart.connected_same_vertex hw hh,Dart.same_vertex_connected hw hh d e⟩

def vertexRepresentative {w h} (hw : 0<w) (x : Fin (w+1)) (y : Fin (h+1)) : Dart w h :=
  if hx : x.val<w then .east ⟨x.val,hx⟩ y else .west ⟨x.val-1,by omega⟩ y

theorem vertexRepresentative_tail {w h} (hw : 0<w) (x : Fin (w+1)) (y : Fin (h+1)) :
    (vertexRepresentative hw x y).tail = ⟨x.val,y.val⟩ := by
  unfold vertexRepresentative
  split
  · rfl
  · change Point.mk (x.val-1+1) y.val = Point.mk x.val y.val
    simp only [Point.mk.injEq]
    have hx := x.isLt
    exact ⟨Nat.sub_add_cancel (by omega),trivial⟩

end StackSorting.GraphWidth.UCurve.PlaneGrid
