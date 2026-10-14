import TriRectangleRotation

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

def RotationWalk {w h} (hw : 0<w) (hh : 0<h) (a b : TDart w h) :=
  Walk (OrbitStep (TDart.rotate hw hh)) (fun _ => True) a b

theorem rotation_one {w h} (hw : 0<w) (hh : 0<h) (a : TDart w h) :
    RotationWalk hw hh a (a.rotate hw hh) := .step trivial (Or.inl rfl) (.refl trivial)

theorem rotation_two {w h} (hw : 0<w) (hh : 0<h) (a : TDart w h) :
    RotationWalk hw hh a ((a.rotate hw hh).rotate hw hh) :=
  (rotation_one hw hh a).trans (rotation_one hw hh _)

theorem rotate_diagonal {w h} (hw : 0<w) (hh : 0<h) (x : Fin w) (y : Fin h) :
    (TDart.diagonal x y).rotate hw hh=.grid (.east x ⟨y.val,by omega⟩) := rfl

theorem rotate_antidiagonal {w h} (hw : 0<w) (hh : 0<h) (x : Fin w) (y : Fin h) :
    (TDart.antidiagonal x y).rotate hw hh=.grid (.west x ⟨y.val+1,by omega⟩) := rfl

theorem rotate_toApex {w h} (hw : 0<w) (hh : 0<h) (i : Fin (perimeter w h)) :
    (TDart.toApex i).rotate hw hh=.grid (boundaryAt hw hh i).toDart := rfl

theorem rotate_fromApex {w h} (hw : 0<w) (hh : 0<h) (i : Fin (perimeter w h)) :
    (TDart.fromApex i).rotate hw hh=.fromApex (cyclePrev i) := rfl

theorem rotate_reverse_grid {w h} (hw : 0<w) (hh : 0<h) (f : FaceDart w h) :
    (TDart.grid f.toDart.reverse).rotate hw hh=toDart hw hh (next (fromOld hw hh f)) := by
  simp only [TDart.rotate,TDart.reverse,Dart.reverse_reverse,TDart.faceNext,
    TDart.toIncidence,FaceDart.dart_roundtrip]

theorem grid_rotation_lift_face {w h} (hw : 0<w) (hh : 0<h) (f : FaceDart w h) :
    RotationWalk hw hh (.grid f.toDart.reverse) (.grid (f.faceNext hw hh).toDart) := by
  by_cases hf : f.faceId=none
  · let i := exteriorIndex hw hh f hf
    have hi : boundaryAt hw hh i=f := boundaryAt_index hw hh f hf
    have hr : (TDart.grid f.toDart.reverse).rotate hw hh=.toApex (cycleNext i) := by
      rw [rotate_reverse_grid,fromOld_exterior hw hh f hf]
      rfl
    have hr2 : ((TDart.grid f.toDart.reverse).rotate hw hh).rotate hw hh=
        .grid (f.faceNext hw hh).toDart := by
      rw [hr,rotate_toApex,← boundaryAt_next,hi]
    exact hr2 ▸ rotation_two hw hh (.grid f.toDart.reverse)
  · cases f with
    | cell x y s =>
      have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by
        have hs : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 := by omega
        rcases hs with hs | hs | hs | hs
        · exact Or.inl (Fin.ext hs)
        · exact Or.inr (Or.inl (Fin.ext hs))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext hs)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext hs)))
      rcases hs with rfl | rfl | rfl | rfl
      · have he : (TDart.grid (FaceDart.cell x y 0).toDart.reverse).rotate hw hh=
            .grid ((FaceDart.cell x y 0).faceNext hw hh).toDart := by
          rw [rotate_reverse_grid]
          rfl
        exact he ▸ rotation_one hw hh _
      · have he : ((TDart.grid (FaceDart.cell x y 1).toDart.reverse).rotate hw hh).rotate hw hh=
            .grid ((FaceDart.cell x y 1).faceNext hw hh).toDart := by
          rw [rotate_reverse_grid]
          rfl
        exact he ▸ rotation_two hw hh _
      · have he : (TDart.grid (FaceDart.cell x y 2).toDart.reverse).rotate hw hh=
            .grid ((FaceDart.cell x y 2).faceNext hw hh).toDart := by
          rw [rotate_reverse_grid]
          rfl
        exact he ▸ rotation_one hw hh _
      · have he : ((TDart.grid (FaceDart.cell x y 3).toDart.reverse).rotate hw hh).rotate hw hh=
            .grid ((FaceDart.cell x y 3).faceNext hw hh).toDart := by
          rw [rotate_reverse_grid]
          rfl
        exact he ▸ rotation_two hw hh _
    | bottom x | right y | top x | left y => exact False.elim (hf rfl)

theorem grid_rotation_lift {w h} (hw : 0<w) (hh : 0<h) (d : Dart w h) :
    RotationWalk hw hh (.grid d) (.grid (d.rotate hw hh)) := by
  have hp := grid_rotation_lift_face hw hh d.reverse.toFaceDart
  simpa only [Dart.face_roundtrip,Dart.reverse_reverse,Dart.rotate,Dart.faceNext] using hp

theorem grid_walk_lift {w h} (hw : 0<w) (hh : 0<h) {d e : Dart w h}
    (hp : Walk (OrbitStep (Dart.rotate hw hh)) (fun _ => True) d e) :
    RotationWalk hw hh (.grid d) (.grid e) := by
  induction hp with
  | refl => exact .refl trivial
  | @step a b c _ hs _ ih =>
    have hab : RotationWalk hw hh (.grid a) (.grid b) := by
      obtain hs | hs := hs
      · exact hs ▸ grid_rotation_lift hw hh a
      · exact (hs ▸ grid_rotation_lift hw hh b).reverse (fun h => h.symm)
    exact hab.trans ih

theorem grid_same_vertex_connected {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h)
    (ht : d.tail=e.tail) : RotationWalk hw hh (.grid d) (.grid e) :=
  grid_walk_lift hw hh (Dart.same_vertex_connected hw hh d e ht)



theorem apex_connected {w h} (hw : 0<w) (hh : 0<h) (i j : Fin (perimeter w h)) :
    RotationWalk hw hh (.fromApex i) (.fromApex j) := by
  apply walk_map TDart.fromApex (h := cycle_connected (by unfold perimeter; omega) i j)
  intro a b hab
  obtain hab | hab := hab
  · apply Or.inr
    rw [rotate_fromApex,← hab,cyclePrev_next]
  · apply Or.inl
    rw [rotate_fromApex,← hab,cyclePrev_next]

theorem connected_same_vertex {w h} (hw : 0<w) (hh : 0<h) {d e : TDart w h}
    (hp : RotationWalk hw hh d e) : d.tail hw hh=e.tail hw hh := by
  induction hp with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have hab : a.tail hw hh=b.tail hw hh := by
      obtain hs | hs := hs
      · exact (TDart.rotate_preserves_vertex hw hh a).symm.trans (congrArg (TDart.tail hw hh) hs)
      · exact (congrArg (TDart.tail hw hh) hs).symm.trans (TDart.rotate_preserves_vertex hw hh b)
    exact hab.trans ih

theorem tail_none {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h)
    (ht : d.tail hw hh=none) : ∃ i, d=.fromApex i := by
  cases d <;> simp only [TDart.tail] at ht
  all_goals try contradiction
  exact ⟨_,rfl⟩

theorem nonapex_reaches_grid {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h)
    (ht : d.tail hw hh≠none) : ∃ e : Dart w h, RotationWalk hw hh d (.grid e) := by
  cases d with
  | grid e => exact ⟨e,.refl trivial⟩
  | diagonal x y => exact ⟨_,rotation_one hw hh _⟩
  | antidiagonal x y => exact ⟨_,rotation_one hw hh _⟩
  | toApex i => exact ⟨_,rotation_one hw hh _⟩
  | fromApex i => exact False.elim (ht rfl)

theorem same_vertex_connected {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h)
    (ht : d.tail hw hh=e.tail hw hh) : RotationWalk hw hh d e := by
  by_cases hd : d.tail hw hh=none
  · obtain ⟨i,rfl⟩ := tail_none hw hh d hd
    obtain ⟨j,rfl⟩ := tail_none hw hh e (ht.symm.trans hd)
    exact apex_connected hw hh i j
  · have he : e.tail hw hh≠none := by intro he; exact hd (ht.trans he)
    obtain ⟨a,ha⟩ := nonapex_reaches_grid hw hh d hd
    obtain ⟨b,hb⟩ := nonapex_reaches_grid hw hh e he
    have ha' := connected_same_vertex hw hh ha
    have hb' := connected_same_vertex hw hh hb
    have hab : a.tail=b.tail := by
      exact Option.some.inj (ha'.symm.trans (ht.trans hb'))
    exact ha.trans ((grid_same_vertex_connected hw hh a b hab).trans
      (hb.reverse (fun h => h.symm)))

theorem vertex_orbits_exact {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h) :
    RotationWalk hw hh d e ↔ d.tail hw hh=e.tail hw hh :=
  ⟨connected_same_vertex hw hh,same_vertex_connected hw hh d e⟩

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
