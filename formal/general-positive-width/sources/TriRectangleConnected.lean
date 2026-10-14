import TriRectangleIncidence

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

def MapStep {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h) : Prop :=
  OrbitStep (TDart.rotate hw hh) d e ∨ OrbitStep (@TDart.reverse w h) d e

theorem mapStep_symm {w h} (hw : 0<w) (hh : 0<h) {d e : TDart w h}
    (hs : MapStep hw hh d e) : MapStep hw hh e d := by
  obtain hs | hs := hs
  · exact Or.inl hs.symm
  · exact Or.inr hs.symm

theorem rotation_to_map {w h} (hw : 0<w) (hh : 0<h) {d e : TDart w h}
    (hp : RotationWalk hw hh d e) : Walk (MapStep hw hh) (fun _ => True) d e :=
  walk_map (adj := OrbitStep (TDart.rotate hw hh)) (adj' := MapStep hw hh)
    id (fun h => Or.inl h) hp

theorem grid_map_lift {w h} (hw : 0<w) (hh : 0<h) {d e : Dart w h}
    (hp : Walk (PlaneGrid.MapStep hw hh) (fun _ => True) d e) :
    Walk (MapStep hw hh) (fun _ => True) (.grid d) (.grid e) := by
  induction hp with
  | refl => exact .refl trivial
  | @step a b c _ hs _ ih =>
    have hab : Walk (MapStep hw hh) (fun _ => True) (.grid a) (.grid b) := by
      obtain hs | hs := hs
      · obtain hs | hs := hs
        · exact rotation_to_map hw hh (hs ▸ grid_rotation_lift hw hh a)
        · exact (rotation_to_map hw hh (hs ▸ grid_rotation_lift hw hh b)).reverse (mapStep_symm hw hh)
      · obtain hs | hs := hs
        · exact .step trivial (Or.inr (Or.inl (show (TDart.grid a).reverse=.grid b from congrArg TDart.grid hs))) (.refl trivial)
        · exact .step trivial (Or.inr (Or.inr (show (TDart.grid b).reverse=.grid a from congrArg TDart.grid hs))) (.refl trivial)
    exact hab.trans ih

theorem every_dart_reaches_grid {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    ∃ e : Dart w h, Walk (MapStep hw hh) (fun _ => True) d (.grid e) := by
  by_cases hd : d.tail hw hh=none
  · obtain ⟨i,rfl⟩ := tail_none hw hh d hd
    refine ⟨(boundaryAt hw hh i).toDart,?_⟩
    exact .step trivial (Or.inr (Or.inl rfl)) (rotation_to_map hw hh (rotation_one hw hh (.toApex i)))
  · obtain ⟨e,he⟩ := nonapex_reaches_grid hw hh d hd
    exact ⟨e,rotation_to_map hw hh he⟩

/-- The actual rotations and edge reversals form one connected dart map. -/
theorem map_connected {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h) :
    Walk (MapStep hw hh) (fun _ => True) d e := by
  obtain ⟨a,ha⟩ := every_dart_reaches_grid hw hh d
  obtain ⟨b,hb⟩ := every_dart_reaches_grid hw hh e
  exact ha.trans ((grid_map_lift hw hh (rectangle_map_connected hw hh a b)).trans
    (hb.reverse (mapStep_symm hw hh)))

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
