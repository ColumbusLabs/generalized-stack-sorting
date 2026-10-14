import TriRectangleCounts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

theorem exterior_tail_injective {w h} (hw : 0<w) (hh : 0<h) {d e : FaceDart w h}
    (hd : d.faceId=none) (he : e.faceId=none) (ht : d.toDart.tail=e.toDart.tail) : d=e := by
  have hx := congrArg Point.time ht
  have hy := congrArg Point.depth ht
  cases d <;> cases e
  all_goals simp only [FaceDart.faceId] at hd he
  all_goals try contradiction
  all_goals simp only [FaceDart.toDart,Dart.tail] at hx hy
  all_goals first
    | (congr 1; apply Fin.ext; omega)
    | (rename_i a b; have ha := a.isLt; have hb := b.isLt; exfalso; omega)

theorem boundary_tail_injective {w h} (hw : 0<w) (hh : 0<h) {i j : Fin (perimeter w h)}
    (ht : (boundaryAt hw hh i).toDart.tail=(boundaryAt hw hh j).toDart.tail) : i=j := by
  have he := exterior_tail_injective hw hh (boundaryAt_exterior hw hh i)
    (boundaryAt_exterior hw hh j) ht
  apply Fin.ext
  have he' := congrArg boundaryIndex he
  simpa only [boundaryIndex_at] using he'

theorem TDart.endpoints_injective {w h} (hw : 0<w) (hh : 0<h) {d e : TDart w h}
    (ht : d.tail hw hh=e.tail hw hh) (he : d.head hw hh=e.head hw hh) : d=e := by
  cases d with
  | grid a =>
    cases e with
    | grid b =>
      exact congrArg TDart.grid (Dart.endpoints_injective (Option.some.inj ht) (Option.some.inj he))
    | diagonal x y | antidiagonal x y =>
      have ht' := Option.some.inj ht
      have he' := Option.some.inj he
      have tx := congrArg Point.time ht'
      have ty := congrArg Point.depth ht'
      have hx := congrArg Point.time he'
      have hy := congrArg Point.depth he'
      cases a <;> simp only [Dart.tail,Dart.reverse] at tx ty hx hy
      all_goals exfalso; omega
    | toApex i => cases he
    | fromApex i => cases ht
  | diagonal x y =>
    cases e with
    | grid b =>
      have ht' := Option.some.inj ht
      have he' := Option.some.inj he
      have tx := congrArg Point.time ht'
      have ty := congrArg Point.depth ht'
      have hx := congrArg Point.time he'
      have hy := congrArg Point.depth he'
      cases b <;> simp only [Dart.tail,Dart.reverse] at tx ty hx hy
      all_goals exfalso; omega
    | diagonal x' y' =>
      have ht' := Option.some.inj ht
      have hx := congrArg Point.time ht'
      have hy := congrArg Point.depth ht'
      congr 1 <;> apply Fin.ext <;> assumption
    | antidiagonal x' y' =>
      have ht' := Option.some.inj ht
      have he' := Option.some.inj he
      have hx := congrArg Point.time ht'
      have hx' := congrArg Point.time he'
      dsimp only at hx hx'
      exfalso; omega
    | toApex i => cases he
    | fromApex i => cases ht
  | antidiagonal x y =>
    cases e with
    | grid b =>
      have ht' := Option.some.inj ht
      have he' := Option.some.inj he
      have tx := congrArg Point.time ht'
      have ty := congrArg Point.depth ht'
      have hx := congrArg Point.time he'
      have hy := congrArg Point.depth he'
      cases b <;> simp only [Dart.tail,Dart.reverse] at tx ty hx hy
      all_goals exfalso; omega
    | diagonal x' y' =>
      have ht' := Option.some.inj ht
      have he' := Option.some.inj he
      have hx := congrArg Point.time ht'
      have hx' := congrArg Point.time he'
      dsimp only at hx hx'
      exfalso; omega
    | antidiagonal x' y' =>
      have he' := Option.some.inj he
      have hx := congrArg Point.time he'
      have hy := congrArg Point.depth he'
      congr 1 <;> apply Fin.ext <;> assumption
    | toApex i => cases he
    | fromApex i => cases ht
  | toApex i =>
    cases e with
    | grid b | diagonal x y | antidiagonal x y => cases he
    | fromApex j => cases ht
    | toApex j => exact congrArg TDart.toApex (boundary_tail_injective hw hh (Option.some.inj ht))
  | fromApex i =>
    cases e with
    | grid b | diagonal x y | antidiagonal x y | toApex j => cases ht
    | fromApex j => exact congrArg TDart.fromApex (boundary_tail_injective hw hh (Option.some.inj he))

/-- Inclusion preserves every old directed grid edge and both of its endpoints. -/
theorem grid_edge_preserved {w h} (hw : 0<w) (hh : 0<h) (d : Dart w h) :
    (TDart.grid d).tail hw hh=some d.tail ∧ (TDart.grid d).head hw hh=some d.head ∧
      (TDart.grid d).reverse=.grid d.reverse := ⟨rfl,rfl,rfl⟩

def baselineIndex {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) : Fin (perimeter w h) :=
  exteriorIndex hw hh (baselineDart hw hh x).toFaceDart (baselineDart_exterior hw hh x)

theorem baselineAt_index {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) :
    (boundaryAt hw hh (baselineIndex hw hh x)).toDart=baselineDart hw hh x := by
  unfold baselineIndex exteriorIndex
  rw [boundaryAt_index hw hh _ (baselineDart_exterior hw hh x),Dart.face_roundtrip]

/-- Each baseline anchor has an actual preserved spoke to the unique exterior apex. -/
theorem baseline_apex_edge {w h} (hw : 0<w) (hh : 0<h) (x : Fin (w+1)) :
    (TDart.toApex (baselineIndex hw hh x)).tail hw hh=some ⟨x.val,0⟩ ∧
    (TDart.toApex (baselineIndex hw hh x)).head hw hh=none := by
  constructor
  · change some (boundaryAt hw hh (baselineIndex hw hh x)).toDart.tail=some ⟨x.val,0⟩
    rw [baselineAt_index,baselineDart_tail]
  · rfl

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
