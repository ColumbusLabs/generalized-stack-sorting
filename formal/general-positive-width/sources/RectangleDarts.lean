import GridSubdivisionPaths

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

/-- Every directed edge of the complete w-by-h cell rectangle, exactly once. -/
inductive Dart (w h : Nat) where
  | east : Fin w → Fin (h+1) → Dart w h
  | south : Fin (w+1) → Fin h → Dart w h
  | west : Fin w → Fin (h+1) → Dart w h
  | north : Fin (w+1) → Fin h → Dart w h
  deriving DecidableEq

def Dart.tail {w h} : Dart w h → Point
  | .east x y => ⟨x.val,y.val⟩
  | .south x y => ⟨x.val,y.val⟩
  | .west x y => ⟨x.val+1,y.val⟩
  | .north x y => ⟨x.val,y.val+1⟩

def Dart.reverse {w h} : Dart w h → Dart w h
  | .east x y => .west x y
  | .south x y => .north x y
  | .west x y => .east x y
  | .north x y => .south x y

def Dart.head {w h} (d : Dart w h) : Point := d.reverse.tail

theorem Dart.reverse_reverse {w h} (d : Dart w h) : d.reverse.reverse = d := by
  cases d <;> rfl

theorem Dart.reverse_ne {w h} (d : Dart w h) : d.reverse ≠ d := by
  cases d <;> simp [Dart.reverse]

theorem Dart.head_reverse {w h} (d : Dart w h) : d.reverse.head = d.tail := by
  simp only [Dart.head, Dart.reverse_reverse]

theorem Dart.unit_step {w h} (d : Dart w h) : UnitAdjacent d.tail d.head := by
  cases d <;> simp [Dart.tail, Dart.head, Dart.reverse, UnitAdjacent]

theorem Dart.tail_bounded {w h} (d : Dart w h) :
    d.tail.time ≤ w ∧ d.tail.depth ≤ h := by
  cases d with
  | east x y => have hx:=x.isLt; have hy:=y.isLt; simp only [Dart.tail]; omega
  | south x y => have hx:=x.isLt; have hy:=y.isLt; simp only [Dart.tail]; omega
  | west x y => have hx:=x.isLt; have hy:=y.isLt; simp only [Dart.tail]; omega
  | north x y => have hx:=x.isLt; have hy:=y.isLt; simp only [Dart.tail]; omega

theorem Dart.head_bounded {w h} (d : Dart w h) :
    d.head.time ≤ w ∧ d.head.depth ≤ h := d.reverse.tail_bounded

/-- A cell with four oriented sides, or a directed side of the exterior
boundary. These are candidate face incidences; the cycle and rotation
properties will be established separately. -/
inductive FaceDart (w h : Nat) where
  | cell : Fin w → Fin h → Fin 4 → FaceDart w h
  | bottom : Fin w → FaceDart w h
  | left : Fin h → FaceDart w h
  | top : Fin w → FaceDart w h
  | right : Fin h → FaceDart w h
  deriving DecidableEq

def FaceDart.toDart {w h} : FaceDart w h → Dart w h
  | .cell x y side =>
    if side.val = 0 then .east x ⟨y.val, by omega⟩
    else if side.val = 1 then .south ⟨x.val+1, by omega⟩ y
    else if side.val = 2 then .west x ⟨y.val+1, by omega⟩
    else .north ⟨x.val, by omega⟩ y
  | .bottom x => .east x ⟨h, by omega⟩
  | .left y => .south ⟨0, by omega⟩ y
  | .top x => .west x ⟨0, by omega⟩
  | .right y => .north ⟨w, by omega⟩ y

def Dart.toFaceDart {w h} : Dart w h → FaceDart w h
  | .east x y => if hy : y.val < h then .cell x ⟨y.val, hy⟩ 0 else .bottom x
  | .south x y => if hx : 0 < x.val then .cell ⟨x.val-1, by omega⟩ y 1 else .left y
  | .west x y => if hy : 0 < y.val then .cell x ⟨y.val-1, by omega⟩ 2 else .top x
  | .north x y => if hx : x.val < w then .cell ⟨x.val, hx⟩ y 3 else .right y

theorem Dart.face_roundtrip {w h} (d : Dart w h) : d.toFaceDart.toDart = d := by
  cases d with
  | east x y =>
    simp only [Dart.toFaceDart]
    split
    · rfl
    · change Dart.east x ⟨h, _⟩ = Dart.east x y
      apply congrArg (Dart.east x)
      apply Fin.ext
      change h = y.val
      have := y.isLt
      omega
  | south x y =>
    simp only [Dart.toFaceDart]
    split
    · change Dart.south ⟨x.val-1+1,_⟩ y = Dart.south x y
      apply congrArg (fun z => Dart.south z y)
      apply Fin.ext
      change x.val-1+1 = x.val
      omega
    · change Dart.south ⟨0,_⟩ y = Dart.south x y
      apply congrArg (fun z => Dart.south z y)
      apply Fin.ext
      change 0 = x.val
      omega
  | west x y =>
    simp only [Dart.toFaceDart]
    split
    · change Dart.west x ⟨y.val-1+1,_⟩ = Dart.west x y
      apply congrArg (Dart.west x)
      apply Fin.ext
      change y.val-1+1 = y.val
      omega
    · change Dart.west x ⟨0,_⟩ = Dart.west x y
      apply congrArg (Dart.west x)
      apply Fin.ext
      change 0 = y.val
      omega
  | north x y =>
    simp only [Dart.toFaceDart]
    split
    · rfl
    · change Dart.north ⟨w,_⟩ y = Dart.north x y
      apply congrArg (fun z => Dart.north z y)
      apply Fin.ext
      change w = x.val
      have := x.isLt
      omega

theorem FaceDart.dart_roundtrip {w h} (d : FaceDart w h) : d.toDart.toFaceDart = d := by
  cases d with
  | cell x y side =>
    have hs : side = 0 ∨ side = 1 ∨ side = 2 ∨ side = 3 := by
      have hv : side.val=0 ∨ side.val=1 ∨ side.val=2 ∨ side.val=3 := by omega
      rcases hv with hv | hv | hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Or.inl (Fin.ext hv))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext hv)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext hv)))
    rcases hs with rfl | rfl | rfl | rfl
    all_goals simp [FaceDart.toDart,Dart.toFaceDart,x.isLt,y.isLt,show (3 : Fin 4).val = 3 by decide]
  | bottom x => simp [FaceDart.toDart, Dart.toFaceDart]
  | left y => simp [FaceDart.toDart, Dart.toFaceDart]
  | top x => simp [FaceDart.toDart, Dart.toFaceDart]
  | right y => simp [FaceDart.toDart, Dart.toFaceDart]

end StackSorting.GraphWidth.UCurve.PlaneGrid
