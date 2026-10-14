import RectangleFaceOrbits

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

@[simp] theorem cycle4_zero : cycleNext (0 : Fin 4) = 1 := by decide
@[simp] theorem cycle4_one : cycleNext (1 : Fin 4) = 2 := by decide
@[simp] theorem cycle4_two : cycleNext (2 : Fin 4) = 3 := by decide
@[simp] theorem cycle4_three : cycleNext (3 : Fin 4) = 0 := by decide

def directionActive (a b c d : Bool) (i : Fin 4) : Bool :=
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else d

def nextActive (a b c d : Bool) (i : Fin 4) : Fin 4 :=
  if directionActive a b c d (cycleNext i) then cycleNext i
  else if directionActive a b c d (cycleNext (cycleNext i)) then cycleNext (cycleNext i)
  else if directionActive a b c d (cycleNext (cycleNext (cycleNext i))) then
    cycleNext (cycleNext (cycleNext i))
  else i

/-- Finite four-direction arithmetic: any two available directions lie on
one next-available cycle, with at most three successor steps between them. -/
theorem nextActive_connected : ∀ a b c d : Bool, ∀ i j : Fin 4,
    directionActive a b c d i = true → directionActive a b c d j = true →
    j=i ∨ j=nextActive a b c d i ∨ j=nextActive a b c d (nextActive a b c d i) ∨
      j=nextActive a b c d (nextActive a b c d (nextActive a b c d i)) := by decide

/-- Local cyclic order: east, north, west, south. -/
def Dart.direction {w h} : Dart w h → Fin 4
  | .east _ _ => 0
  | .north _ _ => 1
  | .west _ _ => 2
  | .south _ _ => 3

theorem Dart.tail_direction_injective {w h} {d e : Dart w h}
    (ht : d.tail=e.tail) (hd : d.direction=e.direction) : d=e := by
  have hx := congrArg Point.time ht
  have hy := congrArg Point.depth ht
  cases d <;> cases e <;> simp [Dart.direction,Fin.ext_iff,show (3 : Fin 4).val=3 by decide] at hd
  all_goals simp only [Dart.tail] at hx hy
  all_goals congr 1 <;> apply Fin.ext <;> (try dsimp only at *) <;> omega

def pointDirectionNext {w h : Nat} (p : Point) (i : Fin 4) : Fin 4 :=
  nextActive (decide (p.time<w)) (decide (0<p.depth))
    (decide (0<p.time)) (decide (p.depth<h)) i

theorem Dart.direction_active {w h} (d : Dart w h) :
    directionActive (decide (d.tail.time<w)) (decide (0<d.tail.depth))
      (decide (0<d.tail.time)) (decide (d.tail.depth<h)) d.direction = true := by
  cases d with
  | east x y => simp [Dart.tail,Dart.direction,directionActive,x.isLt]
  | north x y => simp [Dart.tail,Dart.direction,directionActive]
  | west x y => simp [Dart.tail,Dart.direction,directionActive]
  | south x y => simp [Dart.tail,Dart.direction,directionActive,y.isLt,show (3 : Fin 4).val=3 by decide]

end StackSorting.GraphWidth.UCurve.PlaneGrid
