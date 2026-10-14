import RectangleConnected

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

inductive Side where
  | first | second | third
  deriving DecidableEq

def Side.next : Side → Side
  | .first => .second | .second => .third | .third => .first

def Side.prev : Side → Side
  | .first => .third | .second => .first | .third => .second

theorem Side.prev_next (s : Side) : s.next.prev=s := by cases s <;> rfl
theorem Side.next_prev (s : Side) : s.prev.next=s := by cases s <;> rfl

def Face (w h : Nat) := Sum (Sum (Fin w × Fin h) (Fin w × Fin h)) (Fin (perimeter w h))
abbrev Incidence (w h : Nat) := Face w h × Side

inductive TDart (w h : Nat) where
  | grid : Dart w h → TDart w h
  | diagonal : Fin w → Fin h → TDart w h
  | antidiagonal : Fin w → Fin h → TDart w h
  | toApex : Fin (perimeter w h) → TDart w h
  | fromApex : Fin (perimeter w h) → TDart w h
  deriving DecidableEq

def TDart.reverse {w h} : TDart w h → TDart w h
  | .grid d => .grid d.reverse
  | .diagonal x y => .antidiagonal x y
  | .antidiagonal x y => .diagonal x y
  | .toApex i => .fromApex i
  | .fromApex i => .toApex i

theorem TDart.reverse_reverse {w h} (d : TDart w h) : d.reverse.reverse=d := by
  cases d <;> simp [TDart.reverse,Dart.reverse_reverse]

theorem TDart.reverse_ne {w h} (d : TDart w h) : d.reverse≠d := by
  cases d <;> simp [TDart.reverse,Dart.reverse_ne]

def exteriorIndex {w h} (hw : 0<w) (hh : 0<h) (d : FaceDart w h)
    (hd : d.faceId=none) : Fin (perimeter w h) :=
  ⟨boundaryIndex d,boundaryIndex_lt hw hh d hd⟩

def fromOld {w h} (hw : 0<w) (hh : 0<h) : FaceDart w h → Incidence w h
  | .cell x y s =>
    if s.val=0 then (.inl (.inl (x,y)),.first)
    else if s.val=1 then (.inl (.inl (x,y)),.second)
    else if s.val=2 then (.inl (.inr (x,y)),.second)
    else (.inl (.inr (x,y)),.third)
  | .bottom x => (.inr (exteriorIndex hw hh (.bottom x) rfl),.first)
  | .right y => (.inr (exteriorIndex hw hh (.right y) rfl),.first)
  | .top x => (.inr (exteriorIndex hw hh (.top x) rfl),.first)
  | .left y => (.inr (exteriorIndex hw hh (.left y) rfl),.first)

def toDart {w h} (hw : 0<w) (hh : 0<h) : Incidence w h → TDart w h
  | (.inl (.inl (x,y)),.first) => .grid (.east x ⟨y.val,by omega⟩)
  | (.inl (.inl (x,y)),.second) => .grid (.south ⟨x.val+1,by omega⟩ y)
  | (.inl (.inl (x,y)),.third) => .antidiagonal x y
  | (.inl (.inr (x,y)),.first) => .diagonal x y
  | (.inl (.inr (x,y)),.second) => .grid (.west x ⟨y.val+1,by omega⟩)
  | (.inl (.inr (x,y)),.third) => .grid (.north ⟨x.val,by omega⟩ y)
  | (.inr i,.first) => .grid (boundaryAt hw hh i).toDart
  | (.inr i,.second) => .toApex (cycleNext i)
  | (.inr i,.third) => .fromApex i

def TDart.toIncidence {w h} (hw : 0<w) (hh : 0<h) : TDart w h → Incidence w h
  | .grid d => fromOld hw hh d.toFaceDart
  | .diagonal x y => (.inl (.inr (x,y)),.first)
  | .antidiagonal x y => (.inl (.inl (x,y)),.third)
  | .toApex i => (.inr (cyclePrev i),.second)
  | .fromApex i => (.inr i,.third)

theorem toDart_fromOld {w h} (hw : 0<w) (hh : 0<h) (d : FaceDart w h) :
    toDart hw hh (fromOld hw hh d)=.grid d.toDart := by
  cases d with
  | cell x y s =>
    have hs : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 := by omega
    rcases hs with hs | hs | hs | hs
    all_goals simp [fromOld,toDart,FaceDart.toDart,hs]
  | bottom x | right x | top x | left x =>
    simp only [fromOld,toDart,exteriorIndex]
    congr 1
    congr 1
    exact boundaryAt_index hw hh _ rfl

theorem fromOld_exterior {w h} (hw : 0<w) (hh : 0<h) (d : FaceDart w h)
    (hd : d.faceId=none) : fromOld hw hh d=(.inr (exteriorIndex hw hh d hd),.first) := by
  cases d <;> try rfl
  simp [FaceDart.faceId] at hd

theorem fromOld_boundaryAt {w h} (hw : 0<w) (hh : 0<h) (i : Fin (perimeter w h)) :
    fromOld hw hh (boundaryAt hw hh i)=(.inr i,.first) := by
  rw [fromOld_exterior hw hh _ (boundaryAt_exterior hw hh i)]
  congr 2
  apply Fin.ext
  exact boundaryIndex_at hw hh i

theorem TDart.incidence_roundtrip {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    toDart hw hh (d.toIncidence hw hh)=d := by
  cases d with
  | grid d =>
    change toDart hw hh (fromOld hw hh d.toFaceDart)=.grid d
    rw [toDart_fromOld,Dart.face_roundtrip]
  | diagonal x y | antidiagonal x y | fromApex i => rfl
  | toApex i => simp only [TDart.toIncidence,toDart,cycleNext_prev]

theorem dart_roundtrip {w h} (hw : 0<w) (hh : 0<h) (f : Incidence w h) :
    (toDart hw hh f).toIncidence hw hh=f := by
  obtain ⟨f,s⟩ := f
  cases f with
  | inl f =>
    cases f with
    | inl p | inr p =>
      obtain ⟨x,y⟩ := p
      cases s <;> simp [toDart,TDart.toIncidence,Dart.toFaceDart,fromOld,x.isLt,y.isLt,show (3 : Fin 4).val=3 by decide]
  | inr i =>
    cases s <;> simp only [toDart,TDart.toIncidence,FaceDart.dart_roundtrip,
      fromOld_boundaryAt,cyclePrev_next]

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
