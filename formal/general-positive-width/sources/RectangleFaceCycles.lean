import FiniteCycles

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def FaceDart.faceNext {w h} (hw : 0 < w) (hh : 0 < h) : FaceDart w h → FaceDart w h
  | .cell x y side => .cell x y (cycleNext side)
  | .bottom x => if hx : x.val+1 < w then .bottom ⟨x.val+1,hx⟩ else .right ⟨h-1,by omega⟩
  | .left y => if hy : y.val+1 < h then .left ⟨y.val+1,hy⟩ else .bottom ⟨0,hw⟩
  | .top x => if hx : 0 < x.val then .top ⟨x.val-1,by omega⟩ else .left ⟨0,hh⟩
  | .right y => if hy : 0 < y.val then .right ⟨y.val-1,by omega⟩ else .top ⟨w-1,by omega⟩

def FaceDart.facePrev {w h} (hw : 0 < w) (hh : 0 < h) : FaceDart w h → FaceDart w h
  | .cell x y side => .cell x y (cyclePrev side)
  | .bottom x => if hx : 0 < x.val then .bottom ⟨x.val-1,by omega⟩ else .left ⟨h-1,by omega⟩
  | .left y => if hy : 0 < y.val then .left ⟨y.val-1,by omega⟩ else .top ⟨0,hw⟩
  | .top x => if hx : x.val+1 < w then .top ⟨x.val+1,hx⟩ else .right ⟨0,hh⟩
  | .right y => if hy : y.val+1 < h then .right ⟨y.val+1,hy⟩ else .bottom ⟨w-1,by omega⟩

theorem FaceDart.facePrev_next {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h) :
    (d.faceNext hw hh).facePrev hw hh = d := by
  have hw' : w-1+1=w := by omega
  have hh' : h-1+1=h := by omega
  cases d with
  | cell x y side => simp [FaceDart.faceNext,FaceDart.facePrev,cyclePrev_next]
  | bottom x =>
    have hx := x.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.facePrev,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | left y =>
    have hy := y.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.facePrev,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | top x =>
    have hx := x.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.facePrev,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | right y =>
    have hy := y.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.facePrev,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega

theorem FaceDart.faceNext_prev {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h) :
    (d.facePrev hw hh).faceNext hw hh = d := by
  have hw' : w-1+1=w := by omega
  have hh' : h-1+1=h := by omega
  cases d with
  | cell x y side => simp [FaceDart.faceNext,FaceDart.facePrev,cycleNext_prev]
  | bottom x =>
    have hx := x.isLt
    simp only [FaceDart.facePrev]
    split <;> simp_all [FaceDart.faceNext,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | left y =>
    have hy := y.isLt
    simp only [FaceDart.facePrev]
    split <;> simp_all [FaceDart.faceNext,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | top x =>
    have hx := x.isLt
    simp only [FaceDart.facePrev]
    split <;> simp_all [FaceDart.faceNext,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega
  | right y =>
    have hy := y.isLt
    simp only [FaceDart.facePrev]
    split <;> simp_all [FaceDart.faceNext,Fin.ext_iff]
    all_goals (try split) <;> (try simp_all [Fin.ext_iff]) <;> omega

/-- Cells carry their exact coordinates; all boundary darts are exterior. -/
def FaceDart.faceId {w h} : FaceDart w h → Option (Fin w × Fin h)
  | .cell x y _ => some (x,y)
  | .bottom _ | .left _ | .top _ | .right _ => none

theorem FaceDart.faceId_next {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h) :
    (d.faceNext hw hh).faceId = d.faceId := by
  cases d <;> simp only [FaceDart.faceNext]
  · rfl
  all_goals split <;> rfl

theorem FaceDart.next_starts_at_head {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h) :
    (d.faceNext hw hh).toDart.tail = d.toDart.head := by
  have hw' : w-1+1=w := by omega
  have hh' : h-1+1=h := by omega
  cases d with
  | cell x y side =>
    have hs : side.val=0 ∨ side.val=1 ∨ side.val=2 ∨ side.val=3 := by omega
    rcases hs with hs | hs | hs | hs
    all_goals simp_all [FaceDart.faceNext,cycleNext,FaceDart.toDart,Dart.tail,Dart.head,Dart.reverse,show (3 : Fin 4).val=3 by decide]
  | bottom x =>
    have hx := x.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.toDart,Dart.tail,Dart.head,Dart.reverse] <;> omega
  | left y =>
    have hy := y.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.toDart,Dart.tail,Dart.head,Dart.reverse] <;> omega
  | top x =>
    have hx := x.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.toDart,Dart.tail,Dart.head,Dart.reverse] <;> omega
  | right y =>
    have hy := y.isLt
    simp only [FaceDart.faceNext]
    split <;> simp_all [FaceDart.toDart,Dart.tail,Dart.head,Dart.reverse] <;> omega

end StackSorting.GraphWidth.UCurve.PlaneGrid
