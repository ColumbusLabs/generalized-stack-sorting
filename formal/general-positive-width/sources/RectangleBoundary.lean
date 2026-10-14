import RectangleRotation

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def perimeter (w h : Nat) : Nat := w+h+w+h

def boundaryAt {w h} (_hw : 0 < w) (_hh : 0 < h) (i : Fin (perimeter w h)) : FaceDart w h :=
  if h1 : i.val < w then .bottom ⟨i.val,h1⟩
  else if h2 : i.val < w+h then .right ⟨w+h-1-i.val,by omega⟩
  else if h3 : i.val < w+h+w then .top ⟨w+h+w-1-i.val,by omega⟩
  else .left ⟨i.val-(w+h+w),by have := i.isLt; unfold perimeter at *; omega⟩

def boundaryIndex {w h} : FaceDart w h → Nat
  | .cell _ _ _ => 0
  | .bottom x => x.val
  | .right y => w+(h-1-y.val)
  | .top x => w+h+(w-1-x.val)
  | .left y => w+h+w+y.val

theorem boundaryAt_exterior {w h} (hw : 0 < w) (hh : 0 < h) (i : Fin (perimeter w h)) :
    (boundaryAt hw hh i).faceId = none := by
  unfold boundaryAt
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem boundaryIndex_lt {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h)
    (hd : d.faceId = none) : boundaryIndex d < perimeter w h := by
  cases d with
  | cell x y s => simp [FaceDart.faceId] at hd
  | bottom x => have := x.isLt; simp only [boundaryIndex,perimeter]; omega
  | right y => have := y.isLt; simp only [boundaryIndex,perimeter]; omega
  | top x => have := x.isLt; simp only [boundaryIndex,perimeter]; omega
  | left y => have := y.isLt; simp only [boundaryIndex,perimeter]; omega

theorem boundaryIndex_at {w h} (hw : 0 < w) (hh : 0 < h) (i : Fin (perimeter w h)) :
    boundaryIndex (boundaryAt hw hh i) = i.val := by
  have hi := i.isLt
  unfold perimeter at hi
  unfold boundaryAt
  split
  · rfl
  · split
    · simp only [boundaryIndex]; omega
    · split <;> simp only [boundaryIndex] <;> omega

theorem boundaryAt_index {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h)
    (hd : d.faceId = none) :
    boundaryAt hw hh ⟨boundaryIndex d,boundaryIndex_lt hw hh d hd⟩ = d := by
  cases d with
  | cell x y s => simp [FaceDart.faceId] at hd
  | bottom x =>
    dsimp only [boundaryAt,boundaryIndex]
    rw [dite_eq_left x.isLt]
  | right y =>
    have hy := y.isLt
    have h1 : ¬ w+(h-1-y.val)<w := by omega
    have h2 : w+(h-1-y.val)<w+h := by omega
    dsimp only [boundaryAt,boundaryIndex]
    simp only [dite_eq_right h1,dite_eq_left h2]
    apply congrArg FaceDart.right
    apply Fin.ext
    change w+h-1-(w+(h-1-y.val))=y.val
    omega
  | top x =>
    have hx := x.isLt
    have h1 : ¬ w+h+(w-1-x.val)<w := by omega
    have h2 : ¬ w+h+(w-1-x.val)<w+h := by omega
    have h3 : w+h+(w-1-x.val)<w+h+w := by omega
    dsimp only [boundaryAt,boundaryIndex]
    simp only [dite_eq_right h1,dite_eq_right h2,dite_eq_left h3]
    apply congrArg FaceDart.top
    apply Fin.ext
    change w+h+w-1-(w+h+(w-1-x.val))=x.val
    omega
  | left y =>
    have hy := y.isLt
    have h1 : ¬ w+h+w+y.val<w := by omega
    have h2 : ¬ w+h+w+y.val<w+h := by omega
    have h3 : ¬ w+h+w+y.val<w+h+w := by omega
    dsimp only [boundaryAt,boundaryIndex]
    simp only [dite_eq_right h1,dite_eq_right h2,dite_eq_right h3]
    apply congrArg FaceDart.left
    apply Fin.ext
    change w+h+w+y.val-(w+h+w)=y.val
    omega

theorem exterior_index_injective {w h} (hw : 0 < w) (hh : 0 < h)
    {d e : FaceDart w h} (hd : d.faceId=none) (he : e.faceId=none)
    (hi : boundaryIndex d=boundaryIndex e) : d=e := by
  have hj : (⟨boundaryIndex d,boundaryIndex_lt hw hh d hd⟩ : Fin (perimeter w h)) =
      ⟨boundaryIndex e,boundaryIndex_lt hw hh e he⟩ := Fin.ext hi
  have h := congrArg (boundaryAt hw hh) hj
  simpa only [boundaryAt_index hw hh d hd,boundaryAt_index hw hh e he] using h

theorem boundaryIndex_next {w h} (hw : 0 < w) (hh : 0 < h) (d : FaceDart w h)
    (hd : d.faceId=none) :
    boundaryIndex (d.faceNext hw hh) =
      if boundaryIndex d+1 < perimeter w h then boundaryIndex d+1 else 0 := by
  split <;> cases d
  all_goals try { simp [FaceDart.faceId] at hd }
  all_goals simp only [FaceDart.faceNext]
  all_goals split <;> dsimp only [boundaryIndex,perimeter] at * <;> omega

theorem boundaryAt_next {w h} (hw : 0 < w) (hh : 0 < h) (i : Fin (perimeter w h)) :
    (boundaryAt hw hh i).faceNext hw hh = boundaryAt hw hh (cycleNext i) := by
  apply exterior_index_injective hw hh
  · rw [FaceDart.faceId_next]; exact boundaryAt_exterior hw hh i
  · exact boundaryAt_exterior hw hh (cycleNext i)
  · rw [boundaryIndex_next hw hh _ (boundaryAt_exterior hw hh i),boundaryIndex_at,
      boundaryIndex_at]
    simp only [cycleNext]
    split <;> rfl

end StackSorting.GraphWidth.UCurve.PlaneGrid
