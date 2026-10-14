import RectangleBoundary

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def OrbitStep {α : Type} (f : α → α) (a b : α) : Prop := f a = b ∨ f b = a

theorem orbitStep_symm {α} (f : α → α) {a b : α} (h : OrbitStep f a b) : OrbitStep f b a :=
  h.symm

theorem cycle_walk_to_zero {n} (hn : 0 < n) (i : Fin n) :
    Walk (OrbitStep (@cycleNext n)) (fun _ => True) i ⟨0,hn⟩ := by
  by_cases hi : i.val=0
  · have he : i = ⟨0,hn⟩ := Fin.ext hi
    subst i
    exact .refl trivial
  · let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : j.val < i.val := by dsimp [j]; omega
    have hnext : cycleNext j=i := by
      apply Fin.ext
      have hlt : j.val+1<n := by dsimp [j]; omega
      rw [cycleNext_at_successor j hlt]
      dsimp [j]
      omega
    exact .step trivial (Or.inr hnext) (cycle_walk_to_zero hn j)
termination_by i.val

theorem cycle_connected {n} (hn : 0 < n) (i j : Fin n) :
    Walk (OrbitStep (@cycleNext n)) (fun _ => True) i j :=
  (cycle_walk_to_zero hn i).trans ((cycle_walk_to_zero hn j).reverse (orbitStep_symm _))

theorem walk_map {α β : Type} {adj : α → α → Prop} {adj' : β → β → Prop}
    (f : α → β) (hm : ∀ {a b}, adj a b → adj' (f a) (f b)) {a b}
    (h : Walk adj (fun _ => True) a b) : Walk adj' (fun _ => True) (f a) (f b) := by
  induction h with
  | refl => exact .refl trivial
  | step _ he _ ih => exact .step trivial (hm he) ih

theorem cycle_image_connected {α : Type} {n} (hn : 0 < n) (f : α → α) (g : Fin n → α)
    (hg : ∀ i, g (cycleNext i) = f (g i)) (i j : Fin n) :
    Walk (OrbitStep f) (fun _ => True) (g i) (g j) := by
  apply walk_map g (h := cycle_connected hn i j)
  intro a b hab
  obtain h | h := hab
  · exact Or.inl ((hg a).symm.trans (congrArg g h))
  · exact Or.inr ((hg b).symm.trans (congrArg g h))

theorem FaceDart.cell_face_connected {w h} (hw : 0 < w) (hh : 0 < h)
    (x : Fin w) (y : Fin h) (a b : Fin 4) :
    Walk (OrbitStep (FaceDart.faceNext hw hh)) (fun _ => True) (.cell x y a) (.cell x y b) :=
  cycle_image_connected (by decide) (FaceDart.faceNext hw hh) (.cell x y) (fun _ => rfl) a b

theorem FaceDart.exterior_connected {w h} (hw : 0 < w) (hh : 0 < h)
    (d e : FaceDart w h) (hd : d.faceId=none) (he : e.faceId=none) :
    Walk (OrbitStep (FaceDart.faceNext hw hh)) (fun _ => True) d e := by
  let i : Fin (perimeter w h) := ⟨boundaryIndex d,boundaryIndex_lt hw hh d hd⟩
  let j : Fin (perimeter w h) := ⟨boundaryIndex e,boundaryIndex_lt hw hh e he⟩
  have h := cycle_image_connected (n := perimeter w h) (by unfold perimeter; omega)
    (FaceDart.faceNext hw hh) (boundaryAt hw hh) (fun k => (boundaryAt_next hw hh k).symm) i j
  simpa only [i,j,boundaryAt_index hw hh d hd,boundaryAt_index hw hh e he] using h

theorem FaceDart.same_face_connected {w h} (hw : 0 < w) (hh : 0 < h)
    (d e : FaceDart w h) (he : d.faceId=e.faceId) :
    Walk (OrbitStep (FaceDart.faceNext hw hh)) (fun _ => True) d e := by
  by_cases hd : d.faceId=none
  · exact FaceDart.exterior_connected hw hh d e hd (he.symm.trans hd)
  · cases d <;> simp only [FaceDart.faceId] at hd he
    case cell x y a =>
      cases e <;> simp only [FaceDart.faceId] at he
      case cell x' y' b =>
        have hp : x=x' ∧ y=y' := by simpa using he
        obtain ⟨rfl,rfl⟩ := hp
        exact FaceDart.cell_face_connected hw hh _ _ a b
      all_goals contradiction
    all_goals contradiction

theorem FaceDart.connected_same_face {w h} (hw : 0 < w) (hh : 0 < h)
    {d e : FaceDart w h}
    (he : Walk (OrbitStep (FaceDart.faceNext hw hh)) (fun _ => True) d e) :
    d.faceId=e.faceId := by
  induction he with
  | refl => rfl
  | @step a b c _ h _ ih =>
    have hs : a.faceId = b.faceId := by
      obtain h | h := h
      · exact (FaceDart.faceId_next hw hh _).symm.trans (congrArg FaceDart.faceId h)
      · exact (congrArg FaceDart.faceId h).symm.trans (FaceDart.faceId_next hw hh _)
    exact hs.trans ih

/-- The actual face-permutation components are exactly one for each cell
and one common exterior component. No Euler arithmetic is used to assume
this component classification. -/
theorem FaceDart.face_orbits_exact {w h} (hw : 0 < w) (hh : 0 < h) (d e : FaceDart w h) :
    Walk (OrbitStep (FaceDart.faceNext hw hh)) (fun _ => True) d e ↔ d.faceId=e.faceId :=
  ⟨FaceDart.connected_same_face hw hh,FaceDart.same_face_connected hw hh d e⟩

end StackSorting.GraphWidth.UCurve.PlaneGrid
