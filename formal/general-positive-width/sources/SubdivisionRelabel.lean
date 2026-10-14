import SubdivisionRealization

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open PlaneGrid

/-- A source graph transported by a finite vertex numbering. -/
def reindexGraph {n} (G : Graph n) (R : FiniteCode (Fin n) n) : Graph n where
  Adj i j := G.Adj (R.decode i) (R.decode j)
  symm := G.symm
  loopless := fun i => G.loopless (R.decode i)

/-- Decoding is injective because encoding is its left inverse. -/
theorem reindex_decode_injective {n} (R : FiniteCode (Fin n) n) :
    Function.Injective R.decode := by
  intro i j h
  have hh := congrArg R.encode h
  simpa only [R.encode_decode] using hh

/-- Whether the new ordered edge agrees with the old source numbering. -/
def reindexForward {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) : Prop :=
  (R.decode e.low).val < (R.decode e.high).val

instance {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) : Decidable (reindexForward R e) :=
  inferInstanceAs (Decidable ((R.decode e.low).val < (R.decode e.high).val))

/-- Recover the unique old ordered edge, reversing its orientation if needed. -/
def reindexEdge {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) : OrderedEdge G :=
  if h : reindexForward R e then
    ⟨R.decode e.low,R.decode e.high,h,e.adjacent⟩
  else
    ⟨R.decode e.high,R.decode e.low,by
      have hn : (R.decode e.low).val ≠ (R.decode e.high).val := by
        intro he
        have he' := reindex_decode_injective R (Fin.ext he)
        have hv := congrArg Fin.val he'
        have ho := e.ordered
        omega
      change ¬ (R.decode e.low).val < (R.decode e.high).val at h
      omega,
      G.symm e.adjacent⟩

theorem reindexEdge_low_forward {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (h : reindexForward R e) :
    (reindexEdge R e).low=R.decode e.low := by
  simp only [reindexEdge,dite_eq_left h]

theorem reindexEdge_high_forward {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (h : reindexForward R e) :
    (reindexEdge R e).high=R.decode e.high := by
  simp only [reindexEdge,dite_eq_left h]

theorem reindexEdge_low_backward {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (h : ¬reindexForward R e) :
    (reindexEdge R e).low=R.decode e.high := by
  simp only [reindexEdge,dite_eq_right h]

theorem reindexEdge_high_backward {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (h : ¬reindexForward R e) :
    (reindexEdge R e).high=R.decode e.low := by
  simp only [reindexEdge,dite_eq_right h]

/-- Forgetting orientation does not identify two distinct new ordered edges. -/
theorem reindexEdge_injective {n} {G : Graph n} (R : FiniteCode (Fin n) n) :
    Function.Injective (reindexEdge (G := G) R) := by
  intro e f h
  have hl := congrArg OrderedEdge.low h
  have hh := congrArg OrderedEdge.high h
  by_cases he : reindexForward R e <;> by_cases hf : reindexForward R f
  · rw [reindexEdge_low_forward R e he,reindexEdge_low_forward R f hf] at hl
    rw [reindexEdge_high_forward R e he,reindexEdge_high_forward R f hf] at hh
    exact OrderedEdge.ext (reindex_decode_injective R hl) (reindex_decode_injective R hh)
  · rw [reindexEdge_low_forward R e he,reindexEdge_low_backward R f hf] at hl
    rw [reindexEdge_high_forward R e he,reindexEdge_high_backward R f hf] at hh
    have hl' := congrArg Fin.val (reindex_decode_injective R hl)
    have hh' := congrArg Fin.val (reindex_decode_injective R hh)
    have eo := e.ordered
    have fo := f.ordered
    omega
  · rw [reindexEdge_low_backward R e he,reindexEdge_low_forward R f hf] at hl
    rw [reindexEdge_high_backward R e he,reindexEdge_high_forward R f hf] at hh
    have hl' := congrArg Fin.val (reindex_decode_injective R hl)
    have hh' := congrArg Fin.val (reindex_decode_injective R hh)
    have eo := e.ordered
    have fo := f.ordered
    omega
  · rw [reindexEdge_low_backward R e he,reindexEdge_low_backward R f hf] at hl
    rw [reindexEdge_high_backward R e he,reindexEdge_high_backward R f hf] at hh
    exact OrderedEdge.ext (reindex_decode_injective R hh) (reindex_decode_injective R hl)

/-- Reverse positions on a finite route, including both endpoints. -/
def reversePosition (L : Nat) (i : Fin (L+1)) : Fin (L+1) :=
  ⟨L-i.val,by omega⟩

theorem reversePosition_zero (L : Nat) :
    reversePosition L ⟨0,by omega⟩=⟨L,by omega⟩ := by
  apply Fin.ext
  simp only [reversePosition,Nat.sub_zero]

theorem reversePosition_last (L : Nat) :
    reversePosition L ⟨L,by omega⟩=⟨0,by omega⟩ := by
  apply Fin.ext
  simp only [reversePosition,Nat.sub_self]

theorem reversePosition_injective (L : Nat) : Function.Injective (reversePosition L) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change L-i.val=L-j.val at hh
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem reversePosition_interior (L : Nat) (i : Fin (L+1))
    (h0 : 0<i.val) (hL : i.val<L) :
    0<(reversePosition L i).val ∧ (reversePosition L i).val<L := by
  dsimp only [reversePosition]
  omega

theorem Realization.reverse_step {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (e : OrderedEdge G) (i : Fin (S.length e)) :
    H.Adj (S.pointAt e (reversePosition (S.length e) ⟨i.val,by have := i.isLt; omega⟩))
      (S.pointAt e (reversePosition (S.length e) ⟨i.val+1,by have := i.isLt; omega⟩)) := by
  have hi := i.isLt
  let j : Fin (S.length e) := ⟨S.length e-(i.val+1),by omega⟩
  have hfirst : reversePosition (S.length e) ⟨i.val,by omega⟩=
      (⟨j.val+1,by have := j.isLt; omega⟩ : Fin (S.length e+1)) := by
    apply Fin.ext
    dsimp only [reversePosition,j]
    omega
  have hsecond : reversePosition (S.length e) ⟨i.val+1,by omega⟩=
      (⟨j.val,by have := j.isLt; omega⟩ : Fin (S.length e+1)) := by
    apply Fin.ext
    rfl
  rw [hfirst,hsecond]
  exact H.symm (S.step e j)

/-- The old route position corresponding to a position in the new orientation. -/
def reindexPosition {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (L : Nat) (i : Fin (L+1)) : Fin (L+1) :=
  if reindexForward R e then i else reversePosition L i

theorem reindexPosition_injective {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (L : Nat) :
    Function.Injective (reindexPosition R e L) := by
  by_cases h : reindexForward R e
  · intro i j he
    simpa only [reindexPosition,ite_eq_left h] using he
  · intro i j he
    apply reversePosition_injective L
    simpa only [reindexPosition,ite_eq_right h] using he

theorem reindexPosition_interior {n} {G : Graph n} (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) (L : Nat) (i : Fin (L+1))
    (h0 : 0<i.val) (hL : i.val<L) :
    0<(reindexPosition R e L i).val ∧ (reindexPosition R e L i).val<L := by
  by_cases h : reindexForward R e
  · simpa only [reindexPosition,ite_eq_left h] using And.intro h0 hL
  · simpa only [reindexPosition,ite_eq_right h] using reversePosition_interior L i h0 hL

/-- Relabel the source of an actual finite graph subdivision. The target
vertices and edges are unchanged; old routes are traversed in the orientation
forced by the new ordering. This assumes no geometric or width conclusion. -/
def Realization.reindex {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (R : FiniteCode (Fin n) n) :
    Realization (reindexGraph G R) H where
  length e := S.length (reindexEdge R e)
  positive e := S.positive (reindexEdge R e)
  point := S.point ∘ R.decode
  point_injective := by
    intro i j h
    exact reindex_decode_injective R (S.point_injective h)
  pointAt e i := S.pointAt (reindexEdge R e)
    (reindexPosition R e (S.length (reindexEdge R e)) i)
  first := by
    intro e
    by_cases h : reindexForward R e
    · simp only [reindexPosition,ite_eq_left h,S.first,reindexEdge_low_forward R e h,
        Function.comp_apply]
    · simp only [reindexPosition,ite_eq_right h,reversePosition_zero,S.last,
        reindexEdge_high_backward R e h,Function.comp_apply]
  last := by
    intro e
    by_cases h : reindexForward R e
    · simp only [reindexPosition,ite_eq_left h,S.last,reindexEdge_high_forward R e h,
        Function.comp_apply]
    · simp only [reindexPosition,ite_eq_right h,reversePosition_last,S.first,
        reindexEdge_low_backward R e h,Function.comp_apply]
  path_injective := by
    intro e i j h
    exact reindexPosition_injective R e _ (S.path_injective (reindexEdge R e) h)
  step := by
    intro e i
    by_cases h : reindexForward R e
    · simpa only [reindexPosition,ite_eq_left h] using S.step (reindexEdge R e) i
    · simpa only [reindexPosition,ite_eq_right h] using S.reverse_step (reindexEdge R e) i
  avoids := by
    intro e i h0 hL v
    obtain ⟨h0',hL'⟩ := reindexPosition_interior R e _ i h0 hL
    exact S.avoids (reindexEdge R e) (reindexPosition R e _ i) h0' hL' (R.decode v)
  disjoint := by
    intro e f i j hi0 hiL hj0 hjL h
    obtain ⟨hi0',hiL'⟩ := reindexPosition_interior R e _ i hi0 hiL
    obtain ⟨hj0',hjL'⟩ := reindexPosition_interior R f _ j hj0 hjL
    exact reindexEdge_injective R (S.disjoint (reindexEdge R e) (reindexEdge R f)
      (reindexPosition R e _ i) (reindexPosition R f _ j) hi0' hiL' hj0' hjL' h)

theorem Realization.reindex_point {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (R : FiniteCode (Fin n) n) (i : Fin n) :
    (S.reindex R).point i=S.point (R.decode i) := rfl

theorem Realization.reindex_length {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (R : FiniteCode (Fin n) n)
    (e : OrderedEdge (reindexGraph G R)) :
    (S.reindex R).length e=S.length (reindexEdge R e) := rfl

end StackSorting.GraphWidth.UCurve.SubdivisionTree
