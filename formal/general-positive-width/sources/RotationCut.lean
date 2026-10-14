import FiniteOrbitCounts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

/-- Forward iteration, independent of any orbit/cycle certificate. -/
def rotationIter {α : Type} (rot : α → α) : Nat → α → α
  | 0, d => d
  | n+1, d => rot (rotationIter rot n d)

@[simp] theorem rotationIter_zero {α} (rot : α → α) (d : α) :
    rotationIter rot 0 d = d := rfl

@[simp] theorem rotationIter_succ {α} (rot : α → α) (n : Nat) (d : α) :
    rotationIter rot (n+1) d = rot (rotationIter rot n d) := rfl

theorem rotationIter_add {α} (rot : α → α) (m n : Nat) (d : α) :
    rotationIter rot (m+n) d = rotationIter rot m (rotationIter rot n d) := by
  induction m with
  | zero => simp only [Nat.zero_add, rotationIter_zero]
  | succ m ih => simpa only [Nat.succ_add, rotationIter_succ] using congrArg rot ih

theorem rotationIter_injective {α} {rot : α → α} (hr : Function.Injective rot)
    (n : Nat) : Function.Injective (rotationIter rot n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => ih (hr h)

/-- Pigeonhole for an actual finite encoding: n+1 successive entries must repeat. -/
theorem FiniteCode.sequence_repeats {α n} (C : FiniteCode α n) (s : Nat → α) :
    ∃ i j : Nat, i < j ∧ j ≤ n ∧ s i = s j := by
  letI : DecidableEq α := fun a b => decidable_of_iff (C.encode a = C.encode b)
    ⟨C.injective,congrArg C.encode⟩
  by_cases hex : ∃ i j : Fin (n+1), i.val < j.val ∧ s i.val = s j.val
  · obtain ⟨i,j,hij,he⟩ := hex
    exact ⟨i.val,j.val,hij,by have := j.isLt; omega,he⟩
  let xs := (List.range (n+1)).map (fun i => C.encode (s i))
  have hnodup : xs.Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj he
    have hi' : i < n+1 := by simpa only [xs,List.length_map,List.length_range] using hi
    have hj' : j < n+1 := by simpa only [xs,List.length_map,List.length_range] using hj
    have he' : C.encode (s i) = C.encode (s j) := by
      simpa only [xs,List.getElem_map,List.getElem_range] using he
    have hs := C.injective he'
    have hij : ¬i<j := fun h => hex ⟨⟨i,hi'⟩,⟨j,hj'⟩,h,hs⟩
    have hji : ¬j<i := fun h => hex ⟨⟨j,hj'⟩,⟨i,hi'⟩,h,hs.symm⟩
    omega
  have hlength := hnodup.length_le_of_subset (l₂ := List.finRange n)
    (fun x _ => List.mem_finRange x)
  simp only [xs,List.length_map,List.length_range,List.length_finRange] at hlength
  omega

/-- Finite injectivity gives a positive period, bounded by the actual cardinality.
In particular, every bijection has this property. -/
theorem FiniteCode.positive_rotation_period {α n} (C : FiniteCode α n)
    (rot : α → α) (hr : Function.Injective rot) (d : α) :
    ∃ p : Nat, 0 < p ∧ p ≤ n ∧ rotationIter rot p d = d := by
  obtain ⟨i,j,hij,hjn,he⟩ := C.sequence_repeats (fun k => rotationIter rot k d)
  refine ⟨j-i,by omega,by omega,?_⟩
  apply rotationIter_injective hr i
  rw [←rotationIter_add]
  have hs : i+(j-i)=j := by omega
  rw [hs]
  exact he.symm

/-- Every forward iterate belongs to the undirected permutation orbit. -/
theorem rotationIter_walk {α} (rot : α → α) (n : Nat) (d : α) :
    Walk (OrbitStep rot) (fun _ => True) d (rotationIter rot n d) := by
  induction n with
  | zero => exact .refl trivial
  | succ n ih => exact ih.trans (.step trivial (Or.inl rfl) (.refl trivial))

/-- A first change along a finite forward trajectory retains the starting color.
No periodicity or finiteness hypothesis is needed for this path lemma. -/
theorem rotationIter_first_color_change {α} (rot : α → α) (color : α → Bool)
    (m : Nat) (a : α) (h : color a ≠ color (rotationIter rot m a)) :
    ∃ k : Nat, k < m ∧ color (rotationIter rot k a) = color a ∧
      color (rotationIter rot k a) ≠ color (rot (rotationIter rot k a)) := by
  induction m with
  | zero => exact False.elim (h rfl)
  | succ m ih =>
    by_cases hm : color a = color (rotationIter rot m a)
    · refine ⟨m,by omega,hm.symm,?_⟩
      intro he
      exact h (hm.trans he)
    · obtain ⟨k,hk,hc,he⟩ := ih hm
      exact ⟨k,by omega,hc,he⟩

/-- A crossing of a two-color cut in a finite permutation orbit has another
crossing in that same orbit. Finiteness is witnessed by an actual FiniteCode;
no cycle, connectedness, planarity, or width certificate is assumed. -/
theorem rotation_cut_has_second_crossing {α n} (C : FiniteCode α n)
    (rot : α → α) (hr : Function.Injective rot) (color : α → Bool) (d : α)
    (hd : color d ≠ color (rot d)) :
    ∃ e : α, e ≠ d ∧ Walk (OrbitStep rot) (fun _ => True) d e ∧
      color e = color (rot d) ∧ color e ≠ color (rot e) := by
  obtain ⟨p,hp,_,hperiod⟩ := C.positive_rotation_period rot hr d
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hreturn : rotationIter rot m (rot d) = d := by
    have h := rotationIter_add rot m 1 d
    simpa only [rotationIter_succ,rotationIter_zero] using h.symm.trans hperiod
  have hc : color (rot d) ≠ color (rotationIter rot m (rot d)) := by
    rw [hreturn]
    exact Ne.symm hd
  obtain ⟨k,_,he,hcross⟩ := rotationIter_first_color_change rot color m (rot d) hc
  refine ⟨rotationIter rot k (rot d),?_,?_,he,hcross⟩
  · intro heq
    rw [heq] at he
    exact hd he
  · have hs : Walk (OrbitStep rot) (fun _ => True) d (rot d) :=
      .step trivial (Or.inl rfl) (.refl trivial)
    exact hs.trans (rotationIter_walk rot k (rot d))

/-- A rotation-invariant tail is constant throughout each undirected orbit. -/
theorem orbit_walk_preserves_tail {α β : Type} {rot : α → α} (tail : α → β)
    (ht : ∀ d, tail (rot d) = tail d) {d e : α}
    (h : Walk (OrbitStep rot) (fun _ => True) d e) : tail e = tail d := by
  induction h with
  | refl => rfl
  | @step a b c _ hab _ ih =>
    have he : tail b = tail a := by
      obtain h | h := hab
      · rw [←h]; exact ht a
      · exact (ht b).symm.trans (congrArg tail h)
    exact ih.trans he

/-- The second crossing can be chosen at the same tail when rotation preserves
that tail. The tail hypothesis is the only extra local incidence requirement. -/
theorem rotation_cut_has_second_crossing_same_tail {α β : Type} {n}
    (C : FiniteCode α n) (rot : α → α) (hr : Function.Injective rot)
    (tail : α → β) (ht : ∀ d, tail (rot d) = tail d)
    (color : α → Bool) (d : α) (hd : color d ≠ color (rot d)) :
    ∃ e : α, e ≠ d ∧ tail e = tail d ∧
      Walk (OrbitStep rot) (fun _ => True) d e ∧ color e ≠ color (rot e) := by
  obtain ⟨e,hed,hw,_,hc⟩ := rotation_cut_has_second_crossing C rot hr color d hd
  exact ⟨e,hed,orbit_walk_preserves_tail tail ht hw,hw,hc⟩

/-- Local incidence form: every cut crossing has a distinct same-tail crossing. -/
theorem finite_rotation_cut_continuation {α β : Type} {n}
    (C : FiniteCode α n) (rot : α → α) (hr : Function.Injective rot)
    (tail : α → β) (ht : ∀ d, tail (rot d) = tail d)
    (color : α → Bool) :
    ∀ d, color d ≠ color (rot d) →
      ∃ e, tail e = tail d ∧ e ≠ d ∧ color e ≠ color (rot e) := by
  intro d hd
  obtain ⟨e,he,htail,_,hc⟩ :=
    rotation_cut_has_second_crossing_same_tail C rot hr tail ht color d hd
  exact ⟨e,htail,he,hc⟩

/-- A proved inverse law suffices to discharge the injectivity premise. -/
theorem finite_rotation_cut_continuation_of_inverse {α β : Type} {n}
    (C : FiniteCode α n) (rot inv : α → α) (hi : ∀ d, inv (rot d) = d)
    (tail : α → β) (ht : ∀ d, tail (rot d) = tail d)
    (color : α → Bool) :
    ∀ d, color d ≠ color (rot d) →
      ∃ e, tail e = tail d ∧ e ≠ d ∧ color e ≠ color (rot e) := by
  apply finite_rotation_cut_continuation C rot ?_ tail ht color
  intro a b h
  exact (hi a).symm.trans ((congrArg inv h).trans (hi b))

end StackSorting.GraphWidth.UCurve.PlaneGrid
