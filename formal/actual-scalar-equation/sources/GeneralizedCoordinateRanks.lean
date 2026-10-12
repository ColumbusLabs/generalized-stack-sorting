import GeneralizedDecoratedSemantics

/-! Physical ranks of maximum-insertion coordinates. This identifies literal
coordinate decoding with numerical counts of smaller labels above each token. -/
namespace StackSorting.Generalized.Coordinates
open List

/-- Number of smaller labels preceding the first occurrence of a token. -/
def rankSlot : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, v => if x = v then 0 else (if x < v then 1 else 0) + rankSlot xs v

def rankWord (physical : List Nat) (next length : Nat) : List Nat :=
  (List.range' next length).map (rankSlot physical)

theorem rankSlot_insert_larger {slot x v : Nat} {held after : List Nat}
    (hi : insertAt? slot x held = some after) (hv : v < x) :
    rankSlot after v = rankSlot held v := by
  induction slot generalizing held after with
  | zero =>
    have he : after = x :: held := by simpa [insertAt?] using hi.symm
    simp [he, rankSlot, Nat.ne_of_gt hv, Nat.not_lt.mpr (Nat.le_of_lt hv)]
  | succ slot ih =>
    cases held with
    | nil => simp [insertAt?] at hi
    | cons head held =>
      cases ht : insertAt? slot x held with
      | none => simp [insertAt?, ht] at hi
      | some tail =>
        have he : after = head :: tail := by simpa [insertAt?, ht] using hi.symm
        simp [he, rankSlot, ih ht]

theorem rankSlot_insert_self {slot x : Nat} {held after : List Nat}
    (hi : insertAt? slot x held = some after)
    (old : ∀ y ∈ held, y < x) : rankSlot after x = slot := by
  induction slot generalizing held after with
  | zero =>
    have he : after = x :: held := by simpa [insertAt?] using hi.symm
    simp [he, rankSlot]
  | succ slot ih =>
    cases held with
    | nil => simp [insertAt?] at hi
    | cons head held =>
      cases ht : insertAt? slot x held with
      | none => simp [insertAt?, ht] at hi
      | some tail =>
        have he : after = head :: tail := by simpa [insertAt?, ht] using hi.symm
        have hh := old head (by simp)
        have ho : ∀ y ∈ held, y < x := fun y hy => old y (by simp [hy])
        simp [he, rankSlot, Nat.ne_of_lt hh, hh, ih ht ho, Nat.add_comm]

theorem rankSlot_build_old {next v : Nat} {digits held final : List Nat}
    (hb : build next digits held = some final) (hv : v < next) :
    rankSlot final v = rankSlot held v := by
  induction digits generalizing next held with
  | nil =>
    have he : final = held := by simpa [build] using hb.symm
    simp [he]
  | cons slot digits ih =>
    cases hi : insertAt? slot next held with
    | none => simp [build, hi] at hb
    | some after =>
      have ht : build (next+1) digits after = some final := by simpa [build, hi] using hb
      exact (ih ht (by omega)).trans (rankSlot_insert_larger hi hv)

theorem build_eq_rankWord {next : Nat} {digits held final : List Nat}
    (hb : build next digits held = some final)
    (old : ∀ y ∈ held, y < next) : digits = rankWord final next digits.length := by
  induction digits generalizing next held with
  | nil => simp [rankWord]
  | cons slot digits ih =>
    cases hi : insertAt? slot next held with
    | none => simp [build, hi] at hb
    | some after =>
      have ht : build (next+1) digits after = some final := by simpa [build, hi] using hb
      have hhead : rankSlot final next = slot :=
        (rankSlot_build_old ht (by omega)).trans (rankSlot_insert_self hi old)
      have hn : ∀ y ∈ after, y < next+1 := by
        obtain ⟨pre, post, he, _, ha⟩ := insertAt_split slot next held after hi
        subst after
        intro y hy
        simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | rfl | hy
        · have ho := old y (by simp [he, hy]); omega
        · omega
        · have ho := old y (by simp [he, hy]); omega
      simp only [rankWord, List.length_cons, List.range'_succ, List.map_cons, hhead]
      exact congrArg (slot :: ·) (ih ht hn)

theorem Decodes.eq_rankWord {digits physical : List Nat}
    (h : Decodes digits physical) : digits = rankWord physical 1 digits.length :=
  build_eq_rankWord h (by simp)

/-- Any distinct physical order of the first h labels has genuine coordinates.
This uses insertion of the actual maximum in its literal physical position. -/
theorem decodes_of_permutation {h : Nat} {physical : List Nat}
    (hp : physical.Perm (List.range' 1 h)) :
    ∃ digits, digits.length = h ∧ Decodes digits physical := by
  induction h generalizing physical with
  | zero =>
    have he : physical = [] := List.perm_nil.mp (by simpa using hp)
    exact ⟨[], rfl, by simp [Decodes, build, he]⟩
  | succ h ih =>
    have hm : h+1 ∈ physical := hp.mem_iff.mpr (by simp only [List.mem_range'_1]; omega)
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    have ht : (pre ++ post).Perm (List.range' 1 h) := by
      have hr : List.range' 1 (h+1) = List.range' 1 h ++ [h+1] := by
        simpa [Nat.add_comm] using (List.range'_concat (s := 1) (n := h) (step := 1))
      have hfull : ((h+1) :: (pre ++ post)).Perm ((h+1) :: List.range' 1 h) := by
        have hmiddle : ((h+1) :: (pre ++ post)).Perm physical := by
          rw [he]
          exact (List.perm_middle (a := h+1) (l₁ := pre) (l₂ := post)).symm
        exact hmiddle.trans (hp.trans (by rw [hr]; simp))
      exact List.Perm.cons_inv hfull
    obtain ⟨digits, hlen, hd⟩ := ih ht
    refine ⟨digits ++ [pre.length], by simp [hlen], ?_⟩
    unfold Decodes at *
    rw [build_append, hd]
    simp [build, hlen, he, insertAt_prefix, Nat.add_comm]

/-- Rank extraction exactly characterizes the physical representation of any
factor language. No reachability or fixed-height hypothesis is involved. -/
theorem represents_iff_rankWord (state : Decorated.State) (physical : List Nat) :
    Decorated.Represents state physical ↔
      physical.Perm (List.range' 1 (Decorated.height state)) ∧
      Decorated.denotes state (rankWord physical 1 (Decorated.height state)) := by
  constructor
  · rintro ⟨digits, hd, hp⟩
    have hlen := Decorated.denotes_length hd
    refine ⟨by simpa [hlen] using hp.permutation, ?_⟩
    rw [← hlen, ← hp.eq_rankWord]
    exact hd
  · rintro ⟨hp, hd⟩
    obtain ⟨digits, hlen, hdec⟩ := decodes_of_permutation hp
    have he : digits = rankWord physical 1 (Decorated.height state) := by
      simpa [hlen] using hdec.eq_rankWord
    exact ⟨digits, he.symm ▸ hd, hdec⟩

#print axioms decodes_of_permutation
#print axioms represents_iff_rankWord
end StackSorting.Generalized.Coordinates
