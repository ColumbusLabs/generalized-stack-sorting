import GeneralizedUnarySuffix
import GeneralizedDecoratedTransitions

/-! Every individual held rank of a unary state has its exact coordinate
successor. The selected rank is kept as an index, even when two successor
languages happen to agree. -/
namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates ExceptionalSuffix

theorem ThreeLetters.height {state : State} (ht : ThreeLetters state) :
    height state = state.length := by
  induction state with
  | nil => rfl
  | cons factor rest ih =>
    have hh : factor.height = 1 := by
      rcases ht factor (by simp) with rfl | rfl | rfl <;> rfl
    simp [Decorated.height, hh, show (rest.map Factor.height).sum = rest.length from ih ht.tail, Nat.add_comm]

theorem denotes_unary_split {pre rest : State} {factor : Factor}
    (ht : ThreeLetters pre) (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    {earlier later : List Nat} {digit : Nat} (hlen : earlier.length = pre.length) :
    denotes (pre ++ factor :: rest) (earlier ++ digit :: later) ↔
      denotes pre earlier ∧ factor.denotes [digit] ∧ denotes rest later := by
  constructor
  · intro hd
    obtain ⟨front, tail, hfront, htail, he⟩ := (denotes_append pre _ _).mp hd
    have hlen' : earlier.length = front.length := by
      rw [denotes_length hfront, ht.height, hlen]
    obtain ⟨hfrontEq, htailEq⟩ := List.append_inj he hlen'
    subst front
    obtain ⟨singleton, after, hs, ha, he'⟩ := htail
    have hlength : singleton.length = 1 := by
      have hh : factor.height = 1 := by rcases hf with rfl | rfl | rfl <;> rfl
      exact (Factor.denotes_length hs).trans hh
    have hx : [digit] ++ later = singleton ++ after := htailEq.trans he'
    obtain ⟨hse, hae⟩ := List.append_inj hx (by simpa using hlength.symm)
    subst singleton
    subst after
    exact ⟨hfront, hs, ha⟩
  · rintro ⟨hpre, hf, hrest⟩
    exact (denotes_append pre _ _).mpr ⟨earlier, digit :: later, hpre,
      ⟨[digit], later, hf, hrest, rfl⟩, rfl⟩

theorem scan_output_eq_erase {marked : Nat} {digits output : List Nat}
    (hs : scan 3 marked digits = some output) : output = eraseSuffix marked digits := by
  rw [scan_eq] at hs
  split at hs
  · exact (Option.some.inj hs).symm
  · cases hs

/-- Unbounded exact local deletion language at an arbitrary unary prefix. -/
theorem popImage_unary_split {pre rest : State} {factor : Factor}
    (ht : ThreeLetters pre) (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (output : List Nat) :
    PopImage (pre ++ factor :: rest) pre.length output ↔
      ∃ before after digit, denotes pre before ∧ factor.denotes [digit] ∧
        ScanImage digit rest after ∧ output = before ++ after := by
  constructor
  · rintro ⟨earlier, digit, later, hd, hlen, hs, rfl⟩
    obtain ⟨hpre, hf, hrest⟩ := (denotes_unary_split ht hf hlen).mp hd
    exact ⟨earlier, eraseSuffix digit later, digit, hpre, hf, ⟨later, hrest, hs⟩, rfl⟩
  · rintro ⟨before, after, digit, hpre, hfactor, ⟨later, hrest, hs⟩, rfl⟩
    have he := scan_output_eq_erase hs
    have hl : before.length = pre.length := (denotes_length hpre).trans ht.height
    refine ⟨before, digit, later, (denotes_unary_split ht hf hl).mpr ⟨hpre, hfactor, hrest⟩,
      hl, ?_, ?_⟩
    · simpa [he] using hs
    · simp only [eraseWord, he]

/-- State two contributes no new output beyond state zero: it accepts only
an empty bounded suffix, where state zero accepts the same empty output. -/
theorem scanImage_two_sub_zero (state : State) (output : List Nat) :
    ScanImage 2 state output → ScanImage 0 state output := by
  rintro ⟨digits, hd, hs⟩
  cases digits with
  | nil =>
    have he : output = [] := by simpa [scan] using hs.symm
    subst output
    exact ⟨[], hd, rfl⟩
  | cons digit rest =>
    have hb := denotes_bounded hd digit (by simp)
    rw [scan_three_two_cons hb] at hs
    cases hs

def afterSelected (factor : Factor) (rest : State) : Option State :=
  match factor with
  | .Z => f0 rest
  | .B | .T => union01 rest
  | _ => none

def appendOption (pre : State) (target : Option State) : Option State :=
  target.map (pre ++ ·)

theorem denotes_appendOption (pre : State) (target : Option State) (output : List Nat) :
    denoteOption (appendOption pre target) output ↔
      ∃ before after, denotes pre before ∧ denoteOption target after ∧ output = before ++ after := by
  cases target with
  | none => simp [appendOption, denoteOption]
  | some state => exact denotes_append pre state output

theorem afterSelected_correct {factor : Factor} {rest : State}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) (ht : ThreeLetters rest)
    (output : List Nat) :
    (∃ digit, factor.denotes [digit] ∧ ScanImage digit rest output) ↔
      denoteOption (afterSelected factor rest) output := by
  rcases hf with rfl | rfl | rfl
  · simpa [Factor.denotes, afterSelected] using f0_correct ht output
  · simpa [Factor.denotes, afterSelected, exists_or, and_or_left, or_and_right] using
      union01_correct ht output
  · have hs := union01_correct ht output
    constructor
    · rintro ⟨digit, hd, hscan⟩
      rcases hd with he | he | he
      · have he' : digit = 0 := by simpa using he
        subst digit
        exact hs.mp (Or.inl hscan)
      · have he' : digit = 1 := by simpa using he
        subst digit
        exact hs.mp (Or.inr hscan)
      · have he' : digit = 2 := by simpa using he
        subst digit
        exact hs.mp (Or.inl (scanImage_two_sub_zero rest output hscan))
    · intro hd
      rcases hs.mpr hd with hzero | hone
      · exact ⟨0, Or.inl rfl, hzero⟩
      · exact ⟨1, Or.inr (Or.inl rfl), hone⟩

/-- Each selected value rank has one literal factor-language target (or
rejection). Validity of its decoded physical target follows from exact_pop_rewrite. -/
theorem unary_pop_target {pre rest : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) (output : List Nat) :
    PopImage (pre ++ factor :: rest) pre.length output ↔
      denoteOption (appendOption pre (afterSelected factor rest)) output := by
  rw [popImage_unary_split hp hf, denotes_appendOption]
  constructor
  · rintro ⟨before, after, digit, hb, hd, hs, he⟩
    exact ⟨before, after, hb, (afterSelected_correct hf hr after).mp ⟨digit, hd, hs⟩, he⟩
  · rintro ⟨before, after, hb, ha, he⟩
    obtain ⟨digit, hd, hs⟩ := (afterSelected_correct hf hr after).mpr ha
    exact ⟨before, after, digit, hb, hd, hs, he⟩

#print axioms unary_pop_target
end UnarySuffix
end StackSorting.Generalized.Decorated
