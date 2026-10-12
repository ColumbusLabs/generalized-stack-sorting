import GeneralizedExceptionalSuffixClassification

/-! Concrete exact suffix targets for O-free unary input states. This is the
smaller closure theorem needed by the signed counting recurrence; it does not
attempt transitions from arbitrary clause-bearing decorated states. -/
namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates ExceptionalSuffix

def ThreeLetters (state : State) : Prop :=
  ∀ factor ∈ state, factor = .Z ∨ factor = .B ∨ factor = .T

/-- The exact exceptional-tail parser, with no bounded lookahead. -/
def exceptional : State → Option (Nat × Factor)
  | [] => none
  | factor :: rest =>
      match rest with
      | [] => some (0, factor)
      | _ :: _ => if factor = .T then (exceptional rest).map (fun pair => (pair.1+1, pair.2)) else none

theorem exceptional_word (q : Nat) (factor : Factor) :
    exceptional (List.replicate q .T ++ [factor]) = some (q, factor) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hs : List.replicate q Factor.T ++ [factor] with
    | nil => simp at hs
    | cons head rest =>
      change (exceptional (head :: rest)).map (fun pair => (pair.1+1, pair.2)) = some (q+1, factor)
      rw [← hs, ih]
      rfl

theorem exceptional_shape {state : State} {q : Nat} {factor : Factor}
    (he : exceptional state = some (q, factor)) :
    state = List.replicate q .T ++ [factor] := by
  induction state generalizing q factor with
  | nil => simp [exceptional] at he
  | cons head rest ih =>
    cases rest with
    | nil =>
      simp only [exceptional, Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      rfl
    | cons a rest =>
      by_cases hh : head = .T
      · subst head
        simp only [exceptional, ite_true, Option.map_eq_some_iff] at he
        obtain ⟨⟨q', factor'⟩, ht, hp⟩ := he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        have hw := ih ht
        simpa [List.replicate_succ] using congrArg (Factor.T :: ·) hw
      · simp [exceptional, hh] at he

theorem exceptional_iff (state : State) (q : Nat) (factor : Factor) :
    exceptional state = some (q, factor) ↔ state = List.replicate q .T ++ [factor] :=
  ⟨exceptional_shape, fun he => by rw [he]; exact exceptional_word q factor⟩

def denoteOption : Option State → List Nat → Prop
  | none, _ => False
  | some state, output => denotes state output

def prepend (factor : Factor) (target : Option State) : Option State :=
  target.map (factor :: ·)

def f1 (state : State) : Option State :=
  match state with
  | [] => some []
  | _ :: _ => (exceptional state).map (fun pair => List.replicate pair.1 .O ++ [terminal pair.2])

def exceptionalF0 (q : Nat) : Factor → State
  | .Z => List.replicate q .B ++ [.Z]
  | .B => [.C (q+1)]
  | .T => List.replicate (q+1) .B
  | _ => []

def exceptionalU (q : Nat) : Factor → State
  | .Z => List.replicate q .B ++ [.Z]
  | .B | .T => List.replicate (q+1) .B
  | _ => []

def f0 : State → Option State
  | [] => some []
  | factor :: rest =>
    match exceptional (factor :: rest) with
    | some (q, last) => some (exceptionalF0 q last)
    | none =>
      match factor with
      | .Z => prepend .Z (f1 rest)
      | .B => prepend .Z (match exceptional rest with
          | some (q, last) => some (exceptionalU q last)
          | none => f0 rest)
      | .T => prepend .B (f0 rest)
      | _ => none

def union01 (state : State) : Option State :=
  match exceptional state with
  | some (q, last) => some (exceptionalU q last)
  | none => f0 state


theorem ThreeLetters.tail {factor : Factor} {state : State}
    (ht : ThreeLetters (factor :: state)) : ThreeLetters state := by
  intro a ha
  exact ht a (by simp [ha])

theorem ThreeLetters.canonical {state : State} (ht : ThreeLetters state) :
    CanonicalFactors state := by
  intro size hm
  rcases ht (.C size) hm with he | he | he <;> cases he

theorem exceptional_terminal {state : State} (ht : ThreeLetters state)
    {q : Nat} {factor : Factor} (he : exceptional state = some (q, factor)) :
    factor = .Z ∨ factor = .B ∨ factor = .T := by
  have hs := exceptional_shape he
  exact ht factor (by simp [hs])

theorem terminal_unary {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : Unary factor := by
  rcases hf with rfl | rfl | rfl <;> simp [Unary]

/-- The exact state-one image, including rejection of every other suffix. -/
theorem f1_correct {state : State} (ht : ThreeLetters state) (output : List Nat) :
    ScanImage 1 state output ↔ denoteOption (f1 state) output := by
  cases state with
  | nil => simp [f1, denoteOption]
  | cons factor rest =>
    cases he : exceptional (factor :: rest) with
    | none =>
      simp only [f1, he, Option.map_none, denoteOption, iff_false]
      intro hs
      obtain ⟨q, last, _, shape⟩ := scanImage_one_classification ht.canonical (by simp) hs
      have hx := exceptional_word q last
      rw [← shape, he] at hx
      cases hx
    | some pair =>
      obtain ⟨q, last⟩ := pair
      have shape := exceptional_shape he
      have hu := terminal_unary (exceptional_terminal ht he)
      simp only [f1, he, Option.map_some, denoteOption]
      rw [shape]
      exact scanImage_one_exceptional q hu output

theorem no_state_one {state : State} (ht : ThreeLetters state)
    (hn : state ≠ []) (he : exceptional state = none) (output : List Nat) :
    ¬ ScanImage 1 state output := by
  intro hs
  obtain ⟨q, last, _, shape⟩ := scanImage_one_classification ht.canonical hn hs
  have hx := exceptional_word q last
  rw [← shape, he] at hx
  cases hx

theorem exceptionalF0_correct (q : Nat) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [factor]) output ↔
      denotes (exceptionalF0 q factor) output := by
  rcases hf with rfl | rfl | rfl
  · exact scanImage_zero_Z q output
  · simpa only [exceptionalF0, denotes_single] using scanImage_zero_O_or_B q (Or.inr rfl) output
  · exact scanImage_zero_T q output

theorem exceptionalU_correct (q : Nat) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) (output : List Nat) :
    (ScanImage 0 (List.replicate q .T ++ [factor]) output ∨
      ScanImage 1 (List.replicate q .T ++ [factor]) output) ↔
      denotes (exceptionalU q factor) output := by
  rcases hf with rfl | rfl | rfl
  · exact scanImage_union_Z q output
  · exact scanImage_union_O_or_B q (Or.inr rfl) output
  · exact scanImage_union_T q output

/-- Literal Z and B heads, before any exceptional-tail simplification. -/
theorem scanImage_zero_Z_head (state : State) (output : List Nat) :
    ScanImage 0 (.Z :: state) output ↔
      ∃ tail, ScanImage 1 state tail ∧ output = 0 :: tail := by
  constructor
  · rintro ⟨digits, hd, hs⟩
    obtain ⟨tail, ht, rfl⟩ := (denotes_Z state digits).mp hd
    rw [scan_three_zero_zero] at hs
    obtain ⟨after, ha, he⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨after, ⟨tail, ht, ha⟩, he.symm⟩
  · rintro ⟨tail, ⟨digits, hd, hs⟩, rfl⟩
    exact ⟨0 :: digits, (denotes_Z state _).mpr ⟨digits, hd, rfl⟩,
      by simp [scan_three_zero_zero, hs]⟩

theorem scanImage_zero_B_head (state : State) (output : List Nat) :
    ScanImage 0 (.B :: state) output ↔
      ∃ tail, (ScanImage 0 state tail ∨ ScanImage 1 state tail) ∧ output = 0 :: tail := by
  constructor
  · rintro ⟨digits, hd, hs⟩
    obtain ⟨digit, tail, hc, ht, rfl⟩ := (denotes_B state digits).mp hd
    rcases hc with rfl | rfl
    · rw [scan_three_zero_zero] at hs
      obtain ⟨after, ha, he⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨after, Or.inr ⟨tail, ht, ha⟩, he.symm⟩
    · rw [scan_three_zero_one] at hs
      obtain ⟨after, ha, he⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨after, Or.inl ⟨tail, ht, ha⟩, he.symm⟩
  · rintro ⟨tail, hs, rfl⟩
    rcases hs with ⟨digits, hd, hs⟩ | ⟨digits, hd, hs⟩
    · exact ⟨1 :: digits, (denotes_B state _).mpr ⟨1, digits, Or.inr rfl, hd, rfl⟩,
        by simp [scan_three_zero_one, hs]⟩
    · exact ⟨0 :: digits, (denotes_B state _).mpr ⟨0, digits, Or.inl rfl, hd, rfl⟩,
        by simp [scan_three_zero_zero, hs]⟩

theorem denotes_prepend_Z (target : Option State) (output : List Nat) :
    denoteOption (prepend .Z target) output ↔
      ∃ tail, denoteOption target tail ∧ output = 0 :: tail := by
  cases target <;> simp [prepend, denoteOption]

theorem denotes_prepend_B (target : Option State) (output : List Nat) :
    denoteOption (prepend .B target) output ↔
      ∃ digit tail, (digit = 0 ∨ digit = 1) ∧
        denoteOption target tail ∧ output = digit :: tail := by
  cases target <;> simp [prepend, denoteOption]


theorem exceptional_T_none {state : State} (he : exceptional (.T :: state) = none) :
    state ≠ [] ∧ exceptional state = none := by
  cases state with
  | nil => simp [exceptional] at he
  | cons factor rest =>
    exact ⟨by simp, by simpa only [exceptional, ite_true, Option.map_eq_none_iff] using he⟩

/-- Exact state-zero image for every unary Z/B/T suffix, before the output
O-run bijection or terminal-clause valuation is applied. -/
theorem f0_correct {state : State} (ht : ThreeLetters state) (output : List Nat) :
    ScanImage 0 state output ↔ denoteOption (f0 state) output := by
  induction state generalizing output with
  | nil => simp [f0, denoteOption]
  | cons factor rest ih =>
    have htr := ht.tail
    have head := ht factor (by simp)
    cases he : exceptional (factor :: rest) with
    | some pair =>
      obtain ⟨q, last⟩ := pair
      have shape := exceptional_shape he
      have lastThree := exceptional_terminal ht he
      have hf : f0 (factor :: rest) = some (exceptionalF0 q last) := by simp only [f0, he]
      rw [hf]
      change ScanImage 0 (factor :: rest) output ↔ denotes (exceptionalF0 q last) output
      rw [shape]
      exact exceptionalF0_correct q lastThree output
    | none =>
      rcases head with rfl | rfl | rfl
      · have hf : f0 (.Z :: rest) = prepend .Z (f1 rest) := by simp only [f0, he]
        rw [hf, scanImage_zero_Z_head, denotes_prepend_Z]
        exact exists_congr fun tail => and_congr (f1_correct htr tail) Iff.rfl
      · have hu : ∀ tail, (ScanImage 0 rest tail ∨ ScanImage 1 rest tail) ↔
            denoteOption (match exceptional rest with
              | some (q, last) => some (exceptionalU q last)
              | none => f0 rest) tail := by
          intro tail
          cases her : exceptional rest with
          | some pair =>
            obtain ⟨q, last⟩ := pair
            have shape := exceptional_shape her
            change (ScanImage 0 rest tail ∨ ScanImage 1 rest tail) ↔ denotes (exceptionalU q last) tail
            rw [shape]
            exact exceptionalU_correct q (exceptional_terminal htr her) tail
          | none =>
            have hn : rest ≠ [] := by intro hn; subst rest; simp [exceptional] at he
            have reject := no_state_one htr hn her tail
            simpa only [her, or_false, reject] using ih htr tail
        have hf : f0 (.B :: rest) = prepend .Z (match exceptional rest with
            | some (q, last) => some (exceptionalU q last)
            | none => f0 rest) := by simp only [f0, he]
        rw [hf, scanImage_zero_B_head, denotes_prepend_Z]
        exact exists_congr fun tail => and_congr (hu tail) Iff.rfl
      · have hn := exceptional_T_none he
        have hf : f0 (.T :: rest) = prepend .B (f0 rest) := by simp only [f0, he]
        rw [hf, denotes_prepend_B]
        cases output with
        | nil => simp
        | cons digit tail =>
          rw [scanImage_T_zero_cons]
          have reject := no_state_one htr hn.1 hn.2 tail
          simp only [reject, and_false, false_or, ih htr tail, List.cons.injEq]
          constructor
          · rintro (⟨rfl, ht⟩ | ⟨rfl, ht⟩)
            · exact ⟨0, tail, Or.inl rfl, ht, rfl, rfl⟩
            · exact ⟨1, tail, Or.inr rfl, ht, rfl, rfl⟩
          · rintro ⟨a, rest, ha, ht, rfl, rfl⟩
            rcases ha with rfl | rfl
            · exact Or.inl ⟨rfl, ht⟩
            · exact Or.inr ⟨rfl, ht⟩

theorem union01_correct {state : State} (ht : ThreeLetters state) (output : List Nat) :
    (ScanImage 0 state output ∨ ScanImage 1 state output) ↔
      denoteOption (union01 state) output := by
  cases he : exceptional state with
  | some pair =>
    obtain ⟨q, last⟩ := pair
    have shape := exceptional_shape he
    simp only [union01, he, denoteOption]
    rw [shape]
    exact exceptionalU_correct q (exceptional_terminal ht he) output
  | none =>
    simp only [union01, he]
    by_cases hn : state = []
    · subst state; simp [f0, denoteOption]
    · have reject := no_state_one ht hn he output
      simpa only [reject, or_false] using f0_correct ht output

#print axioms f1_correct
#print axioms f0_correct
#print axioms union01_correct

end UnarySuffix
end StackSorting.Generalized.Decorated
