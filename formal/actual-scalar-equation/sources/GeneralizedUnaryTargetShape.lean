import GeneralizedUnaryDeletion
import GeneralizedCompletionCodes

/-! Exact output shape of the smaller unary recurrence. Every accepted target
is unary, has one explicitly preceded O-run, or has one terminal clause. Thus
this route needs no unproved recursive normalization of multiple O-runs. -/
namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates ExceptionalSuffix

theorem threeLetters_append {left right : State} (hl : ThreeLetters left) (hr : ThreeLetters right) :
    ThreeLetters (left ++ right) := by
  intro factor hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hl factor hm
  · exact hr factor hm

theorem threeLetters_replicate (n : Nat) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : ThreeLetters (List.replicate n factor) := by
  intro a ha
  have he := (List.mem_replicate.mp ha).2
  subst a
  exact hf

theorem threeLetters_single {factor : Factor} (hf : factor = .Z ∨ factor = .B ∨ factor = .T) :
    ThreeLetters [factor] := by
  intro a ha
  have he : a = factor := by simpa using ha
  subst a
  exact hf

/-- The exhaustive three target shapes produced from unary input words. -/
inductive TargetShape : State → Prop where
  | plain {state : State} (unary : ThreeLetters state) : TargetShape state
  | orun (pre : State) (q : Nat) (last : Factor)
      (unary : ThreeLetters pre) (terminal : last = .Z ∨ last = .B) :
      TargetShape (pre ++ .Z :: (List.replicate q .O ++ [last]))
  | clause (pre : State) (q : Nat) (unary : ThreeLetters pre) :
      TargetShape (pre ++ [.C (q+1)])

theorem TargetShape.append_prefix {state pre : State} (ht : TargetShape state)
    (hp : ThreeLetters pre) : TargetShape (pre ++ state) := by
  cases ht with
  | plain hs => exact .plain (threeLetters_append hp hs)
  | orun earlier q last hs hl =>
    simpa only [List.append_assoc] using TargetShape.orun (pre ++ earlier) q last
      (threeLetters_append hp hs) hl
  | clause earlier q hs =>
    simpa only [List.append_assoc] using TargetShape.clause (pre ++ earlier) q
      (threeLetters_append hp hs)

theorem TargetShape.prepend {state : State} {factor : Factor} (ht : TargetShape state)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : TargetShape (factor :: state) :=
  ht.append_prefix (threeLetters_single hf)

theorem exceptionalU_three (q : Nat) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : ThreeLetters (exceptionalU q factor) := by
  rcases hf with rfl | rfl | rfl
  · exact threeLetters_append (threeLetters_replicate q (Or.inr (Or.inl rfl)))
      (threeLetters_single (Or.inl rfl))
  · exact threeLetters_replicate (q+1) (Or.inr (Or.inl rfl))
  · exact threeLetters_replicate (q+1) (Or.inr (Or.inl rfl))

theorem exceptionalF0_shape (q : Nat) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : TargetShape (exceptionalF0 q factor) := by
  rcases hf with rfl | rfl | rfl
  · exact .plain (exceptionalU_three q (Or.inl rfl))
  · exact .clause [] q (by intro a ha; cases ha)
  · exact .plain (threeLetters_replicate (q+1) (Or.inr (Or.inl rfl)))

theorem z_f1_shape {state target : State} (ht : ThreeLetters state)
    (he : prepend .Z (f1 state) = some target) : TargetShape target := by
  cases state with
  | nil =>
    have hx : target = [.Z] := by simpa [prepend, f1] using he.symm
    subst target
    exact .plain (threeLetters_single (Or.inl rfl))
  | cons factor rest =>
    cases hx : exceptional (factor :: rest) with
    | none => simp [prepend, f1, hx] at he
    | some pair =>
      obtain ⟨q, last⟩ := pair
      have shape : target = .Z :: (List.replicate q .O ++ [terminal last]) := by
        simpa [prepend, f1, hx] using he.symm
      rw [shape]
      apply TargetShape.orun [] q (terminal last) (by intro a ha; cases ha)
      rcases exceptional_terminal ht hx with rfl | rfl | rfl <;> simp [terminal]

/-- Exhaustive accepted state-zero targets; the induction prepends only
ordinary Z/B factors, never creates a second O-run or an internal clause. -/
theorem f0_target_shape {state target : State} (ht : ThreeLetters state)
    (he : f0 state = some target) : TargetShape target := by
  induction state generalizing target with
  | nil =>
    have hx : target = [] := by simpa [f0] using he.symm
    subst target
    exact .plain (by intro a ha; cases ha)
  | cons factor rest ih =>
    have htr := ht.tail
    cases hx : exceptional (factor :: rest) with
    | some pair =>
      obtain ⟨q, last⟩ := pair
      have shape : target = exceptionalF0 q last := by simpa only [f0, hx, Option.some.injEq] using he.symm
      rw [shape]
      exact exceptionalF0_shape q (exceptional_terminal ht hx)
    | none =>
      rcases ht factor (by simp) with rfl | rfl | rfl
      · apply z_f1_shape htr
        simpa only [f0, hx] using he
      · have hp := he
        simp only [f0, hx] at hp
        cases hr : exceptional rest with
        | some pair =>
          obtain ⟨q, last⟩ := pair
          have shape : target = .Z :: exceptionalU q last := by simpa [hr, prepend] using hp.symm
          rw [shape]
          exact (TargetShape.plain (exceptionalU_three q (exceptional_terminal htr hr))).prepend (Or.inl rfl)
        | none =>
          obtain ⟨after, ha, hat⟩ := Option.map_eq_some_iff.mp
            (show (f0 rest).map (.Z :: ·) = some target by simpa [hr, prepend] using hp)
          rw [← hat]
          exact (ih htr ha).prepend (Or.inl rfl)
      · obtain ⟨after, ha, hat⟩ := Option.map_eq_some_iff.mp
          (show (f0 rest).map (.B :: ·) = some target by simpa only [f0, hx, prepend] using he)
        rw [← hat]
        exact (ih htr ha).prepend (Or.inr (Or.inl rfl))

theorem union01_target_shape {state target : State} (ht : ThreeLetters state)
    (he : union01 state = some target) : TargetShape target := by
  cases hx : exceptional state with
  | none => exact f0_target_shape ht (by simpa only [union01, hx] using he)
  | some pair =>
    obtain ⟨q, last⟩ := pair
    have shape : target = exceptionalU q last := by simpa only [union01, hx, Option.some.injEq] using he.symm
    rw [shape]
    exact .plain (exceptionalU_three q (exceptional_terminal ht hx))

theorem selected_target_shape {pre rest target : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (he : appendOption pre (afterSelected factor rest) = some target) : TargetShape target := by
  obtain ⟨after, ha, hat⟩ := Option.map_eq_some_iff.mp he
  rw [← hat]
  apply TargetShape.append_prefix (hp := hp)
  rcases hf with rfl | rfl | rfl
  · exact f0_target_shape hr ha
  · exact union01_target_shape hr ha
  · exact union01_target_shape hr ha


theorem ThreeLetters.inhabited {state : State} (ht : ThreeLetters state) :
    ∃ digits, denotes state digits := by
  induction state with
  | nil => exact ⟨[], rfl⟩
  | cons factor rest ih =>
    obtain ⟨tail, htail⟩ := ih ht.tail
    have hf : factor.denotes [0] := by
      rcases ht factor (by simp) with rfl | rfl | rfl
      · rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    exact ⟨0 :: tail, [0], tail, hf, htail, rfl⟩

theorem TargetShape.inhabited {state : State} (hs : TargetShape state) :
    ∃ digits, denotes state digits := by
  cases hs with
  | plain ht => exact ht.inhabited
  | orun pre q last hp hl =>
    obtain ⟨before, hb⟩ := hp.inhabited
    have hf : last.denotes [0] := by rcases hl with rfl | rfl; rfl; exact Or.inl rfl
    have ho : denotes (List.replicate q .O ++ [last]) (List.replicate q 1 ++ [0]) :=
      (denotes_append _ _ _).mpr ⟨_, _, (denotes_O_replicate q _).mpr rfl,
        (denotes_single _ _).mpr hf, rfl⟩
    exact ⟨before ++ 0 :: (List.replicate q 1 ++ [0]),
      (denotes_append _ _ _).mpr ⟨before, _, hb, (denotes_Z _ _).mpr ⟨_, ho, rfl⟩, rfl⟩⟩
  | clause pre q hp =>
    obtain ⟨before, hb⟩ := hp.inhabited
    have hc : (Factor.C (q+1)).denotes (List.replicate (q+1) 0) := by
      simp [Factor.denotes]
    exact ⟨before ++ List.replicate (q+1) 0, (denotes_append _ _ _).mpr
      ⟨before, _, hb, (denotes_single _ _).mpr hc, rfl⟩⟩

theorem popImage_length {state : State} {rank : Nat} {output : List Nat}
    (hp : PopImage state rank output) : output.length+1 = height state := by
  obtain ⟨earlier, selected, later, hd, _, _, rfl⟩ := hp
  have hl := denotes_length hd
  simp only [List.length_append, List.length_cons] at hl
  simp only [eraseWord, List.length_append, eraseSuffix_length]
  omega

theorem selected_target_height {pre rest target : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (he : appendOption pre (afterSelected factor rest) = some target) :
    height target = height (pre ++ factor :: rest)-1 := by
  obtain ⟨digits, hd⟩ := (selected_target_shape hp hr hf he).inhabited
  have ht : denoteOption (appendOption pre (afterSelected factor rest)) digits := by
    simpa only [he, denoteOption] using hd
  have hl := popImage_length ((unary_pop_target hp hr hf digits).mpr ht)
  rw [denotes_length hd] at hl
  omega

/-- Ambient validity and literal physical successor equivalence are derived
for each computed accepted target, with no caller-supplied rewrite claim. -/
theorem selected_target_physical {pre rest target : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (hv : Valid (pre ++ factor :: rest))
    (he : appendOption pre (afterSelected factor rest) = some target) :
    Valid target ∧ (∀ after, Represents target after ↔
      PhysicalPopImage (pre ++ factor :: rest) pre.length after) := by
  apply exact_pop_rewrite hv
  intro output
  have ht := unary_pop_target hp hr hf output
  simpa only [he, denoteOption] using ht.symm

/-- Exact held-code fiber for each computed unary successor. It is the same
complete code language, not only a count equality. -/
theorem codeCompletion_held_target {pre rest target : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (hv : Valid (pre ++ factor :: rest))
    (he : appendOption pre (afterSelected factor rest) = some target)
    (n : Nat) (code : List LazyCode.Letter) :
    CodeCompletion (pre ++ factor :: rest) n (.H (pre.length+1) :: code) ↔
      CodeCompletion target n code := by
  have hh := selected_target_height hp hr hf he
  have ht := selected_target_physical hp hr hf hv he
  have wholeThree : ThreeLetters (pre ++ factor :: rest) :=
    threeLetters_append hp (by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hf; exact hr a ha)
  have hk : pre.length+1 ≤ height (pre ++ factor :: rest) := by
    rw [wholeThree.height]
    simp only [List.length_append, List.length_cons]
    omega
  rw [codeCompletion_held]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨_, _, budget, after, hpop, ha⟩
    exact ⟨by simpa only [hh] using budget, after, (ht.2 after).mpr hpop,
      by simpa only [hh] using ha⟩
  · rintro ⟨budget, after, hrep, ha⟩
    exact ⟨by omega, hk, by simpa only [hh] using budget, after, (ht.2 after).mp hrep,
      by simpa only [hh] using ha⟩

/-- Rejected computed targets contribute no complete first-letter codes. -/
theorem codeCompletion_held_reject {pre rest : State} {factor : Factor}
    (hp : ThreeLetters pre) (hr : ThreeLetters rest)
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T)
    (he : appendOption pre (afterSelected factor rest) = none)
    (n : Nat) (code : List LazyCode.Letter) :
    ¬ CodeCompletion (pre ++ factor :: rest) n (.H (pre.length+1) :: code) := by
  intro hc
  obtain ⟨_, _, _, after, hpop, _⟩ := (codeCompletion_held _ _ _ _).mp hc
  have hpop' : PhysicalPopImage (pre ++ factor :: rest) pre.length after := by
    simpa only [Nat.add_sub_cancel] using hpop
  obtain ⟨digits, hd, _⟩ := physicalPop_to_coordinate hpop'
  have hx := (unary_pop_target hp hr hf digits).mp hd
  simp only [he, denoteOption] at hx

#print axioms f0_target_shape
#print axioms selected_target_shape
#print axioms codeCompletion_held_target
#print axioms codeCompletion_held_reject
end UnarySuffix
end StackSorting.Generalized.Decorated
