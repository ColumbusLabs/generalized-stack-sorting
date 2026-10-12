import GeneralizedRawMachine
import RawCanonical

/-! Exact two-way compatibility with the published no-bypass (2,2) machine. -/
namespace StackSorting.Generalized

def embed : Labelled.RawOp → RawOp
  | .push0 a => .push 0 a
  | .push1 a => .push 1 a
  | .pop0 => .pop 0
  | .pop1 => .pop 1

def decode : RawOp → Labelled.RawOp
  | .push k a => if k = 0 then .push0 a else .push1 a
  | .pop k => if k = 0 then .pop0 else .pop1

theorem step_embed (op : Labelled.RawOp) (held : List Nat) :
    step 2 2 (embed op) held = Labelled.rawStep op held := by
  cases op <;> cases held with
  | nil => rfl
  | cons a rest => cases rest <;> rfl

theorem inputs_embed (ops : List Labelled.RawOp) :
    inputs (ops.map embed) = Labelled.rawInputs ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simpa [inputs, embed, introduced, Labelled.rawInputs,
      Labelled.rawIntroduced] using ih

theorem inputs_decode (ops : List RawOp) :
    Labelled.rawInputs (ops.map decode) = inputs ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | push k a => by_cases hk : k = 0 <;>
        simp [inputs, introduced, Labelled.rawInputs, Labelled.rawIntroduced, decode, hk] at ih ⊢ <;>
        exact ih
    | pop k => by_cases hk : k = 0 <;>
        simp [inputs, introduced, Labelled.rawInputs, Labelled.rawIntroduced, decode, hk] at ih ⊢ <;>
        exact ih

theorem run_embed (ops : List Labelled.RawOp) (held : List Nat) :
    run 2 2 (ops.map embed) held = Labelled.rawRun ops held := by
  induction ops generalizing held with
  | nil => rfl
  | cons op ops ih => simp [run, Labelled.rawRun, step_embed, ih]

theorem step_decode (op : RawOp) (held after out : List Nat)
    (h : step 2 2 op held = some (after, out)) :
    Labelled.rawStep (decode op) held = some (after, out) := by
  cases op with
  | push k a =>
    have hk : k < 2 := by
      by_cases hk : k < 2
      · exact hk
      · simp [step, hk] at h
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simpa [decode] using (step_embed (.push0 a) held ▸ h)
    · simpa [decode] using (step_embed (.push1 a) held ▸ h)
  | pop k =>
    have hk : k < 2 := by
      by_cases hk : k < 2
      · exact hk
      · simp [step, hk] at h
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simpa [decode] using (step_embed .pop0 held ▸ h)
    · simpa [decode] using (step_embed .pop1 held ▸ h)

theorem run_decode (ops : List RawOp) (held after out : List Nat)
    (h : run 2 2 ops held = some (after, out)) :
    Labelled.rawRun (ops.map decode) held = some (after, out) := by
  induction ops generalizing held after out with
  | nil => exact h
  | cons op ops ih =>
    obtain ⟨middle, emitted, tail, hs, ht, ho⟩ := split_run 2 2 op ops held after out h
    have hs' := step_decode op held middle emitted hs
    have ht' := ih middle after tail ht
    simp [Labelled.rawRun, hs', ht', ho]

/-- No extra successful (2,2) histories are admitted by the slot-indexed model. -/
theorem canTransform_two_iff (held input output : List Nat) :
    CanTransform 2 2 held input output ↔ Labelled.CanSort held input output := by
  constructor
  · rintro ⟨ops, hr, hi⟩
    exact ⟨ops.map decode, run_decode ops held [] output hr, (inputs_decode ops).trans hi⟩
  · rintro ⟨ops, hr, hi⟩
    exact ⟨ops.map embed, by simpa [run_embed] using hr, (inputs_embed ops).trans hi⟩

theorem canSort_two_iff (input : List Nat) :
    CanSort 2 2 input ↔ Labelled.CanSort [] input (List.range' 1 input.length) :=
  canTransform_two_iff [] input _

#print axioms canTransform_two_iff
#print axioms canSort_two_iff
end StackSorting.Generalized
