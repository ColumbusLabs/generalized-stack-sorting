import RawExchange

/-! # Exact deletion projection for a token of the original machine -/
namespace StackSorting.Labelled

def deleteToken (a : Nat) (xs : List Nat) : List Nat := xs.filter (· != a)

def deleteOp (a : Nat) (op : RawOp) (held : List Nat) : List RawOp :=
  match op, held with
  | .push0 b, _ => if b = a then [] else [.push0 b]
  | .push1 _, [] => []
  | .push1 b, c :: _ =>
      if b = a then [] else if c = a then [.push0 b] else [.push1 b]
  | .pop0, [] => []
  | .pop0, b :: _ => if b = a then [] else [.pop0]
  | .pop1, c :: b :: _ =>
      if b = a then [] else if c = a then [.pop0] else [.pop1]
  | .pop1, _ => []

/-- Deleting a token shifts only an affected second-position operation to the
first position, or removes the operation if it acts on the deleted token. -/
theorem delete_step (a : Nat) (op : RawOp) (held after emitted : List Nat)
    (h : rawStep op held = some (after, emitted)) :
    rawRun (deleteOp a op held) (deleteToken a held) =
      some (deleteToken a after, deleteToken a emitted) ∧
    rawInputs (deleteOp a op held) = deleteToken a (rawIntroduced op) := by
  cases op with
  | push0 b =>
    simp [rawStep] at h
    rcases h with ⟨rfl, rfl⟩
    by_cases hb : b = a <;>
      simp [deleteOp, deleteToken, rawRun, rawStep, rawInputs, rawIntroduced, hb]
  | push1 b =>
    cases held with
    | nil => simp [rawStep] at h
    | cons c rest =>
      simp [rawStep] at h
      rcases h with ⟨rfl, rfl⟩
      by_cases hb : b = a <;> by_cases hc : c = a <;>
        simp [deleteOp, deleteToken, rawRun, rawStep, rawInputs, rawIntroduced, hb, hc]
  | pop0 =>
    cases held with
    | nil => simp [rawStep] at h
    | cons b rest =>
      simp [rawStep] at h
      rcases h with ⟨rfl, rfl⟩
      by_cases hb : b = a <;>
        simp [deleteOp, deleteToken, rawRun, rawStep, rawInputs, rawIntroduced, hb]
  | pop1 =>
    cases held with
    | nil => simp [rawStep] at h
    | cons c rest =>
      cases rest with
      | nil => simp [rawStep] at h
      | cons b rest =>
        simp [rawStep] at h
        rcases h with ⟨rfl, rfl⟩
        by_cases hb : b = a <;> by_cases hc : c = a <;>
          simp [deleteOp, deleteToken, rawRun, rawStep, rawInputs, rawIntroduced, hb, hc]

def deleteTrace (a : Nat) : List RawOp → List Nat → List RawOp
  | [], _ => []
  | op :: ops, held =>
      match rawStep op held with
      | none => []
      | some (after, _) => deleteOp a op held ++ deleteTrace a ops after

theorem rawInputs_append (as bs : List RawOp) :
    rawInputs (as ++ bs) = rawInputs as ++ rawInputs bs := by
  simp [rawInputs]

/-- Deletion commutes with every successful raw trace, preserving the filtered
initial/final stack, input sequence and output sequence. -/
theorem delete_run (a : Nat) (ops : List RawOp) (held after out : List Nat)
    (h : rawRun ops held = some (after, out)) :
    rawRun (deleteTrace a ops held) (deleteToken a held) =
      some (deleteToken a after, deleteToken a out) ∧
    rawInputs (deleteTrace a ops held) = deleteToken a (rawInputs ops) := by
  induction ops generalizing held after out with
  | nil =>
    simp [rawRun] at h
    rcases h with ⟨rfl, rfl⟩
    simp [deleteTrace, rawRun, rawInputs, deleteToken]
  | cons op ops ih =>
    obtain ⟨u, emitted, tail, hs, hr, hout⟩ := raw_split_run op ops held after out h
    have hf := delete_step a op held u emitted hs
    have ht := ih u after tail hr
    constructor
    · simp only [deleteTrace, hs]
      simp [rawRun_append, hf.1, ht.1]
      simp [← hout, deleteToken]
    · simp only [deleteTrace, hs]
      rw [rawInputs_append, hf.2, ht.2]
      simp [rawInputs, deleteToken]

#print axioms delete_step
#print axioms delete_run

end StackSorting.Labelled
