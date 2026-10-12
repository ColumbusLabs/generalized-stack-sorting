import CanonicalUniqueness

/-!
# Expansion into the original no-bypass stack machine

The independent raw model has only single-token top-two pushes and pops.
Every bypass is expanded to push0 followed by pop0; no pop-permission flag is
imposed on the raw machine.
-/
namespace StackSorting.Labelled
open TForest

inductive RawOp where
  | push0 (token : Nat)
  | push1 (token : Nat)
  | pop0 | pop1
  deriving DecidableEq, Repr

def rawStep (op : RawOp) (held : List Nat) : Option (List Nat × List Nat) :=
  match op, held with
  | .push0 a, _ => some (a :: held, [])
  | .push1 _, [] => none
  | .push1 a, b :: rest => some (b :: a :: rest, [])
  | .pop0, [] => none
  | .pop0, a :: rest => some (rest, [a])
  | .pop1, a :: b :: rest => some (a :: rest, [b])
  | .pop1, _ => none

def rawRun : List RawOp → List Nat → Option (List Nat × List Nat)
  | [], held => some (held, [])
  | op :: ops, held => do
      let (t, out) ← rawStep op held
      let (u, outs) ← rawRun ops t
      pure (u, out ++ outs)

def expandAction : Action → List RawOp
  | .bypass a => [.push0 a, .pop0]
  | .push0 a => [.push0 a]
  | .push1 a => [.push1 a]
  | .pop0 => [.pop0]
  | .pop1 => [.pop1]

def expandTrace (acts : List Action) : List RawOp := acts.flatMap expandAction

def rawIntroduced : RawOp → List Nat
  | .push0 a | .push1 a => [a]
  | .pop0 | .pop1 => []

def rawInputs (ops : List RawOp) : List Nat := ops.flatMap rawIntroduced

theorem expand_inputs (acts : List Action) : rawInputs (expandTrace acts) = inputs acts := by
  induction acts with
  | nil => rfl
  | cons act acts ih =>
    cases act <;> simp [rawInputs, expandTrace, expandAction, rawIntroduced, inputs, introduced] at ih ⊢ <;>
      exact ih

theorem rawRun_append (as bs : List RawOp) (held : List Nat) :
    rawRun (as ++ bs) held = (do
      let (t, out) ← rawRun as held
      let (u, outs) ← rawRun bs t
      pure (u, out ++ outs)) := by
  induction as generalizing held with
  | nil => simp [rawRun, Prod.eta]
  | cons op ops ih =>
    simp [rawRun, ih, Option.bind_assoc, List.append_assoc]

/-- Each permitted compressed stack step expands to legal raw operations. -/
theorem expand_step (act : Action) (s t : SState) (out : List Nat)
    (h : stackStep act s = some (t, out)) :
    rawRun (expandAction act) s.1 = some (t.1, out) := by
  rcases s with ⟨held, flag⟩
  cases act <;> cases held with
  | nil =>
    simp [stackStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [rawRun, rawStep, expandAction]
  | cons a rest =>
    cases rest <;> cases flag <;> simp [stackStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [rawRun, rawStep, expandAction]

/-- Full simulation preserves the exact emitted list and physical stack order. -/
theorem expand_run (acts : List Action) (s t : SState) (out : List Nat)
    (h : stackRun acts s = some (t, out)) :
    rawRun (expandTrace acts) s.1 = some (t.1, out) := by
  induction acts generalizing s t out with
  | nil =>
    simp [stackRun] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | cons act acts ih =>
    cases hs : stackStep act s with
    | none => simp [stackRun, hs] at h
    | some p =>
      rcases p with ⟨u, emitted⟩
      cases hr : stackRun acts u with
      | none => simp [stackRun, hs, hr] at h
      | some p =>
        rcases p with ⟨v, tail⟩
        simp [stackRun, hs, hr] at h
        rcases h with ⟨rfl, rfl⟩
        have hfirst := expand_step act s u emitted hs
        have htail := ih u v tail hr
        change rawRun (expandAction act ++ expandTrace acts) s.1 = _
        simp [rawRun_append, hfirst, htail]

/-- Every complete distinct-token forest path yields a legal trace of the
original machine, with the output-ranked input and increasing output 1,...,n. -/
theorem ranked_original_trace (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out))
    (hd : (inputs acts).Nodup) :
    rawRun (expandTrace (acts.map (relabelAction (outputRank out)))) [] =
      some ([], List.range' 1 out.length) := by
  exact expand_run _ ([], b) ([], c) _ (ranked_complete_stack acts b c out h hd)

#print axioms expand_inputs
#print axioms expand_step
#print axioms expand_run
#print axioms ranked_original_trace

end StackSorting.Labelled
