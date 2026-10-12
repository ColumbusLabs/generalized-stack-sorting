import ForestWord

/-!
# Token identities and concrete stack semantics

A partial formalization of the forest/canonical-history bridge. This file
proves erasure/lifting, stack-order/output simulation, and token conservation.
It does not assume or conclude that the simulated histories are canonical.
-/
namespace StackSorting.Labelled

inductive TForest where
  | nil : TForest
  | cons (token : Nat) (children rest : TForest) : TForest
  deriving DecidableEq, Repr

inductive Action where
  | bypass (token : Nat)
  | push0 (token : Nat)
  | push1 (token : Nat)
  | pop0 | pop1
  deriving DecidableEq, Repr

open TForest

abbrev TState := TForest × Bool
abbrev SState := List Nat × Bool

def append : TForest → TForest → TForest
  | nil, g => g
  | cons a c r, g => cons a c (append r g)

def erase : TForest → Forest
  | nil => .nil
  | cons _ c r => .cons (erase c) (erase r)

def tokens : TForest → List Nat
  | nil => []
  | cons a c r => a :: (tokens c ++ tokens r)

def eraseState (s : TState) : FState := (erase s.1, s.2)
def stackState (s : TState) : SState := (tokens s.1, s.2)

def eraseAction : Action → Op
  | .bypass _ => .bypass
  | .push0 _ => .push0
  | .push1 _ => .push1
  | .pop0 => .pop0
  | .pop1 => .pop1

def introduced : Action → List Nat
  | .bypass a | .push0 a | .push1 a => [a]
  | .pop0 | .pop1 => []

def inputs (as : List Action) : List Nat := as.flatMap introduced

theorem erase_append (f g : TForest) :
    erase (append f g) = StackSorting.append (erase f) (erase g) := by
  induction f with
  | nil => rfl
  | cons a c r _ ihr => simp [append, erase, StackSorting.append, ihr]

theorem tokens_append (f g : TForest) :
    tokens (append f g) = tokens f ++ tokens g := by
  induction f with
  | nil => rfl
  | cons a c r _ ihr => simp [append, tokens, ihr, List.append_assoc]

def tokenStep (act : Action) : TState → Option (TState × List Nat)
  | (f, canPop) => match act, f with
    | .bypass a, _ => some ((f, true), [a])
    | .push0 a, nil => some ((cons a nil nil, false), [])
    | .push0 a, cons b c r => some ((cons a (cons b c nil) r, false), [])
    | .push1 _, nil => none
    | .push1 a, cons b c r => some ((cons b (cons a nil c) r, false), [])
    | .pop0, nil => none
    | .pop0, cons a c r =>
        if canPop then some ((append c r, true), [a]) else none
    | .pop1, cons a nil (cons b c r) =>
        if canPop then some ((cons a nil (append c r), true), [b]) else none
    | .pop1, _ => none

/-- Concrete top-two stack operations, with the same no-push/pop flag.
The stack itself has no comparison restriction. -/
def stackStep (act : Action) : SState → Option (SState × List Nat)
  | (w, canPop) => match act, w with
    | .bypass a, _ => some ((w, true), [a])
    | .push0 a, _ => some ((a :: w, false), [])
    | .push1 _, [] => none
    | .push1 a, b :: v => some ((b :: a :: v, false), [])
    | .pop0, [] => none
    | .pop0, a :: v => if canPop then some ((v, true), [a]) else none
    | .pop1, a :: b :: v => if canPop then some ((a :: v, true), [b]) else none
    | .pop1, _ => none

/-- Labels do not change which forest operations are available. -/
theorem erase_step (act : Action) (s : TState) :
    Option.map (fun p => eraseState p.1) (tokenStep act s) =
      forestStep (eraseAction act) (eraseState s) := by
  rcases s with ⟨f, b⟩
  cases act <;> cases f with
  | nil => simp [tokenStep, forestStep, eraseAction, eraseState, erase]
  | cons a c r =>
    cases c <;> cases r <;> cases b <;>
      simp [tokenStep, forestStep, eraseAction, eraseState, erase, erase_append]

/-- Every labelled-forest step is the indicated concrete stack operation,
with exactly the same emitted token. The converse is deliberately not claimed:
the forest forbids popping a child ahead of its parent. -/
theorem stack_step (act : Action) (s t : TState) (out : List Nat)
    (h : tokenStep act s = some (t, out)) :
    stackStep act (stackState s) = some (stackState t, out) := by
  rcases s with ⟨f, b⟩
  cases act <;> cases f with
  | nil =>
    simp [tokenStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩; simp [stackStep, stackState, tokens]
  | cons a c r =>
    cases c <;> cases r <;> cases b <;>
      simp [tokenStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [stackStep, stackState, tokens, tokens_append, List.append_assoc]

/-- One-step token conservation, even if token names are repeated. -/
theorem step_count (act : Action) (s t : TState) (out : List Nat)
    (h : tokenStep act s = some (t, out)) (a : Nat) :
    (tokens s.1).count a + (introduced act).count a =
      out.count a + (tokens t.1).count a := by
  rcases s with ⟨f, flag⟩
  cases act <;> cases f with
  | nil =>
    simp [tokenStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [tokens, introduced, List.count_cons, Nat.add_comm]
  | cons b c r =>
    cases c <;> cases r <;> cases flag <;>
      simp [tokenStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [tokens, introduced, tokens_append, List.count_cons,
      Nat.add_left_comm, Nat.add_comm]

def tokenRun : List Action → TState → Option (TState × List Nat)
  | [], s => some (s, [])
  | act :: acts, s => do
      let (t, out) ← tokenStep act s
      let (u, outs) ← tokenRun acts t
      pure (u, out ++ outs)

def stackRun : List Action → SState → Option (SState × List Nat)
  | [], s => some (s, [])
  | act :: acts, s => do
      let (t, out) ← stackStep act s
      let (u, outs) ← stackRun acts t
      pure (u, out ++ outs)

/-- Exact erasure of arbitrary labelled executions to unlabelled forest paths. -/
theorem erase_run (acts : List Action) (s : TState) :
    Option.map (fun p => eraseState p.1) (tokenRun acts s) =
      forestRun (acts.map eraseAction) (eraseState s) := by
  induction acts generalizing s with
  | nil => rfl
  | cons act acts ih =>
    have hs := erase_step act s
    cases h : tokenStep act s with
    | none => simp [h] at hs; simp [tokenRun, forestRun, h, ← hs]
    | some p =>
      rcases p with ⟨t, out⟩
      simp [h] at hs
      have ht := ih t
      cases hr : tokenRun acts t with
      | none => simp [hr] at ht; simp [tokenRun, forestRun, h, ← hs, ← ht, hr]
      | some p =>
        rcases p with ⟨u, outs⟩
        simp [hr] at ht
        simp [tokenRun, forestRun, h, ← hs, ← ht, hr]

/-- Every unlabelled forest path lifts for any prescribed input token names. -/
theorem lift_run (acts : List Action) (s : TState) (t : FState)
    (h : forestRun (acts.map eraseAction) (eraseState s) = some t) :
    ∃ u out, tokenRun acts s = some (u, out) ∧ eraseState u = t := by
  have hp := erase_run acts s
  cases hr : tokenRun acts s with
  | none => simp [hr, h] at hp
  | some p =>
    rcases p with ⟨u, out⟩
    refine ⟨u, out, rfl, ?_⟩
    simpa [hr, h] using hp

/-- Every token-labelled forest execution preserves concrete stack order and
emits precisely the same output list. -/
theorem stack_run (acts : List Action) (s t : TState) (out : List Nat)
    (h : tokenRun acts s = some (t, out)) :
    stackRun acts (stackState s) = some (stackState t, out) := by
  induction acts generalizing s t out with
  | nil => simp [tokenRun] at h; rcases h with ⟨rfl, rfl⟩; rfl
  | cons act acts ih =>
    cases hs : tokenStep act s with
    | none => simp [tokenRun, hs] at h
    | some p =>
      rcases p with ⟨u, o⟩
      cases hr : tokenRun acts u with
      | none => simp [tokenRun, hs, hr] at h
      | some p =>
        rcases p with ⟨v, os⟩
        simp [tokenRun, hs, hr] at h
        rcases h with ⟨rfl, rfl⟩
        have hfirst := stack_step act s u o hs
        have hrest := ih u v os hr
        simp [stackRun, hfirst, hrest]

/-- Complete conservation for every finite labelled execution. -/
theorem run_count (acts : List Action) (s t : TState) (out : List Nat)
    (h : tokenRun acts s = some (t, out)) (a : Nat) :
    (tokens s.1).count a + (inputs acts).count a =
      out.count a + (tokens t.1).count a := by
  induction acts generalizing s t out with
  | nil => simp [tokenRun] at h; rcases h with ⟨rfl, rfl⟩; simp [inputs]
  | cons act acts ih =>
    cases hs : tokenStep act s with
    | none => simp [tokenRun, hs] at h
    | some p =>
      rcases p with ⟨u, o⟩
      cases hr : tokenRun acts u with
      | none => simp [tokenRun, hs, hr] at h
      | some p =>
        rcases p with ⟨v, os⟩
        simp [tokenRun, hs, hr] at h
        rcases h with ⟨rfl, rfl⟩
        have hfirst := step_count act s u o hs a
        have hrest := ih u v os hr
        simp [inputs, List.flatMap_cons] at *
        omega

/-- A complete path outputs exactly a permutation of its introduced tokens.
Distinct introduction names therefore make output-rank labelling well-defined. -/
theorem complete_permutation (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out)) :
    (inputs acts).Perm out := by
  apply List.perm_iff_count.mpr
  intro a
  have hc := run_count acts (nil, b) (nil, c) out h a
  simpa [tokens] using hc

/-- Distinct introduced identifiers are each emitted once on a complete path. -/
theorem complete_nodup (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out))
    (hd : (inputs acts).Nodup) : out.Nodup := by
  exact (complete_permutation acts b c out h).nodup_iff.mp hd

#print axioms erase_step
#print axioms stack_step
#print axioms erase_run
#print axioms lift_run
#print axioms stack_run
#print axioms complete_permutation
#print axioms complete_nodup

end StackSorting.Labelled
