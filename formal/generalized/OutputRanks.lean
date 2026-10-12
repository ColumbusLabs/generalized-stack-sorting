import LabelledForest

/-!
# Output-rank relabelling

Relabelling token names commutes with the entire operational model. A complete
trace with distinct introduced identifiers can therefore be relabelled by its
output ranks, giving an increasing-output compressed stack trace. This certifies
the existence/ranking part of the inverse map, not canonicality or injectivity.
-/
namespace StackSorting.Labelled

open TForest

def relabel (g : Nat → Nat) : TForest → TForest
  | nil => nil
  | cons a c r => cons (g a) (relabel g c) (relabel g r)

def relabelState (g : Nat → Nat) (s : TState) : TState := (relabel g s.1, s.2)

def relabelAction (g : Nat → Nat) : Action → Action
  | .bypass a => .bypass (g a)
  | .push0 a => .push0 (g a)
  | .push1 a => .push1 (g a)
  | .pop0 => .pop0
  | .pop1 => .pop1

def relabelResult (g : Nat → Nat) (p : TState × List Nat) : TState × List Nat :=
  (relabelState g p.1, p.2.map g)

theorem relabel_append (g : Nat → Nat) (f h : TForest) :
    relabel g (append f h) = append (relabel g f) (relabel g h) := by
  induction f with
  | nil => rfl
  | cons a c r _ ihr => simp [append, relabel, ihr]

theorem relabel_step (g : Nat → Nat) (act : Action) (s : TState) :
    tokenStep (relabelAction g act) (relabelState g s) =
      Option.map (relabelResult g) (tokenStep act s) := by
  rcases s with ⟨f, b⟩
  cases act <;> cases f with
  | nil => simp [tokenStep, relabelAction, relabelState, relabelResult, relabel]
  | cons a c r =>
    cases c <;> cases r <;> cases b <;>
      simp [tokenStep, relabelAction, relabelState, relabelResult, relabel,
        relabel_append]

theorem relabel_run (g : Nat → Nat) (acts : List Action) (s : TState) :
    tokenRun (acts.map (relabelAction g)) (relabelState g s) =
      Option.map (relabelResult g) (tokenRun acts s) := by
  induction acts generalizing s with
  | nil => rfl
  | cons act acts ih =>
    have hs := relabel_step g act s
    cases h : tokenStep act s with
    | none => simp [h] at hs; simp [tokenRun, h, hs]
    | some p =>
      rcases p with ⟨t, out⟩
      simp [h, relabelResult] at hs
      have ht := ih t
      cases hr : tokenRun acts t with
      | none => simp [hr] at ht; simp [tokenRun, h, hs, ht, hr]
      | some p =>
        rcases p with ⟨u, outs⟩
        simp [hr, relabelResult] at ht
        simp [tokenRun, h, hs, ht, hr, relabelResult]

/-- Ranks are one-based, so the output is exactly 1,2,...,n. -/
def outputRank (out : List Nat) (a : Nat) : Nat := out.idxOf a + 1

theorem map_outputRank (out : List Nat) (hd : out.Nodup) :
    out.map (outputRank out) = List.range' 1 out.length := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [outputRank, hd.idxOf_getElem, Nat.add_comm]

/-- The inverse construction produces an increasing-output compressed stack trace
(in the model with an explicit bypass operation), for every complete forest path with
pairwise distinct input identifiers. -/
theorem ranked_complete_stack (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out))
    (hd : (inputs acts).Nodup) :
    stackRun (acts.map (relabelAction (outputRank out))) ([], b) =
      some (([], c), List.range' 1 out.length) := by
  have hnodup := complete_nodup acts b c out h hd
  have hr := relabel_run (outputRank out) acts (nil, b)
  simp [h, relabelState, relabelResult, relabel, map_outputRank out hnodup] at hr
  have hs := stack_run (acts.map (relabelAction (outputRank out)))
    (nil, b) (nil, c) (List.range' 1 out.length) hr
  simpa [stackState, tokens] using hs

#print axioms relabel_step
#print axioms relabel_run
#print axioms map_outputRank
#print axioms ranked_complete_stack

end StackSorting.Labelled
