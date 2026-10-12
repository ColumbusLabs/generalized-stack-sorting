import OutputRanks

/-!
# Comparison obligations and canonical push positions

Every complete increasing-output forest trace respects all parent/descendant
inequalities. This yields canonical push slots after output-rank relabelling.
-/
namespace StackSorting.Labelled
open TForest

def Heap : TForest → Prop
  | nil => True
  | cons a c r => (∀ b ∈ tokens c, a < b) ∧ Heap c ∧ Heap r

def PushOK (act : Action) (s : TState) : Prop :=
  match act, s.1 with
  | .push0 a, cons b _ _ => a < b
  | .push1 a, cons b _ _ => b < a
  | _, _ => True

def PushTrace : List Action → TState → Prop
  | [], _ => True
  | act :: acts, s => match tokenStep act s with
      | none => False
      | some (t, _) => PushOK act s ∧ PushTrace acts t

theorem heap_append (f g : TForest) : Heap (append f g) ↔ Heap f ∧ Heap g := by
  induction f with
  | nil => simp [append, Heap]
  | cons a c r _ ihr => simp [append, Heap, ihr, and_assoc]

/-- Conservation for a complete suffix starting from an arbitrary forest. -/
theorem complete_from_permutation (acts : List Action) (s : TState) (c : Bool)
    (out : List Nat) (h : tokenRun acts s = some ((nil, c), out)) :
    (tokens s.1 ++ inputs acts).Perm out := by
  apply List.perm_iff_count.mpr
  intro a
  have hc := run_count acts s (nil, c) out h a
  simpa [tokens] using hc

theorem held_mem_output (acts : List Action) (s : TState) (c : Bool)
    (out : List Nat) (h : tokenRun acts s = some ((nil, c), out))
    (a : Nat) (ha : a ∈ tokens s.1) : a ∈ out := by
  exact (complete_from_permutation acts s c out h).mem_iff.mp
    (List.mem_append_left _ ha)

/-- Backwards heap preservation. The emitted token is smaller than all
survivors; for pushes this condition is vacuous, and the successor heap forces
the newly inserted comparison. -/
theorem heap_step_back (act : Action) (s t : TState) (out : List Nat)
    (h : tokenStep act s = some (t, out)) (ht : Heap t.1)
    (hbefore : ∀ a ∈ out, ∀ b ∈ tokens t.1, a < b) :
    Heap s.1 ∧ PushOK act s := by
  rcases s with ⟨f, flag⟩
  cases act with
  | bypass a =>
    simp [tokenStep] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨ht, trivial⟩
  | push0 a =>
    cases f with
    | nil => simp [Heap, PushOK]
    | cons b c r =>
      simp [tokenStep] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Heap, tokens] at ht
      exact ⟨⟨ht.2.1.1, ht.2.1.2, ht.2.2⟩, ht.1.1⟩
  | push1 a =>
    cases f with
    | nil => simp [tokenStep] at h
    | cons b c r =>
      simp [tokenStep] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Heap, tokens] at ht
      exact ⟨⟨ht.1.2, ht.2.1, ht.2.2⟩, ht.1.1⟩
  | pop0 =>
    cases f with
    | nil => simp [tokenStep] at h
    | cons a c r =>
      cases flag with
      | false => simp [tokenStep] at h
      | true =>
        simp [tokenStep] at h
        rcases h with ⟨rfl, rfl⟩
        have hc := (heap_append c r).mp ht
        refine ⟨⟨?_, hc.1, hc.2⟩, trivial⟩
        intro b hb
        exact hbefore a (by simp) b (by simp [tokens_append, hb])
  | pop1 =>
    cases f with
    | nil => simp [tokenStep] at h
    | cons a c r =>
      cases c with
      | cons _ _ _ => simp [tokenStep] at h
      | nil =>
        cases r with
        | nil => simp [tokenStep] at h
        | cons b d r =>
          cases flag with
          | false => simp [tokenStep] at h
          | true =>
            simp [tokenStep] at h
            rcases h with ⟨rfl, rfl⟩
            have hd : Heap (append d r) := ht.2.2
            have hdr := (heap_append d r).mp hd
            refine ⟨⟨by simp [tokens], trivial, ?_⟩, trivial⟩
            refine ⟨?_, hdr.1, hdr.2⟩
            intro z hz
            exact hbefore b (by simp) z (by simp [tokens, tokens_append, hz])

/-- All comparisons and all push choices in a successful increasing-output
forest trace are forced, without assuming canonicality. -/
theorem sorted_trace_heap (acts : List Action) (s : TState) (c : Bool)
    (out : List Nat) (h : tokenRun acts s = some ((nil, c), out))
    (hsorted : out.Pairwise (· < ·)) : Heap s.1 ∧ PushTrace acts s := by
  induction acts generalizing s out with
  | nil =>
    simp [tokenRun] at h
    rcases h with ⟨rfl, rfl⟩
    simp [Heap, PushTrace]
  | cons act acts ih =>
    cases hstep : tokenStep act s with
    | none => simp [tokenRun, hstep] at h
    | some p =>
      rcases p with ⟨t, os⟩
      cases hrun : tokenRun acts t with
      | none => simp [tokenRun, hstep, hrun] at h
      | some p =>
        rcases p with ⟨u, outs⟩
        simp [tokenRun, hstep, hrun] at h
        rcases h with ⟨rfl, rfl⟩
        have hparts := List.pairwise_append.mp hsorted
        have ht := ih t outs hrun hparts.2.1
        have hbefore : ∀ a ∈ os, ∀ b ∈ tokens t.1, a < b := by
          intro a ha b hb
          exact hparts.2.2 a ha b (held_mem_output acts t c outs hrun b hb)
        have hb := heap_step_back act s t os hstep ht.1 hbefore
        exact ⟨hb.1, by simp [PushTrace, hstep, hb.2, ht.2]⟩

/-- Output-rank labelling makes every nonbypass push a canonical push. -/
theorem ranked_pushes (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out))
    (hd : (inputs acts).Nodup) :
    PushTrace (acts.map (relabelAction (outputRank out))) (nil, b) := by
  have hnodup := complete_nodup acts b c out h hd
  have hr := relabel_run (outputRank out) acts (nil, b)
  simp [h, relabelState, relabelResult, relabel, map_outputRank out hnodup] at hr
  exact (sorted_trace_heap _ (nil, b) c _ hr List.pairwise_lt_range').2

#print axioms heap_step_back
#print axioms sorted_trace_heap
#print axioms ranked_pushes

end StackSorting.Labelled
