import EagerTraces

/-!
# Determinacy of increasing-output forest traces

The next operation is determined by held tokens, unread input and desired
output. This yields uniqueness of complete increasing-output traces.
-/
namespace StackSorting.Labelled
open TForest

def popChoice (held : List Nat) (o : Nat) : Option Action :=
  match held with
  | [] => none
  | a :: rest =>
    if a = o then some .pop0 else
      match rest with
      | [] => none
      | b :: _ => if b = o then some .pop1 else none

def nextAction (held input output : List Nat) : Option Action :=
  match output with
  | [] => none
  | o :: _ =>
    if o ∈ held then popChoice held o else
      match input with
      | [] => none
      | a :: _ =>
        if a = o then some (.bypass a) else
          match held with
          | [] => some (.push0 a)
          | b :: _ => if a < b then some (.push0 a) else some (.push1 a)

theorem split_run (act : Action) (acts : List Action) (s t : TState)
    (out : List Nat) (h : tokenRun (act :: acts) s = some (t, out)) :
    ∃ u emitted tail, tokenStep act s = some (u, emitted) ∧
      tokenRun acts u = some (t, tail) ∧ emitted ++ tail = out := by
  cases hs : tokenStep act s with
  | none => simp [tokenRun, hs] at h
  | some p =>
    rcases p with ⟨u, emitted⟩
    cases hr : tokenRun acts u with
    | none => simp [tokenRun, hs, hr] at h
    | some p =>
      rcases p with ⟨v, tail⟩
      simp [tokenRun, hs, hr] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨u, emitted, tail, rfl, hr, rfl⟩

/-- Deterministic next action, derived from the proved comparisons, eager output,
and bypass normalization rather than imposed as an extra assumption. -/
theorem first_action (act : Action) (acts : List Action) (s : TState) (c : Bool)
    (o : Nat) (outs : List Nat)
    (h : tokenRun (act :: acts) s = some ((nil, c), o :: outs))
    (hsorted : (o :: outs).Pairwise (· < ·)) :
    nextAction (tokens s.1) (inputs (act :: acts)) (o :: outs) = some act := by
  have hnodup : (o :: outs).Nodup := hsorted.imp (fun hlt => Nat.ne_of_lt hlt)
  have hd := (complete_from_permutation (act :: acts) s c (o :: outs) h).nodup_iff.mpr hnodup
  have hi : (inputs (act :: acts)).Nodup := (List.pairwise_append.mp hd).2.1
  obtain ⟨u, emitted, tail, hstep, hrun, hout⟩ := split_run act acts s (nil, c) _ h
  have hp : PushOK act s := by
    have ht := (sorted_trace_heap (act :: acts) s c _ h hsorted).2
    simp only [PushTrace, hstep] at ht
    exact ht.1
  rcases s with ⟨f, flag⟩
  cases act with
  | bypass a =>
    simp [tokenStep] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp at hout
    rcases hout with ⟨rfl, rfl⟩
    have hnot : a ∉ tokens f := by
      intro hm
      exact (List.pairwise_append.mp hd).2.2 a hm a
        (by simp [inputs, introduced]) rfl
    simp [nextAction, hnot, inputs, introduced]
  | push0 a =>
    have hnot : o ∉ tokens f := by
      intro hm
      have he := eager_front (.push0 a) acts (f, flag) (nil, c) o outs h hd hm
      exact he
    have hne : a ≠ o := by
      intro heq
      subst a
      exact push_first_impossible (.push0 o) acts (f, flag) (nil, c) o outs h hi (Or.inl rfl)
    cases f with
    | nil => simp [nextAction, tokens, inputs, introduced, hne]
    | cons b d r =>
      change a < b at hp
      simp only [nextAction, hnot, ite_false]
      simp [inputs, introduced, tokens, hne, hp]
  | push1 a =>
    have hnot : o ∉ tokens f := by
      intro hm
      have he := eager_front (.push1 a) acts (f, flag) (nil, c) o outs h hd hm
      exact he
    have hne : a ≠ o := by
      intro heq
      subst a
      exact push_first_impossible (.push1 o) acts (f, flag) (nil, c) o outs h hi (Or.inr rfl)
    cases f with
    | nil => simp [tokenStep] at hstep
    | cons b d r =>
      change b < a at hp
      have hn : ¬ a < b := Nat.not_lt.mpr (Nat.le_of_lt hp)
      simp only [nextAction, hnot, ite_false]
      simp [inputs, introduced, tokens, hne, hn]
  | pop0 =>
    cases f with
    | nil => simp [tokenStep] at hstep
    | cons a d r =>
      cases flag with
      | false => simp [tokenStep] at hstep
      | true =>
        simp [tokenStep] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp at hout
        rcases hout with ⟨rfl, rfl⟩
        simp [nextAction, tokens, popChoice]
  | pop1 =>
    cases f with
    | nil => simp [tokenStep] at hstep
    | cons a d r =>
      cases d with
      | cons _ _ _ => simp [tokenStep] at hstep
      | nil =>
        cases r with
        | nil => simp [tokenStep] at hstep
        | cons b e r =>
          cases flag with
          | false => simp [tokenStep] at hstep
          | true =>
            simp [tokenStep] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            simp at hout
            rcases hout with ⟨rfl, rfl⟩
            have hheld := (List.pairwise_append.mp hd).1
            have hne : a ≠ b := by
              intro heq
              subst a
              have hnot := (List.nodup_cons.mp hheld).1
              exact hnot (by simp [tokens])
            simp [nextAction, tokens, popChoice, hne]

/-- No nonempty complete trace can have empty output. -/
theorem empty_output_run (acts : List Action) (s : TState) (c : Bool)
    (h : tokenRun acts s = some ((nil, c), [])) : acts = [] ∧ s.1 = nil := by
  have hp := (complete_from_permutation acts s c [] h).eq_nil
  have hp' := List.append_eq_nil_iff.mp hp
  rcases s with ⟨f, flag⟩
  have hf : f = nil := by
    cases f with
    | nil => rfl
    | cons a d r => simp [tokens] at hp'
  subst f
  refine ⟨?_, rfl⟩
  cases acts with
  | nil => rfl
  | cons act acts =>
    cases act <;>
      simp [inputs, introduced] at hp'
    all_goals simp [tokenRun, tokenStep] at h

/-- Two complete increasing-output forest traces with the same initial state,
unread input list and output list have exactly the same labelled operations. -/
theorem complete_trace_unique (as bs : List Action) (s : TState) (c d : Bool)
    (out : List Nat)
    (ha : tokenRun as s = some ((nil, c), out))
    (hb : tokenRun bs s = some ((nil, d), out))
    (hin : inputs as = inputs bs) (hsorted : out.Pairwise (· < ·)) : as = bs := by
  induction as generalizing bs s out with
  | nil =>
    simp [tokenRun] at ha
    rcases ha with ⟨rfl, rfl⟩
    exact (empty_output_run bs (nil, c) d hb).1.symm
  | cons act acts ih =>
    cases out with
    | nil =>
      have he := (empty_output_run (act :: acts) s c ha).1
      simp at he
    | cons o outs =>
      cases bs with
      | nil => simp [tokenRun] at hb
      | cons act' acts' =>
        have hfa := first_action act acts s c o outs ha hsorted
        have hfb := first_action act' acts' s d o outs hb hsorted
        rw [hin] at hfa
        have heq : act = act' := Option.some.inj (hfa.symm.trans hfb)
        subst act'
        obtain ⟨u, emitted, tail, hs, hr, hout⟩ := split_run act acts s (nil, c) _ ha
        obtain ⟨v, emitted', tail', hs', hr', hout'⟩ := split_run act acts' s (nil, d) _ hb
        have hpair : (u, emitted) = (v, emitted') := Option.some.inj (hs.symm.trans hs')
        cases hpair
        have htail : tail = tail' := List.append_cancel_left (hout.trans hout'.symm)
        subst tail'
        have hinput : inputs acts = inputs acts' := by
          change introduced act ++ inputs acts = introduced act ++ inputs acts' at hin
          exact List.append_cancel_left hin
        have hsort_tail : tail.Pairwise (· < ·) := by
          rw [← hout] at hsorted
          exact (List.pairwise_append.mp hsorted).2.1
        have hrest := ih acts' u tail hr hr' hinput hsort_tail
        simp [hrest]

theorem inputs_relabel (g : Nat → Nat) (acts : List Action) :
    inputs (acts.map (relabelAction g)) = (inputs acts).map g := by
  induction acts with
  | nil => rfl
  | cons act acts ih =>
    cases act <;> simp [inputs, introduced, relabelAction] at ih ⊢ <;> exact ih

theorem erase_relabel_action (g : Nat → Nat) (act : Action) :
    eraseAction (relabelAction g act) = eraseAction act := by
  cases act <;> rfl

/-- Injectivity of the inverse construction on operation paths: if complete
paths with distinct introduction identifiers yield the same output-ranked input
permutation, their operation labels coincide. -/
theorem ranked_operation_injective (as bs : List Action) (c d : Bool)
    (out out' : List Nat)
    (ha : tokenRun as (nil, true) = some ((nil, c), out))
    (hb : tokenRun bs (nil, true) = some ((nil, d), out'))
    (hda : (inputs as).Nodup) (hdb : (inputs bs).Nodup)
    (hin : inputs (as.map (relabelAction (outputRank out))) =
      inputs (bs.map (relabelAction (outputRank out')))) :
    as.map eraseAction = bs.map eraseAction := by
  have hlenin := congrArg List.length hin
  simp only [inputs_relabel, List.length_map] at hlenin
  have hlen : out.length = out'.length :=
    (complete_permutation as true c out ha).length_eq.symm.trans
      (hlenin.trans (complete_permutation bs true d out' hb).length_eq)
  have hra := relabel_run (outputRank out) as (nil, true)
  have hrb := relabel_run (outputRank out') bs (nil, true)
  have hna := complete_nodup as true c out ha hda
  have hnb := complete_nodup bs true d out' hb hdb
  simp [ha, relabelState, relabelResult, relabel, map_outputRank out hna] at hra
  simp [hb, relabelState, relabelResult, relabel, map_outputRank out' hnb] at hrb
  rw [hlen] at hra
  have hu := complete_trace_unique _ _ (nil, true) c d _ hra hrb hin List.pairwise_lt_range'
  have he := congrArg (List.map eraseAction) hu
  simpa only [List.map_map, Function.comp_def, erase_relabel_action] using he

#print axioms first_action
#print axioms empty_output_run
#print axioms complete_trace_unique
#print axioms ranked_operation_injective

end StackSorting.Labelled
