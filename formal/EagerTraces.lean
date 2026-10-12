import OrderedTraces

/-!
# Eager-output canonicality

The first output after a disabled-pop state must come from unread input.
Combined with token conservation and distinctness, this proves that no held
next-output token is delayed by a push or bypass.
-/
namespace StackSorting.Labelled
open TForest

def IsPop : Action → Prop
  | .pop0 | .pop1 => True
  | _ => False

/-- Starting immediately after a push, the first emitted token must be an
introduced input token, since only a bypass can first re-enable pops. -/
theorem disabled_first_input (acts : List Action) (f : TForest)
    (t : TState) (a : Nat) (out : List Nat)
    (h : tokenRun acts (f, false) = some (t, a :: out)) : a ∈ inputs acts := by
  induction acts generalizing f t a out with
  | nil => simp [tokenRun] at h
  | cons act acts ih =>
    cases act with
    | bypass b =>
      cases hr : tokenRun acts (f, true) with
      | none => simp [tokenRun, tokenStep, hr] at h
      | some p =>
        rcases p with ⟨u, os⟩
        simp [tokenRun, tokenStep, hr] at h
        rcases h with ⟨_, rfl, _⟩
        simp [inputs, introduced]
    | push0 b =>
      cases f with
      | nil =>
        have hr : tokenRun acts (cons b nil nil, false) = some (t, a :: out) := by
          simpa [tokenRun, tokenStep, Prod.eta] using h
        have hi := ih _ _ _ _ hr
        change a ∈ b :: inputs acts
        exact List.mem_cons_of_mem b hi
      | cons d c r =>
        have hr : tokenRun acts (cons b (cons d c nil) r, false) = some (t, a :: out) := by
          simpa [tokenRun, tokenStep, Prod.eta] using h
        have hi := ih _ _ _ _ hr
        change a ∈ b :: inputs acts
        exact List.mem_cons_of_mem b hi
    | push1 b =>
      cases f with
      | nil => simp [tokenRun, tokenStep] at h
      | cons d c r =>
        have hr : tokenRun acts (cons d (cons b nil c) r, false) = some (t, a :: out) := by
          simpa [tokenRun, tokenStep, Prod.eta] using h
        have hi := ih _ _ _ _ hr
        change a ∈ b :: inputs acts
        exact List.mem_cons_of_mem b hi
    | pop0 => cases f <;> simp [tokenRun, tokenStep] at h
    | pop1 =>
      cases f with
      | nil => simp [tokenRun, tokenStep] at h
      | cons a c r => cases c <;> cases r <;> simp [tokenRun, tokenStep] at h

/-- A push or bypass cannot delay an already-held next-output token. -/
theorem eager_front (act : Action) (acts : List Action) (s t : TState)
    (a : Nat) (out : List Nat)
    (h : tokenRun (act :: acts) s = some (t, a :: out))
    (hd : (tokens s.1 ++ inputs (act :: acts)).Nodup)
    (ha : a ∈ tokens s.1) : IsPop act := by
  have hdis : a ∉ inputs (act :: acts) := by
    intro hai
    have hn := List.pairwise_append.mp hd
    exact hn.2.2 a ha a hai rfl
  rcases s with ⟨f, flag⟩
  cases act with
  | pop0 => trivial
  | pop1 => trivial
  | bypass b =>
    cases hr : tokenRun acts (f, true) with
    | none => simp [tokenRun, tokenStep, hr] at h
    | some p =>
      rcases p with ⟨u, os⟩
      simp [tokenRun, tokenStep, hr] at h
      rcases h with ⟨_, rfl, _⟩
      exact False.elim (hdis (by simp [inputs, introduced]))
  | push0 b =>
    cases f with
    | nil => simp [tokens] at ha
    | cons d c r =>
      have hr : tokenRun acts (cons b (cons d c nil) r, false) = some (t, a :: out) := by
        simpa [tokenRun, tokenStep, Prod.eta] using h
      have hi := disabled_first_input acts _ t a out hr
      exact False.elim (hdis (by
        change a ∈ b :: inputs acts
        exact List.mem_cons_of_mem b hi))
  | push1 b =>
    cases f with
    | nil => simp [tokens] at ha
    | cons d c r =>
      have hr : tokenRun acts (cons d (cons b nil c) r, false) = some (t, a :: out) := by
        simpa [tokenRun, tokenStep, Prod.eta] using h
      have hi := disabled_first_input acts _ t a out hr
      exact False.elim (hdis (by
        change a ∈ b :: inputs acts
        exact List.mem_cons_of_mem b hi))

/-- A newly introduced next-output token cannot be stored for later: the
compressed history must use a bypass. -/
theorem push_first_impossible (act : Action) (acts : List Action) (s t : TState)
    (a : Nat) (out : List Nat)
    (h : tokenRun (act :: acts) s = some (t, a :: out))
    (hd : (inputs (act :: acts)).Nodup)
    (hp : act = .push0 a ∨ act = .push1 a) : False := by
  rcases s with ⟨f, flag⟩
  rcases hp with rfl | rfl
  · change (a :: inputs acts).Nodup at hd
    have hnot := (List.nodup_cons.mp hd).1
    cases f with
    | nil =>
      have hr : tokenRun acts (cons a nil nil, false) = some (t, a :: out) := by
        simpa [tokenRun, tokenStep, Prod.eta] using h
      exact hnot (disabled_first_input acts _ t a out hr)
    | cons b c r =>
      have hr : tokenRun acts (cons a (cons b c nil) r, false) = some (t, a :: out) := by
        simpa [tokenRun, tokenStep, Prod.eta] using h
      exact hnot (disabled_first_input acts _ t a out hr)
  · change (a :: inputs acts).Nodup at hd
    have hnot := (List.nodup_cons.mp hd).1
    cases f with
    | nil => simp [tokenRun, tokenStep] at h
    | cons b c r =>
      have hr : tokenRun acts (cons b (cons a nil c) r, false) = some (t, a :: out) := by
        simpa [tokenRun, tokenStep, Prod.eta] using h
      exact hnot (disabled_first_input acts _ t a out hr)

def EagerTrace : List Action → TState → List Nat → Prop
  | [], _, _ => True
  | act :: acts, s, out =>
      (∀ a tail, out = a :: tail → a ∈ tokens s.1 → IsPop act) ∧
      match tokenStep act s with
      | none => False
      | some (t, emitted) => EagerTrace acts t (out.drop emitted.length)

theorem sorted_trace_eager (acts : List Action) (s : TState) (c : Bool)
    (out : List Nat) (h : tokenRun acts s = some ((nil, c), out))
    (hsorted : out.Pairwise (· < ·)) : EagerTrace acts s out := by
  induction acts generalizing s out with
  | nil => trivial
  | cons act acts ih =>
    have hnodup : out.Nodup := hsorted.imp (fun hlt => Nat.ne_of_lt hlt)
    have hd := (complete_from_permutation (act :: acts) s c out h).nodup_iff.mpr hnodup
    have heager : ∀ a tail, out = a :: tail → a ∈ tokens s.1 → IsPop act := by
      intro a tail heq ha
      subst out
      exact eager_front act acts s (nil, c) a tail h hd ha
    refine ⟨heager, ?_⟩
    cases hs : tokenStep act s with
    | none => simp [tokenRun, hs] at h
    | some p =>
      rcases p with ⟨t, emitted⟩
      cases hr : tokenRun acts t with
      | none => simp [tokenRun, hs, hr] at h
      | some p =>
        rcases p with ⟨u, outs⟩
        simp [tokenRun, hs, hr] at h
        rcases h with ⟨rfl, rfl⟩
        have ht := ih t outs hr (List.pairwise_append.mp hsorted).2.1
        simpa [hs] using ht

/-- The entire output-ranked trace obeys both canonical push inequalities and
eager output at every state. The original machine equivalence and injectivity
are separate results. -/
theorem ranked_pushes_and_eager (acts : List Action) (b c : Bool) (out : List Nat)
    (h : tokenRun acts (nil, b) = some ((nil, c), out))
    (hd : (inputs acts).Nodup) :
    PushTrace (acts.map (relabelAction (outputRank out))) (nil, b) ∧
    EagerTrace (acts.map (relabelAction (outputRank out))) (nil, b)
      (List.range' 1 out.length) := by
  have hnodup := complete_nodup acts b c out h hd
  have hr := relabel_run (outputRank out) acts (nil, b)
  simp [h, relabelState, relabelResult, relabel, map_outputRank out hnodup] at hr
  exact ⟨ranked_pushes acts b c out h hd,
    sorted_trace_eager _ (nil, b) c _ hr List.pairwise_lt_range'⟩

#print axioms disabled_first_input
#print axioms eager_front
#print axioms push_first_impossible
#print axioms sorted_trace_eager
#print axioms ranked_pushes_and_eager

end StackSorting.Labelled
