import ForestCompleteness

/-! # A fixed operation skeleton determines the input from the output -/
namespace StackSorting.Labelled

def rawKind : RawOp → Op
  | .push0 _ => .push0
  | .push1 _ => .push1
  | .pop0 => .pop0
  | .pop1 => .pop1

def emitWeight : RawOp → Nat
  | .push0 _ | .push1 _ => 0
  | .pop0 | .pop1 => 1

theorem emitWeight_kind (p q : RawOp) (h : rawKind p = rawKind q) :
    emitWeight p = emitWeight q := by
  cases p <;> cases q <;> simp [rawKind] at h <;> rfl

theorem rawStep_output_length (op : RawOp) (s t out : List Nat)
    (h : rawStep op s = some (t, out)) : out.length = emitWeight op := by
  cases op <;> cases s with
  | nil =>
    simp [rawStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl
  | cons a rest =>
    cases rest <;> simp [rawStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- A raw operation can be reversed when its slot, final stack and emitted
output are specified. Push payloads are recovered rather than assumed equal. -/
theorem rawStep_reverse (p q : RawOp) (s u t out : List Nat)
    (hk : rawKind p = rawKind q)
    (hp : rawStep p s = some (t, out)) (hq : rawStep q u = some (t, out)) :
    s = u ∧ rawIntroduced p = rawIntroduced q := by
  cases p <;> cases q <;> simp [rawKind] at hk
  case push0.push0 a b =>
    simp [rawStep] at hp hq
    rcases hp with ⟨rfl, rfl⟩
    simp at hq
    rcases hq with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  case push1.push1 a b =>
    cases s with
    | nil => simp [rawStep] at hp
    | cons c s =>
      cases u with
      | nil => simp [rawStep] at hq
      | cons d u =>
        simp [rawStep] at hp hq
        rcases hp with ⟨rfl, rfl⟩
        simp at hq
        rcases hq with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  case pop0.pop0 =>
    cases s with
    | nil => simp [rawStep] at hp
    | cons a s =>
      cases u with
      | nil => simp [rawStep] at hq
      | cons b u =>
        simp [rawStep] at hp hq
        rcases hp with ⟨rfl, rfl⟩
        rcases hq with ⟨rfl, he⟩
        simp at he
        subst b
        exact ⟨rfl, rfl⟩
  case pop1.pop1 =>
    cases s with
    | nil => simp [rawStep] at hp
    | cons a s =>
      cases s with
      | nil => simp [rawStep] at hp
      | cons b s =>
        cases u with
        | nil => simp [rawStep] at hq
        | cons c u =>
          cases u with
          | nil => simp [rawStep] at hq
          | cons d u =>
            simp [rawStep] at hp hq
            rcases hp with ⟨rfl, rfl⟩
            simp at hq
            rcases hq with ⟨⟨rfl, rfl⟩, rfl⟩
            exact ⟨rfl, rfl⟩

/-- Full wiring uniqueness, valid without sorting or distinctness assumptions. -/
theorem rawRun_reverse (as bs : List RawOp) (s u t out : List Nat)
    (hk : as.map rawKind = bs.map rawKind)
    (ha : rawRun as s = some (t, out)) (hb : rawRun bs u = some (t, out)) :
    s = u ∧ rawInputs as = rawInputs bs := by
  induction as generalizing bs s u t out with
  | nil =>
    have hbnil : bs = [] := by simpa using hk.symm
    subst bs
    simp [rawRun] at ha hb
    rcases ha with ⟨rfl, rfl⟩
    simp at hb
    exact ⟨hb.symm, rfl⟩
  | cons a as ih =>
    cases bs with
    | nil => simp at hk
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨s', emitted, tail, hs, hr, ho⟩ := raw_split_run a as s t out ha
      obtain ⟨u', emitted', tail', hs', hr', ho'⟩ := raw_split_run b bs u t out hb
      have hlen : emitted.length = emitted'.length :=
        (rawStep_output_length a s s' emitted hs).trans
          ((emitWeight_kind a b hk.1).trans (rawStep_output_length b u u' emitted' hs').symm)
      have hparts := List.append_inj (ho.trans ho'.symm) hlen
      rcases hparts with ⟨rfl, rfl⟩
      have hrest := ih bs s' u' t tail hk.2 hr hr'
      have hfirst := rawStep_reverse a b s u u' emitted hk.1 (by simpa [hrest.1] using hs) hs'
      refine ⟨hfirst.1, ?_⟩
      change rawIntroduced a ++ rawInputs as = rawIntroduced b ++ rawInputs bs
      rw [hfirst.2, hrest.2]

def expandKind : Op → List Op
  | .bypass => [.push0, .pop0]
  | op => [op]

theorem rawKinds_expand (acts : List Action) :
    (expandTrace acts).map rawKind = (acts.map eraseAction).flatMap expandKind := by
  induction acts with
  | nil => rfl
  | cons act acts ih =>
    cases act <;> simp [expandTrace, expandAction, rawKind, eraseAction, expandKind] at ih ⊢ <;> exact ih

/-- Same forest operation labels and same complete output imply the same
input payloads, even when the two token-name assignments were different. -/
theorem forest_wiring_unique (as bs : List Action) (b c d : Bool) (out : List Nat)
    (ha : tokenRun as (TForest.nil, b) = some ((TForest.nil, c), out))
    (hb : tokenRun bs (TForest.nil, b) = some ((TForest.nil, d), out))
    (hk : as.map eraseAction = bs.map eraseAction) : inputs as = inputs bs := by
  have hsa := stack_run as (TForest.nil, b) (TForest.nil, c) out ha
  have hsb := stack_run bs (TForest.nil, b) (TForest.nil, d) out hb
  have hra := expand_run as ([], b) ([], c) out hsa
  have hrb := expand_run bs ([], b) ([], d) out hsb
  have hkind : (expandTrace as).map rawKind = (expandTrace bs).map rawKind := by
    rw [rawKinds_expand, rawKinds_expand, hk]
  have hi := (rawRun_reverse _ _ [] [] [] out hkind hra hrb).2
  simpa only [expand_inputs] using hi

#print axioms rawStep_reverse
#print axioms rawRun_reverse
#print axioms forest_wiring_unique

end StackSorting.Labelled
