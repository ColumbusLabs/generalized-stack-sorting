import ForestCompleteness

/-! Physical capacity for the original no-bypass machine. -/
namespace StackSorting.Labelled
open TForest

/-- Every visited physical stack, including the initial one, has at most H tokens.
Invalid operations do not fit. There is no compressed bypass in this predicate. -/
def RawFits (H : Nat) : List RawOp → List Nat → Prop
  | [], held => held.length ≤ H
  | op :: ops, held => held.length ≤ H ∧ match rawStep op held with
    | none => False
    | some (t, _) => RawFits H ops t

/-- Input positions are zero-based internally: r entries have already been read. -/
def InputBound (H : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | r, a :: input => r + 2 ≤ a + H ∧ InputBound H (r+1) input

def CanSortWithin (H : Nat) (input : List Nat) (n : Nat) : Prop :=
  ∃ ops, rawRun ops [] = some ([], List.range' 1 n) ∧
    rawInputs ops = input ∧ RawFits H ops []

/-- A compressed introducing step needs one spare physical slot, even a bypass. -/
def ForestFits (H : Nat) : List Action → TState → Prop
  | [], s => (tokens s.1).length ≤ H
  | act :: acts, s => (tokens s.1).length ≤ H ∧
      (introduced act ≠ [] → (tokens s.1).length + 1 ≤ H) ∧
      match tokenStep act s with
      | none => False
      | some (t, _) => ForestFits H acts t

theorem inputBound_mem (H r a : Nat) (input : List Nat)
    (h : InputBound H r input) (ha : a ∈ input) : r + 2 ≤ a + H := by
  induction input generalizing r with
  | nil => simp at ha
  | cons b input ih =>
    rcases h with ⟨hb, ht⟩
    rcases List.mem_cons.mp ha with he | hm
    · subst b; exact hb
    · have hz := ih (r+1) ht hm; omega

theorem rawFits_head (H : Nat) (ops : List RawOp) (held : List Nat)
    (h : RawFits H ops held) : held.length ≤ H := by
  cases ops with
  | nil => exact h
  | cons op ops => exact h.1

theorem rawFits_append (H : Nat) (as bs : List RawOp) (s t out : List Nat)
    (hr : rawRun as s = some (t,out)) :
    RawFits H (as ++ bs) s ↔ RawFits H as s ∧ RawFits H bs t := by
  induction as generalizing s out with
  | nil =>
    simp [rawRun] at hr
    rcases hr with ⟨rfl, rfl⟩
    simp only [List.nil_append, RawFits]
    exact ⟨fun h => ⟨rawFits_head _ _ _ h, h⟩, fun h => h.2⟩
  | cons op ops ih =>
    obtain ⟨u, emitted, tail, hs, ht, _⟩ := raw_split_run op ops s t out hr
    simp only [List.cons_append, RawFits, hs]
    rw [ih u tail ht]
    exact and_assoc.symm

theorem range_cons (q n : Nat) : List.range' q (n+1) = q :: List.range' (q+1) n := by
  simp [List.range'_succ]

theorem raw_bound_input (H : Nat) (ops : List RawOp) (held : List Nat)
    (q n r : Nat) (hr : rawRun ops held = some ([], List.range' q n))
    (hb : RawFits H ops held) (balance : held.length + q = r+1) :
    InputBound H r (rawInputs ops) := by
  induction ops generalizing held q n r with
  | nil => trivial
  | cons op ops ih =>
    obtain ⟨u, emitted, tail, hs, ht, ho⟩ := raw_split_run op ops held [] _ hr
    have hfit : RawFits H ops u := by simpa only [RawFits, hs] using hb.2
    cases op with
    | push0 a =>
      simp [rawStep] at hs
      rcases hs with ⟨rfl,rfl⟩
      simp at ho
      subst tail
      have ha : a ∈ List.range' q n := (raw_complete_permutation ops (a::held) _ ht).mem_iff.mp (by simp)
      have haq : q ≤ a := by
        obtain ⟨i, _, he⟩ := List.mem_range'.mp ha
        omega
      have hh := rawFits_head _ _ _ hfit
      change r+2 ≤ a+H ∧ InputBound H (r+1) (rawInputs ops)
      refine ⟨by simp only [List.length_cons] at hh; omega, ?_⟩
      apply ih _ q n (r+1) ht hfit
      simp only [List.length_cons]; omega
    | push1 a =>
      cases held with
      | nil => simp [rawStep] at hs
      | cons b held =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl,rfl⟩
        simp at ho
        subst tail
        have ha : a ∈ List.range' q n :=
          (raw_complete_permutation ops (b::a::held) _ ht).mem_iff.mp (by simp)
        have haq : q ≤ a := by
          obtain ⟨i, _, he⟩ := List.mem_range'.mp ha
          omega
        have hh := rawFits_head _ _ _ hfit
        change r+2 ≤ a+H ∧ InputBound H (r+1) (rawInputs ops)
        refine ⟨by simp only [List.length_cons] at balance hh; omega, ?_⟩
        apply ih _ q n (r+1) ht hfit
        simp only [List.length_cons] at balance ⊢; omega
    | pop0 =>
      cases held with
      | nil => simp [rawStep] at hs
      | cons a held =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl,rfl⟩
        cases n with
        | zero => simp at ho
        | succ n =>
          rw [range_cons] at ho
          simp at ho
          rcases ho with ⟨ha, he⟩
          subst a; subst tail
          apply ih held (q+1) n r ht hfit
          simp only [List.length_cons] at balance; omega
    | pop1 =>
      cases held with
      | nil => simp [rawStep] at hs
      | cons a held =>
        cases held with
        | nil => simp [rawStep] at hs
        | cons b held =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl,rfl⟩
          cases n with
          | zero => simp at ho
          | succ n =>
            rw [range_cons] at ho
            simp at ho
            rcases ho with ⟨hb, he⟩
            subst b; subst tail
            apply ih (a::held) (q+1) n r ht hfit
            simp only [List.length_cons] at balance ⊢; omega



theorem inputBound_append (H r : Nat) (as bs : List Nat) :
    InputBound H r (as ++ bs) ↔
      InputBound H r as ∧ InputBound H (r+as.length) bs := by
  induction as generalizing r with
  | nil => simp [InputBound]
  | cons a as ih =>
    simp only [List.cons_append, InputBound, List.length_cons]
    rw [ih]
    have he : r + (as.length+1) = r+1+as.length := by omega
    rw [he]
    exact and_assoc.symm

theorem stackStep_length (act : Action) (s t : SState) (out : List Nat)
    (h : stackStep act s = some (t,out)) :
    s.1.length + (introduced act).length = out.length + t.1.length := by
  rcases s with ⟨held, flag⟩
  cases act <;> cases held with
  | nil =>
    simp [stackStep] at h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [introduced] <;> omega
  | cons a rest =>
    cases rest <;> cases flag <;> simp [stackStep] at h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [introduced] <;> omega

theorem tokenStep_length (act : Action) (s t : TState) (out : List Nat)
    (h : tokenStep act s = some (t,out)) :
    (tokens s.1).length + (introduced act).length =
      out.length + (tokens t.1).length := by
  exact stackStep_length act (stackState s) (stackState t) out (stack_step act s t out h)

theorem forest_bound (H : Nat) (acts : List Action) (s : TState)
    (c : Bool) (q n r : Nat)
    (hr : tokenRun acts s = some ((nil,c), List.range' q n))
    (hb : InputBound H r (inputs acts))
    (balance : (tokens s.1).length + q = r+1)
    (hh : (tokens s.1).length ≤ H) : ForestFits H acts s := by
  induction acts generalizing s q n r with
  | nil => exact hh
  | cons act acts ih =>
    obtain ⟨u, emitted, tail, hs, ht, ho⟩ := split_run act acts s (nil,c) _ hr
    have hsz := tokenStep_length act s u emitted hs
    have hspare : introduced act ≠ [] → (tokens s.1).length+1 ≤ H := by
      intro hintro
      cases n with
      | zero =>
        have he := (empty_output_run (act::acts) s c hr).1
        simp at he
      | succ n =>
        have hrc : tokenRun (act::acts) s = some ((nil,c), q::List.range' (q+1) n) := by
          simpa only [range_cons] using hr
        have hsorted : (q::List.range' (q+1) n).Pairwise (· < ·) := by
          rw [← range_cons]; exact List.pairwise_lt_range'
        have hd := (complete_from_permutation (act::acts) s c _ hrc).nodup_iff.mpr
          (hsorted.imp (fun h => Nat.ne_of_lt h))
        have hnoth : q ∉ tokens s.1 := by
          intro hm
          have he := eager_front act acts s (nil,c) q _ hrc hd hm
          cases act <;> simp [IsPop, introduced] at he hintro
        have hmem : q ∈ inputs (act::acts) := by
          have hm : q ∈ tokens s.1 ++ inputs (act::acts) :=
            (complete_from_permutation (act::acts) s c _ hrc).mem_iff.mpr (by simp)
          exact (List.mem_append.mp hm).resolve_left hnoth
        have hq := inputBound_mem H r q _ hb hmem
        omega
    refine ⟨hh, hspare, ?_⟩
    simp only [hs]
    have htbound : InputBound H (r+(introduced act).length) (inputs acts) := by
      exact (inputBound_append H r (introduced act) (inputs acts)).mp hb |>.2
    have htail : tail = List.range' (q+emitted.length) (n-emitted.length) := by
      have he := congrArg (List.drop emitted.length) ho
      simpa only [List.drop_left, List.drop_range', Nat.mul_one] using he
    rw [htail] at ht
    apply ih u (q+emitted.length) (n-emitted.length) (r+(introduced act).length) ht htbound
    · omega
    · cases act <;> simp [introduced] at hsz hspare <;> omega

theorem expand_action_fits (H : Nat) (act : Action) (s t : SState) (out : List Nat)
    (h : stackStep act s = some (t,out)) :
    RawFits H (expandAction act) s.1 ↔
      s.1.length ≤ H ∧ (introduced act ≠ [] → s.1.length+1 ≤ H) := by
  rcases s with ⟨held,flag⟩
  cases act <;> cases held with
  | nil =>
    simp [stackStep] at h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [RawFits, expandAction, rawStep, introduced]
  | cons a rest =>
    cases rest <;> cases flag <;> simp [stackStep] at h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [RawFits, expandAction, rawStep, introduced]
    all_goals omega

theorem forestFits_iff_rawFits (H : Nat) (acts : List Action) (s t : TState)
    (out : List Nat) (hr : tokenRun acts s = some (t,out)) :
    ForestFits H acts s ↔ RawFits H (expandTrace acts) (tokens s.1) := by
  induction acts generalizing s out with
  | nil => rfl
  | cons act acts ih =>
    obtain ⟨u, emitted, tail, hs, ht, _⟩ := split_run act acts s t out hr
    have hstack := stack_step act s u emitted hs
    have hraw := expand_step act (stackState s) (stackState u) emitted hstack
    change _ ↔ RawFits H (expandAction act ++ expandTrace acts) (tokens s.1)
    simp only [stackState] at hraw
    have hf := expand_action_fits H _ _ _ _ hstack
    simp only [stackState] at hf
    rw [rawFits_append H _ _ _ _ _ hraw, hf]
    simp only [ForestFits, hs]
    rw [ih u tail ht]
    exact and_assoc.symm

theorem canSortWithin_iff_inputBound (H : Nat) (input : List Nat) (n : Nat) :
    CanSortWithin H input n ↔ CanSort [] input (List.range' 1 n) ∧ InputBound H 0 input := by
  constructor
  · rintro ⟨ops, hr, hi, hb⟩
    refine ⟨⟨ops, hr, hi⟩, ?_⟩
    have he := raw_bound_input H ops [] 1 n 0 hr hb rfl
    simpa only [hi] using he
  · rintro ⟨hsort, hb⟩
    obtain ⟨acts,c,hr,hi⟩ := sortable_has_forest input n hsort
    have hf := forest_bound H acts (nil,true) c 1 n 0 hr (by simpa only [hi] using hb)
      rfl (Nat.zero_le H)
    have hfits := (forestFits_iff_rawFits H acts (nil,true) (nil,c) _ hr).mp hf
    refine ⟨expandTrace acts, ?_, (expand_inputs acts).trans hi, hfits⟩
    exact expand_run acts ([],true) ([],c) _ (stack_run acts (nil,true) (nil,c) _ hr)

/-- Every successful increasing-output canonical trace attains minimum physical
capacity: existence of any bounded raw trace is equivalent to this one's fit. -/
theorem canonical_capacity_optimal (H : Nat) (acts : List Action) (c : Bool) (n : Nat)
    (hr : tokenRun acts (nil,true) = some ((nil,c), List.range' 1 n)) :
    CanSortWithin H (inputs acts) n ↔ RawFits H (expandTrace acts) [] := by
  constructor
  · intro h
    have hb := (canSortWithin_iff_inputBound H _ n).mp h |>.2
    have hf := forest_bound H acts (nil,true) c 1 n 0 hr hb rfl (Nat.zero_le H)
    exact (forestFits_iff_rawFits H acts (nil,true) (nil,c) _ hr).mp hf
  · intro hb
    refine ⟨expandTrace acts, ?_, expand_inputs acts, hb⟩
    exact expand_run acts ([],true) ([],c) _ (stack_run acts (nil,true) (nil,c) _ hr)

/-- Maximum drop from a residual input, with r positions already consumed. -/
def maxDropFrom : Nat → List Nat → Nat
  | _, [] => 0
  | r, a :: input => max (r+1-a) (maxDropFrom (r+1) input)

def maxDrop (input : List Nat) : Nat := maxDropFrom 0 input

theorem inputBound_iff_maxDrop (H r : Nat) (input : List Nat) (hH : 0 < H) :
    InputBound H r input ↔ maxDropFrom r input + 1 ≤ H := by
  induction input generalizing r with
  | nil => simp [InputBound, maxDropFrom]; omega
  | cons a input ih =>
    simp only [InputBound, maxDropFrom]
    have hm : max (r+1-a) (maxDropFrom (r+1) input)+1 ≤ H ↔
        (r+1-a)+1 ≤ H ∧ maxDropFrom (r+1) input+1 ≤ H := by omega
    rw [hm, ← ih (r+1)]
    have hh : (r+1-a)+1 ≤ H ↔ r+2 ≤ a+H := by omega
    rw [hh]

theorem rawFits_nonempty_positive (H : Nat) (ops : List RawOp)
    (hne : ops ≠ []) (hb : RawFits H ops []) : 0 < H := by
  cases ops with
  | nil => exact False.elim (hne rfl)
  | cons op ops =>
    cases op with
    | push0 a =>
      have ht : RawFits H ops [a] := by simpa [RawFits, rawStep] using hb
      have hh := rawFits_head H ops [a] ht
      simp only [List.length_cons, List.length_nil] at hh
      omega
    | push1 a => simp [RawFits, rawStep] at hb
    | pop0 => simp [RawFits, rawStep] at hb
    | pop1 => simp [RawFits, rawStep] at hb

theorem canSortWithin_positive (H : Nat) (input : List Nat) (n : Nat)
    (hne : input ≠ []) (h : CanSortWithin H input n) : 0 < H := by
  obtain ⟨ops, _, hi, hb⟩ := h
  apply rawFits_nonempty_positive H ops _ hb
  intro he
  subst ops
  exact hne hi.symm

/-- Exact physical-capacity characterization, including the plus-one slot
needed to insert even a token that immediately exits. -/
theorem canSortWithin_iff_maxDrop (H : Nat) (input : List Nat) (n : Nat)
    (hne : input ≠ []) :
    CanSortWithin H input n ↔
      CanSort [] input (List.range' 1 n) ∧ maxDrop input+1 ≤ H := by
  constructor
  · intro h
    have hp := canSortWithin_positive H input n hne h
    obtain ⟨hs,hb⟩ := (canSortWithin_iff_inputBound H input n).mp h
    exact ⟨hs, (inputBound_iff_maxDrop H 0 input hp).mp hb⟩
  · rintro ⟨hs, hb⟩
    have hp : 0 < H := by omega
    exact (canSortWithin_iff_inputBound H input n).mpr
      ⟨hs, (inputBound_iff_maxDrop H 0 input hp).mpr hb⟩

def IsMinimumCapacity (input : List Nat) (n H : Nat) : Prop :=
  CanSortWithin H input n ∧ ∀ K, CanSortWithin K input n → H ≤ K

/-- Minimum physical capacity is one plus maximum drop for every nonempty
sortable permutation in the original machine. -/
theorem minimumCapacity_eq_maxDrop (input : List Nat) (n : Nat)
    (hne : input ≠ []) (hs : CanSort [] input (List.range' 1 n)) :
    IsMinimumCapacity input n (maxDrop input+1) := by
  refine ⟨(canSortWithin_iff_maxDrop _ input n hne).mpr ⟨hs,Nat.le_refl _⟩, ?_⟩
  intro K hk
  exact ((canSortWithin_iff_maxDrop K input n hne).mp hk).2

#print axioms raw_bound_input
#print axioms forest_bound
#print axioms forestFits_iff_rawFits
#print axioms canSortWithin_iff_inputBound
#print axioms canonical_capacity_optimal
#print axioms canSortWithin_iff_maxDrop
#print axioms minimumCapacity_eq_maxDrop
end StackSorting.Labelled
