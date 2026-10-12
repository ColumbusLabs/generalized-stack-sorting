import OriginalMachine

/-! # Conservation and exchange for the original stack machine -/
namespace StackSorting.Labelled

/-- Raw operations conserve token multiplicities. -/
theorem rawStep_count (op : RawOp) (s t out : List Nat)
    (h : rawStep op s = some (t, out)) (a : Nat) :
    s.count a + (rawIntroduced op).count a = out.count a + t.count a := by
  cases op <;> cases s with
  | nil =>
    simp [rawStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [rawIntroduced, List.count_cons]
  | cons b rest =>
    cases rest <;> simp [rawStep] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [rawIntroduced, List.count_cons, Nat.add_comm, Nat.add_left_comm]

theorem rawRun_count (ops : List RawOp) (s t out : List Nat)
    (h : rawRun ops s = some (t, out)) (a : Nat) :
    s.count a + (rawInputs ops).count a = out.count a + t.count a := by
  induction ops generalizing s t out with
  | nil => simp [rawRun] at h; rcases h with ⟨rfl, rfl⟩; simp [rawInputs]
  | cons op ops ih =>
    cases hs : rawStep op s with
    | none => simp [rawRun, hs] at h
    | some p =>
      rcases p with ⟨u, emitted⟩
      cases hr : rawRun ops u with
      | none => simp [rawRun, hs, hr] at h
      | some p =>
        rcases p with ⟨v, tail⟩
        simp [rawRun, hs, hr] at h
        rcases h with ⟨rfl, rfl⟩
        have hf := rawStep_count op s u emitted hs a
        have ht := ih u v tail hr
        simp [rawInputs] at *
        omega

theorem raw_complete_permutation (ops : List RawOp) (held out : List Nat)
    (h : rawRun ops held = some ([], out)) : (held ++ rawInputs ops).Perm out := by
  apply List.perm_iff_count.mpr
  intro a
  simpa using rawRun_count ops held [] out h a

theorem raw_held_mem_output (ops : List RawOp) (held out : List Nat)
    (h : rawRun ops held = some ([], out)) (a : Nat) (ha : a ∈ held) : a ∈ out := by
  exact (raw_complete_permutation ops held out h).mem_iff.mp
    (List.mem_append_left _ ha)

theorem raw_split_run (op : RawOp) (ops : List RawOp) (s t out : List Nat)
    (h : rawRun (op :: ops) s = some (t, out)) :
    ∃ u emitted tail, rawStep op s = some (u, emitted) ∧
      rawRun ops u = some (t, tail) ∧ emitted ++ tail = out := by
  cases hs : rawStep op s with
  | none => simp [rawRun, hs] at h
  | some p =>
    rcases p with ⟨u, emitted⟩
    cases hr : rawRun ops u with
    | none => simp [rawRun, hs, hr] at h
    | some p =>
      rcases p with ⟨v, tail⟩
      simp [rawRun, hs, hr] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨u, emitted, tail, rfl, hr, rfl⟩

/-- Move the larger marked token y from before x to immediately below x.
The two lists P and Q hold intervening tokens. A successful increasing-output
continuation cannot emit y while x remains, and the simulation synchronizes
when x is removed. Inputs and output are unchanged. -/
theorem exchange_general (ops : List RawOp) (P Q R : List Nat) (x y : Nat)
    (hxy : x < y) (out : List Nat)
    (h : rawRun ops (P ++ (y :: (Q ++ x :: R))) = some ([], out))
    (hsorted : out.Pairwise (· < ·)) :
    ∃ ops', rawRun ops' (P ++ (Q ++ x :: y :: R)) = some ([], out) ∧
      rawInputs ops' = rawInputs ops := by
  induction ops generalizing P Q R out with
  | nil => simp [rawRun] at h
  | cons op ops ih =>
    obtain ⟨u, emitted, tail, hs, hr, hout⟩ := raw_split_run op ops _ [] out h
    have hparts : emitted.Pairwise (· < ·) ∧ tail.Pairwise (· < ·) ∧
        ∀ a ∈ emitted, ∀ b ∈ tail, a < b := by
      rw [← hout] at hsorted
      exact List.pairwise_append.mp hsorted
    cases op with
    | push0 a =>
      simp [rawStep] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp at hout
      subst out
      obtain ⟨ops', hv, hi⟩ := ih (a :: P) Q R tail hr hparts.2.1
      refine ⟨.push0 a :: ops', ?_, ?_⟩
      · simpa [rawRun, rawStep, Prod.eta] using hv
      · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi
    | push1 a =>
      cases P with
      | nil =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp at hout
        subst out
        obtain ⟨ops', hv, hi⟩ := ih [] (a :: Q) R tail hr hparts.2.1
        refine ⟨.push0 a :: ops', ?_, ?_⟩
        · simpa [rawRun, rawStep, Prod.eta] using hv
        · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi
      | cons b P =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp at hout
        subst out
        obtain ⟨ops', hv, hi⟩ := ih (b :: a :: P) Q R tail hr hparts.2.1
        refine ⟨.push1 a :: ops', ?_, ?_⟩
        · simpa [rawRun, rawStep, Prod.eta] using hv
        · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi
    | pop0 =>
      cases P with
      | nil =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        have hx := raw_held_mem_output ops (Q ++ x :: R) tail hr x (by simp)
        have hyx := hparts.2.2 y (by simp) x hx
        omega
      | cons a P =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        obtain ⟨ops', hv, hi⟩ := ih P Q R tail hr hparts.2.1
        refine ⟨.pop0 :: ops', ?_, ?_⟩
        · simp [rawRun, rawStep, hv, ← hout]
        · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi
    | pop1 =>
      cases P with
      | nil =>
        cases Q with
        | nil =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl, rfl⟩
          refine ⟨.pop0 :: ops, ?_, ?_⟩
          · simp [rawRun, rawStep, hr, ← hout]
          · simp [rawInputs, rawIntroduced]
        | cons a Q =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl, rfl⟩
          obtain ⟨ops', hv, hi⟩ := ih [] Q R tail hr hparts.2.1
          refine ⟨.pop0 :: ops', ?_, ?_⟩
          · simp only [List.nil_append] at hv
            simp [rawRun, rawStep, hv, ← hout]
          · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi
      | cons a P =>
        cases P with
        | nil =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl, rfl⟩
          have hx := raw_held_mem_output ops (a :: (Q ++ x :: R)) tail hr x (by simp)
          have hyx := hparts.2.2 y (by simp) x hx
          omega
        | cons b P =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl, rfl⟩
          obtain ⟨ops', hv, hi⟩ := ih (a :: P) Q R tail hr hparts.2.1
          refine ⟨.pop1 :: ops', ?_, ?_⟩
          · simp only [List.cons_append] at hv
            simp [rawRun, rawStep, hv, ← hout]
          · simp [rawInputs, rawIntroduced] at hi ⊢; exact hi

theorem top_pair_exchange (ops : List RawOp) (R : List Nat) (x y : Nat)
    (hxy : x < y) (out : List Nat)
    (h : rawRun ops (y :: x :: R) = some ([], out))
    (hsorted : out.Pairwise (· < ·)) :
    ∃ ops', rawRun ops' (x :: y :: R) = some ([], out) ∧
      rawInputs ops' = rawInputs ops := by
  exact exchange_general ops [] [] R x y hxy out h hsorted

#print axioms raw_complete_permutation
#print axioms top_pair_exchange

end StackSorting.Labelled
