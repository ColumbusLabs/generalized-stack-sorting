import ForestWord

/-!
Operation-labelled first-downstep trees. This grammar keeps both pop labels and
both push labels, including coincident machine edges. `eval` is a finite-control
semantics with a genuine bottom marker. The counting-series layer is separate.
-/
namespace StackSorting.FirstReturn
open StackSorting Mark Op

inductive Tree where
  | pop0 | pop1
  | bypass (t : Tree)
  | push0 (s t : Tree)
  | push1 (s t : Tree)
  deriving DecidableEq, Repr

def encode : Tree → List Op
  | .pop0 => [.pop0]
  | .pop1 => [.pop1]
  | .bypass t => .bypass :: encode t
  | .push0 s t => .push0 :: (encode s ++ encode t)
  | .push1 s t => .push1 :: (encode s ++ encode t)

def weight : Tree → Nat
  | .pop0 | .pop1 => 0
  | .bypass t => 1 + weight t
  | .push0 s t | .push1 s t => 1 + weight s + weight t

/-- `none` is the true bottom boundary; it is not a fictive stack letter. -/
def eval : Tree → Mark → Option Mark → Bool → Option (Option Mark)
  | .pop0, _, b, enabled => if enabled then some b else none
  | .pop1, a, b, enabled =>
      if enabled then match a, b with
      | L, some _ => some (some L)
      | _, _ => none
      else none
  | .bypass t, a, b, _ => eval t a b true
  | .push0 s t, a, b, _ =>
      match eval s R (some a) false with
      | some (some e) => eval t e b true
      | _ => none
  | .push1 s t, _, b, _ =>
      match eval s R (some L) false with
      | some (some e) => eval t e b true
      | _ => none

def letters : Option Mark → List Mark
  | none => []
  | some a => [a]

theorem encode_ne_nil (t : Tree) : encode t ≠ [] := by cases t <;> simp [encode]

theorem eval_bottom_iff (t : Tree) (a : Mark) (b d : Option Mark) (flag : Bool)
    (h : eval t a b flag = some d) : d = none ↔ b = none := by
  induction t generalizing a b d flag with
  | pop0 => cases flag <;> simp_all [eval]
  | pop1 =>
      cases flag <;> cases a <;> cases b <;> simp_all [eval]
      cases h
      simp
  | bypass t ih => exact ih a b d true h
  | push0 s t _ ih =>
      simp only [eval] at h
      split at h <;> try contradiction
      exact ih _ b d true h
  | push1 s t _ ih =>
      simp only [eval] at h
      split at h <;> try contradiction
      exact ih _ b d true h

/-- The Polish first-downstep encoding is prefix-free, retaining operation labels. -/
theorem encode_prefix (t u : Tree) (xs ys : List Op)
    (h : encode t ++ xs = encode u ++ ys) : t = u ∧ xs = ys := by
  induction t generalizing u xs ys with
  | pop0 =>
      cases u <;> simp only [encode, List.cons_append, List.cons.injEq,
        List.nil_append, reduceCtorEq, false_and, true_and] at h
      exact ⟨rfl, h⟩
  | pop1 =>
      cases u <;> simp only [encode, List.cons_append, List.cons.injEq,
        List.nil_append, reduceCtorEq, false_and, true_and] at h
      exact ⟨rfl, h⟩
  | bypass t ih =>
      cases u <;> simp only [encode, List.cons_append, List.cons.injEq,
        reduceCtorEq, false_and, true_and] at h
      obtain ⟨ht, hr⟩ := ih _ xs ys h
      exact ⟨congrArg Tree.bypass ht, hr⟩
  | push0 s t ihs iht =>
      cases u <;> simp only [encode, List.cons_append, List.cons.injEq,
        reduceCtorEq, false_and, true_and] at h
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨hs, hr⟩ := ihs _ _ _ h
      obtain ⟨ht, he⟩ := iht _ _ _ hr
      exact ⟨by rw [hs, ht], he⟩
  | push1 s t ihs iht =>
      cases u <;> simp only [encode, List.cons_append, List.cons.injEq,
        reduceCtorEq, false_and, true_and] at h
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨hs, hr⟩ := ihs _ _ _ h
      obtain ⟨ht, he⟩ := iht _ _ _ hr
      exact ⟨by rw [hs, ht], he⟩

theorem encode_injective : Function.Injective encode := by
  intro t u h
  exact (encode_prefix t u [] [] (by simpa using h)).1

theorem wordRun_append (xs ys : List Op) (s : WState) :
    wordRun (xs ++ ys) s = (wordRun xs s).bind (wordRun ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih =>
      simp only [List.cons_append, wordRun]
      cases wordStep op s <;> simp [ih]

/-- Every successful grammar evaluation is the corresponding exact word-machine
execution above an untouched suffix. Bottom evaluation requires an empty tail. -/
theorem eval_sound (t : Tree) (a : Mark) (b d : Option Mark) (flag : Bool)
    (tail : List Mark) (hb : b = none → tail = [])
    (h : eval t a b flag = some d) :
    wordRun (encode t) (a :: (letters b ++ tail), flag) =
      some (letters d ++ tail, true) := by
  induction t generalizing a b d flag tail with
  | pop0 =>
      cases flag <;> simp_all [eval, encode, wordRun, wordStep]
  | pop1 =>
      cases flag <;> cases a <;> cases b <;>
        simp_all [eval, encode, letters, wordRun, wordStep]
      cases h
      rfl
  | bypass t ih =>
      simpa [encode, wordRun, wordStep] using ih a b d true tail hb h
  | push0 s t ihs iht =>
      simp only [eval] at h
      split at h
      next e he =>
        have hs := ihs R (some a) (some e) false (letters b ++ tail) (by simp) he
        have ht := iht e b d true tail hb h
        change wordRun (encode s) (R :: a :: (letters b ++ tail), false) =
          some (e :: (letters b ++ tail), true) at hs
        simp only [encode, wordRun, wordStep, Option.bind_some, wordRun_append]
        rw [hs]
        exact ht
      next hbad => contradiction
  | push1 s t ihs iht =>
      simp only [eval] at h
      split at h
      next e he =>
        have hs := ihs R (some L) (some e) false (letters b ++ tail) (by simp) he
        have ht := iht e b d true tail hb h
        simp only [encode, wordRun, wordStep, Option.bind_some, wordRun_append]
        change wordRun (encode s) (R :: L :: (letters b ++ tail), false) =
          some (e :: (letters b ++ tail), true) at hs
        rw [hs]
        exact ht
      next hbad => contradiction

/-- Any execution that descends below its starting held height has a uniquely
encoded first-downstep prefix. This is the grammar completeness obligation. -/
theorem down_complete (ops : List Op) (a : Mark) (b : Option Mark) (flag : Bool)
    (tail : List Mark) (hb : b = none → tail = []) (out : WState)
    (hrun : wordRun ops (a :: (letters b ++ tail), flag) = some out)
    (hle : out.1.length ≤ (letters b ++ tail).length) :
    ∃ t rest d, ops = encode t ++ rest ∧ eval t a b flag = some d ∧
      wordRun rest (letters d ++ tail, true) = some out := by
  cases ops with
  | nil =>
      simp only [wordRun, Option.some.injEq] at hrun
      have he := congrArg (fun s : WState => s.1.length) hrun
      simp only [List.length_cons] at he
      omega
  | cons op ops =>
      cases op with
      | bypass =>
          have hr : wordRun ops (a :: (letters b ++ tail), true) = some out := by
            simpa [wordRun, wordStep] using hrun
          obtain ⟨t, rest, d, he, hv, ht⟩ :=
            down_complete ops a b true tail hb out hr hle
          exact ⟨.bypass t, rest, d, by simp [encode, he], hv, ht⟩
      | pop0 =>
          cases flag with
          | false => simp [wordRun, wordStep] at hrun
          | true =>
              exact ⟨.pop0, ops, b, rfl, rfl, by simpa [wordRun, wordStep] using hrun⟩
      | pop1 =>
          cases b with
          | none =>
              have hh := hb rfl
              subst tail
              cases flag <;> cases a <;> simp [wordRun, wordStep, letters] at hrun
          | some b =>
              cases flag <;> cases a <;> simp [wordRun, wordStep, letters] at hrun
              exact ⟨.pop1, ops, some L, rfl, rfl, hrun⟩
      | push0 =>
          have hr : wordRun ops (R :: a :: (letters b ++ tail), false) = some out := by
            simpa [wordRun, wordStep] using hrun
          obtain ⟨s, rest, d, he, hv, ht⟩ := down_complete ops R (some a) false
            (letters b ++ tail) (by simp) out hr (by simpa [letters] using Nat.le_succ_of_le hle)
          cases d with
          | none =>
              have := (eval_bottom_iff s R (some a) none false hv).mp rfl
              contradiction
          | some e =>
              have hrest : rest.length < (Op.push0 :: ops).length := by
                have hl := congrArg List.length he
                simp only [List.length_append, List.length_cons] at *
                omega
              obtain ⟨t, rest', d', he', hv', ht'⟩ := down_complete rest e b true tail hb out ht hle
              refine ⟨.push0 s t, rest', d', ?_, ?_, ht'⟩
              · simp [encode, he, he', List.append_assoc]
              · simp [eval, hv, hv']
      | push1 =>
          have hr : wordRun ops (R :: L :: (letters b ++ tail), false) = some out := by
            simpa [wordRun, wordStep] using hrun
          obtain ⟨s, rest, d, he, hv, ht⟩ := down_complete ops R (some L) false
            (letters b ++ tail) (by simp) out hr (by simpa [letters] using Nat.le_succ_of_le hle)
          cases d with
          | none =>
              have := (eval_bottom_iff s R (some L) none false hv).mp rfl
              contradiction
          | some e =>
              have hrest : rest.length < (Op.push1 :: ops).length := by
                have hl := congrArg List.length he
                simp only [List.length_append, List.length_cons] at *
                omega
              obtain ⟨t, rest', d', he', hv', ht'⟩ := down_complete rest e b true tail hb out ht hle
              refine ⟨.push1 s t, rest', d', ?_, ?_, ht'⟩
              · simp [encode, he, he', List.append_assoc]
              · simp [eval, hv, hv']
termination_by ops.length


#print axioms encode_prefix
#print axioms eval_sound
end StackSorting.FirstReturn
