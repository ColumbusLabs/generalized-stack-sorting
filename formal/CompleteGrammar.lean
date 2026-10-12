import FirstReturnTrees

namespace StackSorting.FirstReturn
open StackSorting Mark Op

inductive Path where
  | nil
  | bypass (p : Path)
  | push (t : Tree) (p : Path)
  deriving DecidableEq, Repr

def pathEncode : Path → List Op
  | .nil => []
  | .bypass p => .bypass :: pathEncode p
  | .push t p => .push0 :: (encode t ++ pathEncode p)

def Valid : Path → Prop
  | .nil => True
  | .bypass p => Valid p
  | .push t p => eval t L none false = some none ∧ Valid p

instance decidableValid : (p : Path) → Decidable (Valid p)
  | .nil => isTrue trivial
  | .bypass p => decidableValid p
  | .push _t p => @instDecidableAnd _ _ (inferInstance) (decidableValid p)

def pathWeight : Path → Nat
  | .nil => 0
  | .bypass p => 1 + pathWeight p
  | .push t p => 1 + weight t + pathWeight p

def opWeight : Op → Nat
  | .bypass | .push0 | .push1 => 1
  | .pop0 | .pop1 => 0

def wordWeight (ops : List Op) : Nat := (ops.map opWeight).sum

@[simp] theorem wordWeight_append (xs ys : List Op) :
    wordWeight (xs ++ ys) = wordWeight xs + wordWeight ys := by
  simp [wordWeight, List.map_append, List.sum_append]

theorem encode_weight (t : Tree) : wordWeight (encode t) = weight t := by
  induction t <;> simp_all [encode, weight, wordWeight, opWeight,
    List.map_append, List.sum_append, Nat.add_assoc]

theorem pathEncode_weight (p : Path) : wordWeight (pathEncode p) = pathWeight p := by
  induction p with
  | nil => rfl
  | bypass p ih => simpa [pathEncode, pathWeight, wordWeight, opWeight, Nat.add_comm] using ih
  | push t p ih =>
      simp only [pathEncode, wordWeight, List.map_cons, List.sum_cons, opWeight,
        List.map_append, List.sum_append, pathWeight]
      change 1 + (wordWeight (encode t) + wordWeight (pathEncode p)) = _
      rw [encode_weight, ih]
      omega

theorem pathEncode_injective : Function.Injective pathEncode := by
  intro p
  induction p with
  | nil => intro q h; cases q <;> simp_all [pathEncode]
  | bypass p ih =>
      intro q h
      cases q <;> simp only [pathEncode, List.cons.injEq, reduceCtorEq,
        false_and, true_and] at h
      exact congrArg Path.bypass (ih h)
  | push t p ih =>
      intro q h
      cases q <;> simp only [pathEncode, List.cons.injEq, reduceCtorEq,
        false_and, true_and] at h
      obtain ⟨ht, hp⟩ := encode_prefix _ _ _ _ h
      rw [ht, ih hp]

theorem path_sound (p : Path) (h : Valid p) :
    wordRun (pathEncode p) ([], true) = some ([], true) := by
  induction p with
  | nil => rfl
  | bypass p ih => simpa [pathEncode, wordRun, wordStep] using ih h
  | push t p ih =>
      have ht := eval_sound t L none none false [] (by simp) h.1
      change wordRun (encode t) ([L], false) = some ([], true) at ht
      simp only [pathEncode, wordRun, wordStep, Option.bind_some, wordRun_append]
      rw [ht]
      exact ih h.2

theorem path_complete (ops : List Op) (flag : Bool)
    (h : wordRun ops ([], true) = some ([], flag)) :
    ∃ p, Valid p ∧ pathEncode p = ops := by
  cases ops with
  | nil => exact ⟨.nil, trivial, rfl⟩
  | cons op ops =>
      cases op with
      | bypass =>
          have hr : wordRun ops ([], true) = some ([], flag) := by
            simpa [wordRun, wordStep] using h
          obtain ⟨p, hp, he⟩ := path_complete ops flag hr
          exact ⟨.bypass p, hp, by simp [pathEncode, he]⟩
      | push0 =>
          have hr : wordRun ops ([L], false) = some ([], flag) := by
            simpa [wordRun, wordStep] using h
          obtain ⟨t, rest, d, he, ht, hrest⟩ :=
            down_complete ops L none false [] (by simp) ([], flag) hr (by simp [letters])
          have hd : d = none := (eval_bottom_iff t L none d false ht).mpr rfl
          subst d
          have hlen : rest.length < (Op.push0 :: ops).length := by
            have hl := congrArg List.length he
            simp only [List.length_append, List.length_cons] at *
            omega
          obtain ⟨p, hp, hep⟩ := path_complete rest flag hrest
          exact ⟨.push t p, ⟨ht, hp⟩, by simp [pathEncode, hep, he]⟩
      | push1 => simp [wordRun, wordStep] at h
      | pop0 => simp [wordRun, wordStep] at h
      | pop1 => simp [wordRun, wordStep] at h
termination_by ops.length

/-- The finite-control first-return grammar is exactly the already formalized
operation language. The grammar is unambiguous and preserves input-token size. -/
theorem accepted_iff_unique_grammar (ops : List Op) :
    WordAccepts ops ↔ ∃ p, (Valid p ∧ pathEncode p = ops) ∧
      ∀ q, Valid q ∧ pathEncode q = ops → q = p := by
  constructor
  · rintro ⟨flag, h⟩
    obtain ⟨p, hp, he⟩ := path_complete ops flag h
    refine ⟨p, ⟨hp, he⟩, ?_⟩
    intro q hq
    exact pathEncode_injective (hq.2.trans he.symm)
  · rintro ⟨p, ⟨hp, he⟩, _⟩
    exact ⟨true, he ▸ path_sound p hp⟩

#print axioms down_complete
#print axioms accepted_iff_unique_grammar
#print axioms pathEncode_weight
end StackSorting.FirstReturn
