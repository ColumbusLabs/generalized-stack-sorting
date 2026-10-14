import SparseFormulaReindex

namespace StackSorting.SparseEndpointMSO.CanonicalChoice

def SupportedTuple (D : Model) (X : Fin k → Nat → Prop) : Prop :=
  ∀ i x, X i x → x ∈ D.domain

/-- A finite block of actual bounded monadic quantifiers. -/
def allSets : (k : Nat) → Formula a (k + b) → Formula a b
  | 0, f => f.reindex id (Fin.cast (Nat.zero_add b))
  | k+1, f => allSets k (.allSet (f.reindex id (Fin.cast (by omega))))

private theorem cons_addCases_cast (X : Nat → Prop) (xs : Fin k → Nat → Prop)
    (sets : Fin b → Nat → Prop) (h : k+1+b = (k+b)+1) :
    (fun i => Fin.cases X (Fin.addCases xs sets) (Fin.cast h i)) =
      Fin.addCases (Fin.cases X xs) sets := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · have hh : Fin.cast h (Fin.castAdd b j.succ) = (Fin.castAdd b j).succ := by
        apply Fin.ext
        rfl
      rw [hh]
      simp
  · have hh : Fin.cast h (Fin.natAdd (k+1) j) = (Fin.natAdd k j).succ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    rw [hh]
    simp

theorem eval_allSets (D : Model) (k : Nat) (f : Formula a (k+b))
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (allSets k f) env sets ↔
      ∀ X : Fin k → Nat → Prop, SupportedTuple D X →
        Eval D f env (Fin.addCases X sets) := by
  induction k with
  | zero =>
    rw [allSets, Formula.eval_reindex]
    have he (X : Fin 0 → Nat → Prop) :
        (fun i => sets (Fin.cast (Nat.zero_add b) i)) = Fin.addCases X sets := by
      funext i
      refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
      rw [Fin.addCases_right]
      congr 1
      apply Fin.ext
      simp
    constructor
    · intro h X _
      simpa only [id_eq, he X] using h
    · intro h
      have hh := h Fin.elim0 (fun i => Fin.elim0 i)
      simpa only [id_eq, he Fin.elim0] using hh
  | succ k ih =>
    rw [allSets, ih]
    simp only [Eval, Formula.eval_reindex, id_eq]
    constructor
    · intro h X hX
      have hh := h (fun i => X i.succ) (fun i x hx => hX i.succ x hx)
        (X 0) (hX 0)
      rw [cons_addCases_cast] at hh
      have he : (Fin.cases (X 0) (fun i => X i.succ)) = X := by
        funext i
        exact Fin.cases (by rfl) (fun j => by rfl) i
      simpa only [he] using hh
    · intro h xs hxs X hX
      rw [cons_addCases_cast]
      apply h
      intro i
      exact Fin.cases hX (fun j => hxs j) i

#print axioms eval_allSets
end StackSorting.SparseEndpointMSO.CanonicalChoice
