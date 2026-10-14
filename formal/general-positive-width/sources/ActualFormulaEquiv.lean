import OwnerParameterMerge

namespace StackSorting.SparseEndpointMSO.FiniteCopy
variable {Atom : Nat → Type} {α β : Type}

/-- Pointwise atomic equivalence along an actual carrier bijection transports
all formulas, including arbitrary nested second-order quantification. -/
theorem actualEval_equiv
    (ats : {r : Nat} → Atom r → (Fin r → α) → Prop)
    (bts : {r : Nat} → Atom r → (Fin r → β) → Prop) (e : α ≃ β)
    (hat : ∀ {r} (A : Atom r) env, ats A env ↔ bts A (fun i => e (env i)))
    (p : CopyFormula Atom a b) (env : Fin a → α) (out : Fin a → β)
    (sets : Fin b → α → Prop) (outSets : Fin b → β → Prop)
    (he : ∀ i, e (env i)=out i) (hs : ∀ j x, sets j x ↔ outSets j (e x)) :
    ActualEval ats p env sets ↔ ActualEval bts p out outSets := by
  induction p with
  | truth => rfl
  | equal i j =>
    change env i=env j ↔ out i=out j
    exact e.injective.eq_iff.symm.trans (by rw [he i,he j])
  | member i X => simpa only [ActualEval,he] using hs X (env i)
  | atom A args =>
    have h := hat A (fun i => env (args i))
    simpa only [ActualEval,he] using h
  | neg p ih => exact not_congr (ih env out sets outSets he hs)
  | conj p q ihp ihq => exact and_congr (ihp env out sets outSets he hs) (ihq env out sets outSets he hs)
  | implies p q ihp ihq => exact imp_congr (ihp env out sets outSets he hs) (ihq env out sets outSets he hs)
  | existsFO p ih =>
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨e x,(ih (Fin.cases x env) (Fin.cases (e x) out) sets outSets (fun i => Fin.cases rfl he i) hs).mp hx⟩
    · rintro ⟨y,hy⟩
      exact ⟨e.symm y,(ih (Fin.cases (e.symm y) env) (Fin.cases y out) sets outSets (fun i => Fin.cases (e.apply_symm_apply y) he i) hs).mpr hy⟩
  | allFO p ih =>
    constructor
    · intro h y
      exact (ih (Fin.cases (e.symm y) env) (Fin.cases y out) sets outSets (fun i => Fin.cases (e.apply_symm_apply y) he i) hs).mp (h (e.symm y))
    · intro h x
      exact (ih (Fin.cases x env) (Fin.cases (e x) out) sets outSets (fun i => Fin.cases rfl he i) hs).mpr (h (e x))
  | allSet p ih =>
    constructor
    · intro h Y
      apply (ih env out (Fin.cases (fun x => Y (e x)) sets) (Fin.cases Y outSets) he ?_).mp
        (h (fun x => Y (e x)))
      intro j x
      exact Fin.cases Iff.rfl (fun q => hs q x) j
    · intro h X
      apply (ih env out (Fin.cases X sets) (Fin.cases (fun y => X (e.symm y)) outSets) he ?_).mpr
        (h (fun y => X (e.symm y)))
      intro j x
      refine Fin.cases ?_ (fun q => hs q x) j
      simp only [Fin.cases_zero,Equiv.symm_apply_apply]

#print axioms actualEval_equiv
end StackSorting.SparseEndpointMSO.FiniteCopy
