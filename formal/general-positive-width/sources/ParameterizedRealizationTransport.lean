import SparseParametricRealization

namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric

/-- Pointwise change of an actual represented carrier through a genuine
bijection. The atomic equivalences are explicit; no sentence-level oracle
is introduced. -/
def Realization.transport {J : Interpretation Atom c d} {D : Model}
    {params : Fin d → Nat → Prop} {α β : Type}
    {atomsA : {r : Nat} → Atom r → (Fin r → α) → Prop}
    (R : Realization J D params α atomsA) (e : α ≃ β)
    (atomsB : {r : Nat} → Atom r → (Fin r → β) → Prop)
    (hAtom : ∀ {r} (A : Atom r) (env : Fin r → α),
      atomsA A env ↔ atomsB A (fun i => e (env i))) :
    Realization J D params β atomsB where
  rep v x := R.rep v (e.symm x)
  valid _ _ h := R.valid _ _ h
  cover x := R.cover (e.symm x)
  complete v hv := by
    obtain ⟨x,hx⟩ := R.complete v hv
    exact ⟨e x,by simpa only [Equiv.symm_apply_apply] using hx⟩
  equal v w x y hv hw := by
    rw [R.equal v w (e.symm x) (e.symm y) hv hw]
    exact e.symm.injective.eq_iff
  atom A env actual hr := by
    have h := (R.atom A env (fun i => e.symm (actual i)) hr).trans
      (hAtom A (fun i => e.symm (actual i)))
    simpa only [Equiv.apply_symm_apply] using h

#print axioms Realization.transport
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
