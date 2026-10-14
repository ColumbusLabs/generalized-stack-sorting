import DecompositionIntroductionSyntax

namespace StackSorting.GraphWidth.Nested.CarrierSemantics
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

noncomputable def numberedNodeEquiv (N : NestedInput D) :
    N.substitution.Node ≃ Fin (Fintype.card N.substitution.Node) where
  toFun := N.substitution.index
  invFun := N.substitution.label
  left_inv := N.substitution.label_index
  right_inv := N.substitution.index_label

noncomputable def numberedFlatEquiv (N : NestedInput D) :
    FlatCarrier N ≃ IntroductionSyntax.Carrier n (Fintype.card N.substitution.Node) :=
  Equiv.sumCongr (Equiv.refl _) (numberedNodeEquiv N)

theorem numbered_parent_iff (N : NestedInput D) (a b : N.substitution.Node) :
    (a≠N.substitution.root ∧ N.substitution.parent a=b) ↔
      (N.substitution.index a).val≠0 ∧
        N.substitution.tree.parent (N.substitution.index a)=N.substitution.index b := by
  have h := literal_parent_exact N (N.substitution.index a) (N.substitution.index b)
  rw [Syntax.eval_flattenedParentAt] at h
  simp only [TreeSubstitution.label_index] at h
  exact (flattenedParent_exact N a b).symm.trans h

theorem numbered_atoms_exact (N : NestedInput D) {r : Nat} (A : Syntax.OutputAtom r)
    (env : Fin r → FlatCarrier N) :
    outputAtoms N A env ↔ IntroductionSyntax.atoms N.flattened A
      (fun i => numberedFlatEquiv N (env i)) := by
  cases A with
  | original =>
    cases h : env 0 <;>
      simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h]
  | node =>
    cases h : env 0 <;>
      simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h]
  | parent =>
    cases h0 : env 0 with
    | inl v =>
      cases h1 : env 1 <;>
        simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h0,h1]
    | inr a =>
      cases h1 : env 1 with
      | inl v => simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h0,h1]
      | inr b =>
        simpa [outputAtoms,IntroductionSyntax.atoms,h0,h1,numberedFlatEquiv,
          numberedNodeEquiv] using numbered_parent_iff N a b
  | bag =>
    cases h0 : env 0 with
    | inl v =>
      cases h1 : env 1 <;>
        simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h0,h1]
    | inr a =>
      cases h1 : env 1 with
      | inl v =>
        simp [outputAtoms,IntroductionSyntax.atoms,h0,h1,numberedFlatEquiv,
          numberedNodeEquiv,NestedInput.flattened]
      | inr b => simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h0,h1]
  | originalEdge =>
    cases h0 : env 0 <;> cases h1 : env 1 <;>
      simp [outputAtoms,IntroductionSyntax.atoms,numberedFlatEquiv,h0,h1]

noncomputable def numberedRealization (N : NestedInput D) {c d : Nat}
    {J : Interpretation Syntax.InputAtom c d} {M : Model} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier N) (Syntax.atoms (relations N))) :
    Realization (compose J Syntax.interpretation) M
      (flattenedSets params (fun i => R.liftSet (Fin.elim0 i)))
      (IntroductionSyntax.Carrier n (Fintype.card N.substitution.Node))
      (IntroductionSyntax.atoms N.flattened) :=
  (realizeFlattened N R).transport (numberedFlatEquiv N)
    (IntroductionSyntax.atoms N.flattened) (numbered_atoms_exact N)

/-- The original event number and fixed vertex tag survive literal flattening.
This is the needed input identity for a two-free-original-variable preorder. -/
theorem numbered_vertex_code (N : NestedInput D) {c d : Nat}
    {J : Interpretation Syntax.InputAtom c d} {M : Model} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier N) (Syntax.atoms (relations N)))
    (tag : Fin c) (x : Nat) (v : Fin n) :
    (numberedRealization N R).rep (finProdFinEquiv (0,tag),x) (.inl v) ↔
      R.rep (tag,x) (vertex N v) := by
  change (outerTag (finProdFinEquiv (0,tag))=0 ∧
    R.rep (innerTag (finProdFinEquiv (0,tag)),x) (vertex N v)) ↔ _
  simp [outerTag,innerTag]

#print axioms numbered_parent_iff
#print axioms numbered_atoms_exact
#print axioms numberedRealization
#print axioms numbered_vertex_code
end StackSorting.GraphWidth.Nested.CarrierSemantics
