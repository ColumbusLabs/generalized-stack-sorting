import MarginalLabelledCarrier

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x)
variable (hc : ConnectedIntroductionComponents D)

theorem numbered_atoms {r : Nat} (atom : Nested.Syntax.InputAtom r)
    (env : Fin r → CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc)) :
    Nested.Syntax.atoms F.labelledRelations atom (fun i => F.numberedLabelEquiv ht hm hc (env i)) ↔
      Nested.Syntax.atoms (CarrierSemantics.relations (F.rootedNestedInput ht hm hc)) atom env := by
  cases atom with
  | original =>
      rcases h : env 0 with v | (x | a) <;>
        simp only [Nested.Syntax.atoms,h] <;> try exact Iff.rfl
  | localNode =>
      rcases h : env 0 with v | (x | a) <;>
        simp only [Nested.Syntax.atoms,h] <;> try exact Iff.rfl
  | localRoot =>
      rcases h : env 0 with v | (x | a) <;>
        simp only [Nested.Syntax.atoms,h] <;> try exact Iff.rfl
      exact F.numbered_local_root ht hm hc a
  | owner =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
  | margin =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
  | adhesion =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
  | outerParent =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
  | localParent =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
      exact F.numbered_local_parent ht hm hc a b
  | localBag =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl
      exact F.numbered_local_bag ht hm hc a w
  | originalEdge =>
      rcases h0 : env 0 with v | (x | a) <;> rcases h1 : env 1 with w | (y | b) <;>
        simp only [Nested.Syntax.atoms,h0,h1] <;> try exact Iff.rfl

#print axioms numbered_atoms
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
