import SparseFrontierAdmissibility
import NormalizedDecompositionRegions

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
open SameVertexForest GraphWidth ConnectedConeNormalization
variable {n k b : Nat}

/-- Exact reverse bridge from an actual named finite order and its concrete
frontier bound to the accepted literal admissibility sentence. -/
theorem named_order_admissible (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (O : RankedOrder n) (G : Graph n)
    (hrel : ∀ u v, RelationEval D earlier X (e u).val (e v).val ↔ O.rel u v)
    (hG : ∀ u v, G.Adj u v ↔ ModelAdjacent D (e u).val (e v).val)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hb : ∀ v, (FiniteTupleBound.points (RegionBag G O v)).card ≤ b) :
    Eval D (admissibleSentence earlier b) Fin.elim0 X := by
  let name (x : Nat) (hx : x ∈ D.domain) : Fin n := e.symm ⟨x,hx⟩
  have named (x : Nat) (hx : x ∈ D.domain) : (e (name x hx)).val = x := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  have rel (x : Nat) (hx : x ∈ D.domain) (y : Nat) (hy : y ∈ D.domain) :
      RelationEval D earlier X x y ↔ O.rel (name x hx) (name y hy) := by
    simpa only [named] using hrel (name x hx) (name y hy)
  have adjacent (x : Nat) (hx : x ∈ D.domain) (y : Nat) (hy : y ∈ D.domain) :
      G.Adj (name x hx) (name y hy) ↔ ModelAdjacent D x y := by
    simpa only [named] using hG (name x hx) (name y hy)
  refine ⟨(eval_forestOrderSentence D earlier X).mpr ?_,
    (eval_eliminationSentence D earlier X).mpr ?_,
    (eval_frontierBoundSentence D earlier X b).mpr ?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro x hx hh
      exact O.irrefl _ ((rel x hx x hx).mp hh)
    · intro x hx y hy z hz hxy hyz
      exact (rel x hx z hz).mpr (O.trans ((rel x hx y hy).mp hxy)
        ((rel y hy z hz).mp hyz))
    · intro x hx y hy z hz hxz hyz
      rcases O.predecessors ((rel x hx z hz).mp hxz) ((rel y hy z hz).mp hyz) with h | h | h
      · exact Or.inl ((rel x hx y hy).mpr h)
      · exact Or.inr (Or.inl (by simpa only [named] using congrArg (fun u => (e u).val) h))
      · exact Or.inr (Or.inr ((rel y hy x hx).mpr h))
  · intro x hx y hy hadj
    rcases helim ((adjacent x hx y hy).mpr hadj) with h | h
    · exact Or.inr (Or.inl ((rel x hx y hy).mpr h))
    · exact Or.inr (Or.inr ((rel y hy x hx).mpr h))
  · intro v hv
    rintro ⟨values,hdom,hfront,hinj⟩
    let f : Fin (b+1) → Fin n := fun i => name (values i) (hdom i)
    have hf : ∀ i, RegionBag G O (name v hv) (f i) := by
      intro i
      rcases hfront i with he | ⟨huv,z,hz,hvz,huz⟩
      · exact Or.inl (e.injective (Subtype.ext (by simpa only [f,named] using he)))
      · refine Or.inr ⟨(rel _ (hdom i) _ hv).mp huv,name z hz,?_,
          (adjacent _ (hdom i) _ hz).mpr huz⟩
        rcases hvz with he | hr
        · exact Or.inr (e.injective (Subtype.ext (by simpa only [f,named] using he)))
        · exact Or.inl ((rel _ hv _ hz).mp hr)
    have hi : Function.Injective f := by
      intro i j he
      apply hinj
      simpa only [f,named] using congrArg (fun u => (e u).val) he
    exact (FiniteTupleBound.repeats_iff_card_le _ b).mpr (hb (name v hv)) f hf hi

#print axioms named_order_admissible
end StackSorting.SparseEndpointMSO.EliminationSyntax
