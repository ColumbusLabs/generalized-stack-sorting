import MarginalRootedFamily

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k)

/-- All local nodes together use exactly one original-vertex channel and one
outer-owner channel, regardless of the number or sizes of margins. -/
abbrev LocalLabels := Sigma (fun x : Fin t => Option (Fin (F.vertices x)))

def flattenLocal : F.LocalLabels → Fin n ⊕ Fin t
  | ⟨x,none⟩ => .inr x
  | ⟨x,some u⟩ => .inl (F.names x u).val

noncomputable def expandLocal : Fin n ⊕ Fin t → F.LocalLabels
  | .inr x => ⟨x,none⟩
  | .inl v => ⟨introductionNode D v,some ((F.names (introductionNode D v)).symm ⟨v,rfl⟩)⟩

theorem flatten_expand (z : Fin n ⊕ Fin t) : F.flattenLocal (F.expandLocal z)=z := by
  cases z with
  | inl v => simp only [expandLocal,flattenLocal,Equiv.apply_symm_apply]
  | inr x => rfl

theorem expand_flatten (z : F.LocalLabels) : F.expandLocal (F.flattenLocal z)=z := by
  rcases z with ⟨x,z⟩
  cases z with
  | none => rfl
  | some u =>
    have aux (v : Fin n) (hx : introductionNode D v=x) :
        F.expandLocal (.inl v)=⟨x,some ((F.names x).symm ⟨v,hx⟩)⟩ := by
      subst x
      rfl
    change F.expandLocal (.inl (F.names x u).val)=_
    rw [aux _ (F.names x u).property]
    apply congrArg (fun z => (⟨x,some z⟩ : F.LocalLabels))
    exact (F.names x).symm_apply_apply u

noncomputable def localLabelsEquiv : F.LocalLabels ≃ Fin n ⊕ Fin t where
  toFun := F.flattenLocal
  invFun := F.expandLocal
  left_inv := F.expand_flatten
  right_inv := F.flatten_expand

@[simp] theorem flatten_vertex (x : Fin t) (u : Fin (F.vertices x)) :
    F.localLabelsEquiv ⟨x,some u⟩=.inl (F.names x u).val := rfl
@[simp] theorem flatten_root (x : Fin t) : F.localLabelsEquiv ⟨x,none⟩=.inr x := rfl

#print axioms localLabelsEquiv
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
