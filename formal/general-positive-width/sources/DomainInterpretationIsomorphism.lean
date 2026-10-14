import CanonicalCodeIsomorphism

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseEndpointMSO.DomainInterpretation

/-- Two actual-domain interpretations of the same carrier produce the full
finite-model isomorphism, extending the on-domain map harmlessly by zero. -/
noncomputable def modelIsomorphism {P : Type} {D E : Model} {R : Relations P}
    (J : DomainInterpretation D R) (K : DomainInterpretation E R) : Isomorphism D E := by
  classical
  let f := J.vertex.symm.trans K.vertex
  let g := K.vertex.symm.trans J.vertex
  let toName (x : Nat) := if h : x ∈ D.domain then (f ⟨x,h⟩).val else 0
  let fromName (y : Nat) := if h : y ∈ E.domain then (g ⟨y,h⟩).val else 0
  have hto (x : Nat) (hx : x ∈ D.domain) : toName x=(f ⟨x,hx⟩).val := by simp [toName,hx]
  have hfrom (y : Nat) (hy : y ∈ E.domain) : fromName y=(g ⟨y,hy⟩).val := by simp [fromName,hy]
  have hfg (x : {x // x ∈ D.domain}) : g (f x)=x := by
    change J.vertex (K.vertex.symm (K.vertex (J.vertex.symm x)))=x
    rw [K.vertex.symm_apply_apply,J.vertex.apply_symm_apply]
  have hgf (y : {y // y ∈ E.domain}) : f (g y)=y := by
    change K.vertex (J.vertex.symm (J.vertex (K.vertex.symm y)))=y
    rw [J.vertex.symm_apply_apply,K.vertex.apply_symm_apply]
  refine {
    toFun := toName
    invFun := fromName
    to_mem := ?_
    inv_mem := ?_
    left_inv := ?_
    right_inv := ?_
    insert_iff := ?_
    remove_iff := ?_
    successor_iff := ?_
    matching_iff := ?_ }
  · intro x hx
    rw [hto x hx]
    exact (f ⟨x,hx⟩).property
  · intro y hy
    rw [hfrom y hy]
    exact (g ⟨y,hy⟩).property
  · intro x hx
    rw [hto x hx,hfrom _ (f ⟨x,hx⟩).property]
    exact congrArg Subtype.val (hfg ⟨x,hx⟩)
  · intro y hy
    rw [hfrom y hy,hto _ (g ⟨y,hy⟩).property]
    exact congrArg Subtype.val (hgf ⟨y,hy⟩)
  · intro x hx
    rw [hto x hx]
    have h := (J.insert_iff (J.vertex.symm ⟨x,hx⟩)).trans
      (K.insert_iff (J.vertex.symm ⟨x,hx⟩)).symm
    simpa only [f,Equiv.trans_apply,J.vertex.apply_symm_apply] using h
  · intro x hx
    rw [hto x hx]
    have h := (J.remove_iff (J.vertex.symm ⟨x,hx⟩)).trans
      (K.remove_iff (J.vertex.symm ⟨x,hx⟩)).symm
    simpa only [f,Equiv.trans_apply,J.vertex.apply_symm_apply] using h
  · intro x hx y hy
    rw [hto x hx,hto y hy]
    have h := (J.successor_iff (J.vertex.symm ⟨x,hx⟩) (J.vertex.symm ⟨y,hy⟩)).trans
      (K.successor_iff (J.vertex.symm ⟨x,hx⟩) (J.vertex.symm ⟨y,hy⟩)).symm
    simpa only [f,Equiv.trans_apply,J.vertex.apply_symm_apply] using h
  · intro x hx y hy
    rw [hto x hx,hto y hy]
    have h := (J.matching_iff (J.vertex.symm ⟨x,hx⟩) (J.vertex.symm ⟨y,hy⟩)).trans
      (K.matching_iff (J.vertex.symm ⟨x,hx⟩) (J.vertex.symm ⟨y,hy⟩)).symm
    simpa only [f,Equiv.trans_apply,J.vertex.apply_symm_apply] using h

#print axioms modelIsomorphism
end StackSorting.SparseEndpointMSO.DomainInterpretation
