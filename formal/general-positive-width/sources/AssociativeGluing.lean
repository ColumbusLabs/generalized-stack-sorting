import BiInterfaceGraph

noncomputable section

namespace StackSorting.BiInterface
variable {k : ℕ} {U V W : Type*}
variable (G : Graph k U) (H : Graph k V) (K : Graph k W)

private def assocAB : Glued G H → Glued G (glue H K) :=
  glueLift G H (inLeft G (glue H K))
    (fun v => inRight G (glue H K) (inLeft H K v)) (by
      intro u v huv
      obtain ⟨i, hi, hj⟩ := huv
      apply (inLeft_eq_inRight G (glue H K) _ _).mpr
      exact ⟨i, hi, by simp [glue, hj]⟩)

def assocForward : Glued (glue G H) K → Glued G (glue H K) :=
  glueLift (glue G H) K (assocAB G H K)
    (fun w => inRight G (glue H K) (inRight H K w)) (by
      intro q w hqw
      obtain ⟨i, hi, hj⟩ := hqw
      obtain ⟨v, hv, hq⟩ := Option.map_eq_some_iff.mp hi
      subst q
      change inRight G (glue H K) (inLeft H K v) = _
      apply congrArg
      exact (inLeft_eq_inRight H K v w).mpr ⟨i, hv, hj⟩)

private def assocBC : Glued H K → Glued (glue G H) K :=
  glueLift H K (fun v => inLeft (glue G H) K (inRight G H v))
    (inRight (glue G H) K) (by
      intro v w hvw
      obtain ⟨i, hi, hj⟩ := hvw
      apply (inLeft_eq_inRight (glue G H) K _ _).mpr
      exact ⟨i, by simp [glue, hi], hj⟩)

def assocReverse : Glued G (glue H K) → Glued (glue G H) K :=
  glueLift G (glue H K)
    (fun u => inLeft (glue G H) K (inLeft G H u)) (assocBC G H K) (by
      intro u q huq
      obtain ⟨i, hi, hj⟩ := huq
      obtain ⟨v, hv, hq⟩ := Option.map_eq_some_iff.mp hj
      subst q
      change inLeft (glue G H) K (inLeft G H u) = _
      apply congrArg
      exact (inLeft_eq_inRight G H u v).mpr ⟨i, hi, hv⟩)

@[simp] theorem assocForward_A (u : U) :
    assocForward G H K (inLeft (glue G H) K (inLeft G H u)) =
      inLeft G (glue H K) u := rfl
@[simp] theorem assocForward_B (v : V) :
    assocForward G H K (inLeft (glue G H) K (inRight G H v)) =
      inRight G (glue H K) (inLeft H K v) := rfl
@[simp] theorem assocForward_C (w : W) :
    assocForward G H K (inRight (glue G H) K w) =
      inRight G (glue H K) (inRight H K w) := rfl
@[simp] theorem assocReverse_A (u : U) :
    assocReverse G H K (inLeft G (glue H K) u) =
      inLeft (glue G H) K (inLeft G H u) := rfl
@[simp] theorem assocReverse_B (v : V) :
    assocReverse G H K (inRight G (glue H K) (inLeft H K v)) =
      inLeft (glue G H) K (inRight G H v) := rfl
@[simp] theorem assocReverse_C (w : W) :
    assocReverse G H K (inRight G (glue H K) (inRight H K w)) =
      inRight (glue G H) K w := rfl

noncomputable def associator : Glued (glue G H) K ≃ Glued G (glue H K) where
  toFun := assocForward G H K
  invFun := assocReverse G H K
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with | h q =>
      cases q with
      | inl q => induction q using Quotient.inductionOn with | h q => cases q <;> rfl
      | inr w => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with | h q =>
      cases q with
      | inl u => rfl
      | inr q => induction q using Quotient.inductionOn with | h q => cases q <;> rfl

private theorem forward_adj {a b} (hab : (glue (glue G H) K).Adj a b) :
    (glue G (glue H K)).Adj (assocForward G H K a) (assocForward G H K b) := by
  rcases hab with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
  · rcases hxy with ⟨u,v,huv,rfl,rfl⟩ | ⟨u,v,huv,rfl,rfl⟩
    · exact Or.inl ⟨u,v,huv,rfl,rfl⟩
    · exact Or.inr ⟨inLeft H K u,inLeft H K v,Or.inl ⟨u,v,huv,rfl,rfl⟩,rfl,rfl⟩
  · exact Or.inr ⟨inRight H K x,inRight H K y,Or.inr ⟨x,y,hxy,rfl,rfl⟩,rfl,rfl⟩

private theorem reverse_adj {a b} (hab : (glue G (glue H K)).Adj a b) :
    (glue (glue G H) K).Adj (assocReverse G H K a) (assocReverse G H K b) := by
  rcases hab with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
  · exact Or.inl ⟨inLeft G H x,inLeft G H y,Or.inl ⟨x,y,hxy,rfl,rfl⟩,rfl,rfl⟩
  · rcases hxy with ⟨u,v,huv,rfl,rfl⟩ | ⟨u,v,huv,rfl,rfl⟩
    · exact Or.inl ⟨inRight G H u,inRight G H v,Or.inr ⟨u,v,huv,rfl,rfl⟩,rfl,rfl⟩
    · exact Or.inr ⟨u,v,huv,rfl,rfl⟩

theorem associator_adj (a b : Glued (glue G H) K) :
    (glue G (glue H K)).Adj (associator G H K a) (associator G H K b) ↔
      (glue (glue G H) K).Adj a b := by
  constructor
  · intro h
    have hh := reverse_adj G H K h
    change (glue (glue G H) K).Adj
      ((associator G H K).symm (associator G H K a))
      ((associator G H K).symm (associator G H K b)) at hh
    simpa using hh
  · exact forward_adj G H K

theorem associator_left (i : Fin k) :
    ((glue (glue G H) K).left i).map (associator G H K) =
      (glue G (glue H K)).left i := by
  cases h : G.left i <;> simp [glue, h, associator]
  rfl

theorem associator_right (i : Fin k) :
    ((glue (glue G H) K).right i).map (associator G H K) =
      (glue G (glue H K)).right i := by
  cases h : K.right i <;> simp [glue, h, associator]
  rfl

#print axioms associator_adj
end StackSorting.BiInterface
