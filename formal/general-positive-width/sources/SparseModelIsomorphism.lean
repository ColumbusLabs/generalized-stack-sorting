import SparseModelInverse

namespace StackSorting.SparseEndpointMSO

/-- An actual two-sided finite-domain isomorphism. No total bijection on Nat
and no agreement of irrelevant off-domain predicates is required. -/
structure Isomorphism (D E : Model) where
  toFun : Nat → Nat
  invFun : Nat → Nat
  to_mem : ∀ x ∈ D.domain, toFun x ∈ E.domain
  inv_mem : ∀ y ∈ E.domain, invFun y ∈ D.domain
  left_inv : ∀ x ∈ D.domain, invFun (toFun x) = x
  right_inv : ∀ y ∈ E.domain, toFun (invFun y) = y
  insert_iff : ∀ x ∈ D.domain, D.I x ↔ E.I (toFun x)
  remove_iff : ∀ x ∈ D.domain, D.R x ↔ E.R (toFun x)
  successor_iff : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.S x y ↔ E.S (toFun x) (toFun y)
  matching_iff : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y ↔ E.M (toFun x) (toFun y)

theorem Isomorphism.injective {D E : Model} (iso : Isomorphism D E)
    {x y : Nat} (hx : x ∈ D.domain) (hy : y ∈ D.domain)
    (he : iso.toFun x = iso.toFun y) : x = y := by
  have hh := congrArg iso.invFun he
  simpa only [iso.left_inv x hx, iso.left_inv y hy] using hh

def Isomorphism.symm {D E : Model} (iso : Isomorphism D E) : Isomorphism E D where
  toFun := iso.invFun
  invFun := iso.toFun
  to_mem := iso.inv_mem
  inv_mem := iso.to_mem
  left_inv := iso.right_inv
  right_inv := iso.left_inv
  insert_iff y hy := by
    simpa only [iso.right_inv y hy] using (iso.insert_iff _ (iso.inv_mem y hy)).symm
  remove_iff y hy := by
    simpa only [iso.right_inv y hy] using (iso.remove_iff _ (iso.inv_mem y hy)).symm
  successor_iff x hx y hy := by
    simpa only [iso.right_inv x hx, iso.right_inv y hy] using
      (iso.successor_iff _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)).symm
  matching_iff x hx y hy := by
    simpa only [iso.right_inv x hx, iso.right_inv y hy] using
      (iso.matching_iff _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)).symm

def Isomorphism.trans {D E F : Model} (a : Isomorphism D E) (b : Isomorphism E F) :
    Isomorphism D F where
  toFun x := b.toFun (a.toFun x)
  invFun x := a.invFun (b.invFun x)
  to_mem x hx := b.to_mem _ (a.to_mem x hx)
  inv_mem x hx := a.inv_mem _ (b.inv_mem x hx)
  left_inv x hx := by rw [b.left_inv _ (a.to_mem x hx), a.left_inv x hx]
  right_inv x hx := by rw [a.right_inv _ (b.inv_mem x hx), b.right_inv x hx]
  insert_iff x hx := (a.insert_iff x hx).trans (b.insert_iff _ (a.to_mem x hx))
  remove_iff x hx := (a.remove_iff x hx).trans (b.remove_iff _ (a.to_mem x hx))
  successor_iff x hx y hy := (a.successor_iff x hx y hy).trans
    (b.successor_iff _ (a.to_mem x hx) _ (a.to_mem y hy))
  matching_iff x hx y hy := (a.matching_iff x hx y hy).trans
    (b.matching_iff _ (a.to_mem x hx) _ (a.to_mem y hy))

def supportIsomorphism (D : Model) : Isomorphism D (supported D) where
  toFun := id
  invFun := id
  to_mem _ hx := hx
  inv_mem _ hx := hx
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  insert_iff x hx := by simp [supported, hx]
  remove_iff x hx := by simp [supported, hx]
  successor_iff x hx y hy := by simp [supported, hx, hy]
  matching_iff x hx y hy := by simp [supported, hx, hy]

/-- Full sparse-MSO invariance, including both first-order quantifier kinds
and all bounded monadic subsets. -/
theorem Isomorphism.eval {D E : Model} (iso : Isomorphism D E) (f : Formula a b)
    (envD envE : Fin a → Nat) (setsD setsE : Fin b → Nat → Prop)
    (hdom : ∀ i, envD i ∈ D.domain) (henv : ∀ i, envE i = iso.toFun (envD i))
    (hsets : ∀ X x, x ∈ D.domain → (setsE X (iso.toFun x) ↔ setsD X x)) :
    Eval D f envD setsD ↔ Eval E f envE setsE := by
  induction f with
  | truth => rfl
  | equal i j =>
    simp only [Eval, henv]
    exact ⟨congrArg iso.toFun, iso.injective (hdom i) (hdom j)⟩
  | member i X =>
    simp only [Eval, henv]
    exact (hsets X _ (hdom i)).symm
  | insert i => simpa only [Eval, henv] using iso.insert_iff _ (hdom i)
  | remove i => simpa only [Eval, henv] using iso.remove_iff _ (hdom i)
  | successor i j =>
    simpa only [Eval, henv] using iso.successor_iff _ (hdom i) _ (hdom j)
  | matching i j =>
    simpa only [Eval, henv] using iso.matching_iff _ (hdom i) _ (hdom j)
  | neg f ih => exact not_congr (ih envD envE setsD setsE hdom henv hsets)
  | conj f g ihf ihg => exact and_congr (ihf _ _ _ _ hdom henv hsets) (ihg _ _ _ _ hdom henv hsets)
  | implies f g ihf ihg => exact imp_congr (ihf _ _ _ _ hdom henv hsets) (ihg _ _ _ _ hdom henv hsets)
  | existsFO k f ih =>
    constructor
    · rintro ⟨v, hv, hf⟩
      let w := fun i => iso.toFun (v i)
      refine ⟨w, fun i => iso.to_mem _ (hv i), ?_⟩
      exact (ih _ _ _ _
        (fun i => Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hdom j) i)
        (fun i => Fin.addCases (fun j => by simp [w]) (fun j => by simpa using henv j) i)
        hsets).mp hf
    · rintro ⟨w, hw, hf⟩
      let v := fun i => iso.invFun (w i)
      refine ⟨v, fun i => iso.inv_mem _ (hw i), ?_⟩
      exact (ih _ _ _ _
        (fun i => Fin.addCases (fun j => by simpa [v] using iso.inv_mem _ (hw j))
          (fun j => by simpa using hdom j) i)
        (fun i => Fin.addCases (fun j => by simpa [v] using (iso.right_inv _ (hw j)).symm)
          (fun j => by simpa using henv j) i) hsets).mpr hf
  | allFO k f ih =>
    constructor
    · intro h w hw
      let v := fun i => iso.invFun (w i)
      have hv : ∀ i, v i ∈ D.domain := fun i => iso.inv_mem _ (hw i)
      exact (ih _ _ _ _
        (fun i => Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hdom j) i)
        (fun i => Fin.addCases (fun j => by simpa [v] using (iso.right_inv _ (hw j)).symm)
          (fun j => by simpa using henv j) i) hsets).mp (h v hv)
    · intro h v hv
      let w := fun i => iso.toFun (v i)
      have hw : ∀ i, w i ∈ E.domain := fun i => iso.to_mem _ (hv i)
      exact (ih _ _ _ _
        (fun i => Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hdom j) i)
        (fun i => Fin.addCases (fun j => by simp [w]) (fun j => by simpa using henv j) i)
        hsets).mpr (h w hw)
  | allSet f ih =>
    constructor
    · intro h Y hY
      let X := fun x => x ∈ D.domain ∧ Y (iso.toFun x)
      have hX : ∀ x, X x → x ∈ D.domain := fun _ hx => hx.1
      apply (ih _ _ _ _ hdom henv ?_).mp (h X hX)
      intro Z x hx
      exact Fin.cases (by simp [X, hx]) (fun Z => hsets Z x hx) Z
    · intro h X hX
      let Y := fun y => y ∈ E.domain ∧ X (iso.invFun y)
      have hY : ∀ y, Y y → y ∈ E.domain := fun _ hy => hy.1
      apply (ih _ _ _ _ hdom henv ?_).mpr (h Y hY)
      intro Z x hx
      exact Fin.cases (by simp [Y, iso.to_mem x hx, iso.left_inv x hx])
        (fun Z => hsets Z x hx) Z

theorem Isomorphism.satisfies {D E : Model} (iso : Isomorphism D E) (f : Formula 0 0) :
    Satisfies D f ↔ Satisfies E f :=
  iso.eval f Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun X => Fin.elim0 X)

theorem Isomorphism.walk {D E : Model} (iso : Isomorphism D E)
    {x y : Nat} (hw : Walk D x y) : Walk E (iso.toFun x) (iso.toFun y) := by
  induction hw with
  | refl hx => exact .refl (iso.to_mem x hx)
  | @step p q hp hq hs ih =>
    exact .step ih (iso.to_mem q hq) ((iso.successor_iff p hp.mem q hq).mp hs)

theorem Isomorphism.closedReach {D E : Model} (iso : Isomorphism D E)
    {x y : Nat} (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    ClosedReach D x y ↔ ClosedReach E (iso.toFun x) (iso.toFun y) := by
  rw [closedReach_iff_walk D hx, closedReach_iff_walk E (iso.to_mem x hx)]
  constructor
  · exact iso.walk
  · intro hw
    have hh := iso.symm.walk hw
    simpa only [Isomorphism.symm, iso.left_inv x hx, iso.left_inv y hy] using hh

#print axioms Isomorphism.eval
#print axioms Isomorphism.satisfies
#print axioms Isomorphism.closedReach
end StackSorting.SparseEndpointMSO
