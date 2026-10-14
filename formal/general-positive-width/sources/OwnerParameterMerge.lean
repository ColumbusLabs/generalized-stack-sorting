import SparseParametricComposition

set_option backward.isDefEq.respectTransparency false
namespace StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
variable {LocalAtom : Nat → Type}

/-- The global carrier is a disjoint union, not an overlapping union. -/
def merge {ι : Type} {β : ι → Type} (loc : ∀ i, Fin d → β i → Prop) :
    Fin d → (Sigma β) → Prop := fun j z => loc z.1 j z.2

@[simp] theorem merge_restrict {ι : Type} {β : ι → Type}
    (loc : ∀ i, Fin d → β i → Prop) (i : ι) (j : Fin d) (v : β i) :
    merge loc j ⟨i,v⟩ ↔ loc i j v := Iff.rfl

theorem owners_disjoint {ι : Type} {β : ι → Type} {i j : ι}
    (h : i≠j) (u : β i) (v : β j) : (⟨i,u⟩ : Sigma β)≠⟨j,v⟩ := by
  intro he
  exact h (congrArg Sigma.fst he)

/-- One ownership relation is added for relativization. Its anchor is an
ordinary free first-order variable and is shifted under every FO binder. -/
inductive Atom (LocalAtom : Nat → Type) : Nat → Type where
  | loc {r : Nat} : LocalAtom r → Atom LocalAtom r
  | belongs : Atom LocalAtom 2

def atoms {α : Type} (loc : {r : Nat} → LocalAtom r → (Fin r → α) → Prop)
    (belongs : α → α → Prop) : {r : Nat} → Atom LocalAtom r → (Fin r → α) → Prop
  | _, .loc A, env => loc A env
  | _, .belongs, env => belongs (env 0) (env 1)

abbrev Fiber {α : Type} (belongs : α → α → Prop) (owner : α) := {x : α // belongs owner x}

def fiberAtoms {α : Type} (loc : {r : Nat} → LocalAtom r → (Fin r → α) → Prop)
    (belongs : α → α → Prop) (owner : α) :
    {r : Nat} → LocalAtom r → (Fin r → Fiber belongs owner) → Prop :=
  fun A env => loc A (fun i => (env i).val)

def guard (owner v : Fin n) : CopyFormula (Atom LocalAtom) n b :=
  .atom .belongs (fun i => if i=0 then owner else v)

/-- SO binders range over all global sets. Their restrictions range over all
loc sets, so no extra owner set parameter and no SO support oracle is needed. -/
def relativize : CopyFormula LocalAtom a b → (Fin a → Fin n) → Fin n →
    CopyFormula (Atom LocalAtom) n b
  | .truth, _, _ => .truth
  | .equal i j, vars, _ => .equal (vars i) (vars j)
  | .member i X, vars, _ => .member (vars i) X
  | .atom A args, vars, _ => .atom (.loc A) (fun i => vars (args i))
  | .neg p, vars, owner => .neg (relativize p vars owner)
  | .conj p q, vars, owner => .conj (relativize p vars owner) (relativize q vars owner)
  | .implies p q, vars, owner => .implies (relativize p vars owner) (relativize q vars owner)
  | .existsFO p, vars, owner => .existsFO (.conj (guard owner.succ 0)
      (relativize p (Fin.cases 0 (fun i => (vars i).succ)) owner.succ))
  | .allFO p, vars, owner => .allFO (.implies (guard owner.succ 0)
      (relativize p (Fin.cases 0 (fun i => (vars i).succ)) owner.succ))
  | .allSet p, vars, owner => .allSet (relativize p vars owner)

@[simp] theorem eval_guard {α : Type}
    (loc : {r : Nat} → LocalAtom r → (Fin r → α) → Prop)
    (belongs : α → α → Prop) (owner v : Fin n)
    (env : Fin n → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms loc belongs) (guard owner v) env sets ↔ belongs (env owner) (env v) := by
  simp [guard,ActualEval,atoms]

/-- Complete loc/global formula correspondence, including arbitrary nesting
of FO and SO binders. Empty fibers are covered without choosing an element. -/
theorem eval_relativize {α : Type}
    (loc : {r : Nat} → LocalAtom r → (Fin r → α) → Prop)
    (belongs : α → α → Prop) (owner : α) (p : CopyFormula LocalAtom a b)
    (vars : Fin a → Fin n) (anchor : Fin n) (env : Fin n → α)
    (localEnv : Fin a → Fiber belongs owner)
    (sets : Fin b → α → Prop) (localSets : Fin b → Fiber belongs owner → Prop)
    (ha : env anchor=owner) (hv : ∀ i, env (vars i)=(localEnv i).val)
    (hs : ∀ j v, sets j v.val ↔ localSets j v) :
    ActualEval (atoms loc belongs) (relativize p vars anchor) env sets ↔
      ActualEval (fiberAtoms loc belongs owner) p localEnv localSets := by
  induction p generalizing n with
  | truth => rfl
  | equal i j =>
    simp only [relativize,ActualEval,hv]
    exact ⟨Subtype.ext,congrArg Subtype.val⟩
  | member i X => simpa only [relativize,ActualEval,hv] using hs X (localEnv i)
  | atom A args =>
    simp only [relativize,ActualEval,atoms,fiberAtoms]
    have he : (fun i => env (vars (args i)))=(fun i => (localEnv (args i)).val) :=
      funext (fun i => hv (args i))
    rw [he]
  | neg p ih => exact not_congr (ih vars anchor env localEnv sets localSets ha hv hs)
  | conj p q ihp ihq =>
    exact and_congr
      (ihp vars anchor env localEnv sets localSets ha hv hs)
      (ihq vars anchor env localEnv sets localSets ha hv hs)
  | implies p q ihp ihq =>
    exact imp_congr
      (ihp vars anchor env localEnv sets localSets ha hv hs)
      (ihq vars anchor env localEnv sets localSets ha hv hs)
  | existsFO p ih =>
    simp only [relativize,ActualEval,eval_guard,Fin.cases_succ,Fin.cases_zero,ha]
    constructor
    · rintro ⟨v,hv',hp⟩
      refine ⟨⟨v,hv'⟩,?_⟩
      exact (ih (n := n+1) (Fin.cases (0 : Fin (n+1)) (fun i => (vars i).succ)) anchor.succ (Fin.cases v env) (Fin.cases ⟨v,hv'⟩ localEnv) sets localSets (by simpa only [Fin.cases_succ] using ha) (by intro i; refine Fin.cases ?_ (fun j => ?_) i; rfl; exact hv j) hs).mp hp
    · rintro ⟨v,hp⟩
      refine ⟨v.val,v.property,?_⟩
      exact (ih (n := n+1) (Fin.cases (0 : Fin (n+1)) (fun i => (vars i).succ)) anchor.succ (Fin.cases v.val env) (Fin.cases v localEnv) sets localSets (by simpa only [Fin.cases_succ] using ha) (by intro i; refine Fin.cases ?_ (fun j => ?_) i; rfl; exact hv j) hs).mpr hp
  | allFO p ih =>
    simp only [relativize,ActualEval,eval_guard,Fin.cases_succ,Fin.cases_zero,ha]
    constructor
    · intro h v
      exact (ih (n := n+1) (Fin.cases (0 : Fin (n+1)) (fun i => (vars i).succ)) anchor.succ (Fin.cases v.val env) (Fin.cases v localEnv) sets localSets (by simpa only [Fin.cases_succ] using ha) (by intro i; refine Fin.cases ?_ (fun j => ?_) i; rfl; exact hv j) hs).mp (h v.val v.property)
    · intro h v hv'
      exact (ih (n := n+1) (Fin.cases (0 : Fin (n+1)) (fun i => (vars i).succ)) anchor.succ (Fin.cases v env) (Fin.cases ⟨v,hv'⟩ localEnv) sets localSets (by simpa only [Fin.cases_succ] using ha) (by intro i; refine Fin.cases ?_ (fun j => ?_) i; rfl; exact hv j) hs).mpr (h ⟨v,hv'⟩)
  | allSet p ih =>
    simp only [relativize,ActualEval]
    constructor
    · intro h X
      let Y : α → Prop := fun z => ∃ v : Fiber belongs owner, v.val=z ∧ X v
      apply (ih vars anchor env localEnv (Fin.cases Y sets) (Fin.cases X localSets) ha hv ?_).mp (h Y)
      intro j v
      refine Fin.cases ?_ (fun q => hs q v) j
      change (∃ w : Fiber belongs owner, w.val=v.val ∧ X w) ↔ X v
      constructor
      · rintro ⟨w,he,hw⟩
        exact (Subtype.ext he : w=v) ▸ hw
      · intro hx; exact ⟨v,rfl,hx⟩
    · intro h Y
      apply (ih vars anchor env localEnv (Fin.cases Y sets)
        (Fin.cases (fun v => Y v.val) localSets) ha hv ?_).mpr (h (fun v => Y v.val))
      intro j v
      exact Fin.cases Iff.rfl (fun q => hs q v) j

#print axioms merge_restrict
#print axioms owners_disjoint
#print axioms eval_relativize
end StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
