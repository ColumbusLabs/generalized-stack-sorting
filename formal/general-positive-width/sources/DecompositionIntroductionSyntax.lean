import NestedFlatteningRealization

namespace StackSorting.GraphWidth.Nested.IntroductionSyntax
open FinitePort
open StackSorting.SparseEndpointMSO.FiniteCopy
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

abbrev Carrier (n t : Nat) := Fin n ⊕ Fin t

private theorem cases_one {a : Nat} {α : Type} (x : α) (f : Fin (a+1) → α) :
    Fin.cases x f (1 : Fin (a+2))=f 0 := rfl

def atoms (D : Decomposition G T) : {r : Nat} → Syntax.OutputAtom r →
    (Fin r → Carrier n t) → Prop
  | _,.original,env => match env 0 with | .inl _ => True | _ => False
  | _,.node,env => match env 0 with | .inr _ => True | _ => False
  | _,.parent,env => match env 0,env 1 with
      | .inr i,.inr j => i.val≠0 ∧ T.parent i=j
      | _,_ => False
  | _,.bag,env => match env 0,env 1 with
      | .inr i,.inl v => v∈D.bag i
      | _,_ => False
  | _,.originalEdge,env => match env 0,env 1 with
      | .inl u,.inl v => G.Adj u v
      | _,_ => False

def unary (A : Syntax.OutputAtom 1) (i : Fin a) : CopyFormula Syntax.OutputAtom a b :=
  .atom A (fun _ => i)
def binary (A : Syntax.OutputAtom 2) (i j : Fin a) : CopyFormula Syntax.OutputAtom a b :=
  .atom A (fun q => if q=0 then i else j)

/-- Ordinary ancestor reachability through strict actual parent edges. The
closed-set formula explicitly guards both node endpoints. -/
def ancestorAt (x y : Fin a) : CopyFormula Syntax.OutputAtom a b :=
  .conj (unary .node x) (.conj (unary .node y) (.allSet
    (.implies (.conj (.member y 0) (.allFO (.allFO
      (.implies (binary .parent 1 0) (.implies (.member 1 0) (.member 0 0))))))
      (.member x 0))))

/-- Connected occurrences make the first covering bag exactly the covering
bag whose strict parent does not cover. No order or introduction atom is input. -/
def introducedAt (x v : Fin a) : CopyFormula Syntax.OutputAtom a b :=
  .conj (binary .bag x v) (.allFO
    (.implies (binary .parent x.succ 0) (.neg (binary .bag 0 v.succ))))

/-- Reflexive introduction preorder. Physical chronology will split equal
introduction classes only after this literal formula is pulled to S/M. -/
def preorderAt (u v : Fin a) : CopyFormula Syntax.OutputAtom a b :=
  .existsFO (.existsFO (.conj (introducedAt 1 u.succ.succ)
    (.conj (introducedAt 0 v.succ.succ) (ancestorAt 1 0))))

theorem ancestor_closed_iff (x y : Fin t) :
    Ancestor T x y ↔ ∀ X : Fin t → Prop, X y →
      (∀ z, z.val≠0 → X z → X (T.parent z)) → X x := by
  constructor
  · intro h
    induction h with
    | refl => intro X hx _; exact hx
    | @step z hz h ih =>
      intro X hzX closed
      exact ih X (closed z hz hzX) closed
  · intro h
    apply h (fun z => Ancestor T z y) (.refl _)
    intro z hz hzy
    exact (Ancestor.step hz (.refl _)).trans hzy

theorem introduced_iff (D : Decomposition G T) (i : Fin t) (v : Fin n) :
    (v∈D.bag i ∧ (i.val≠0 → v∉D.bag (T.parent i))) ↔ introductionNode D v=i := by
  constructor
  · rintro ⟨hv,hp⟩
    by_contra hn
    have ha := introduction_ancestor D hv
    exact hp (ha.ne_zero_of_strict hn) (adhesion_parent_mem ⟨hv,hn⟩)
  · rintro rfl
    refine ⟨(introduction_spec D v).1,?_⟩
    intro hi hp
    have hle := (introduction_spec D v).2 _ hp
    have hlt := T.parent_lt (introductionNode D v) hi
    omega

/-- Evaluation is capture-safe even under extra free set parameters. -/
theorem eval_ancestorAt (D : Decomposition G T) (x y : Fin a)
    (env : Fin a → Carrier n t) (sets : Fin b → Carrier n t → Prop) :
    ActualEval (atoms D) (ancestorAt x y) env sets ↔
      atoms D .node (fun _ => env x) ∧ atoms D .node (fun _ => env y) ∧
        ∀ X : Carrier n t → Prop, X (env y) →
          (∀ u v, atoms D .parent (Fin.cases u (fun _ => v)) → X u → X v) → X (env x) := by
  simp [ancestorAt,ActualEval,unary,binary,atoms,cases_one]

theorem ancestor_nodes_exact (D : Decomposition G T) (x y : Fin a)
    (env : Fin a → Carrier n t) (sets : Fin b → Carrier n t → Prop)
    (i j : Fin t) (hx : env x=.inr i) (hy : env y=.inr j) :
    ActualEval (atoms D) (ancestorAt x y) env sets ↔ Ancestor T i j := by
  rw [eval_ancestorAt,hx,hy]
  change (True ∧ True ∧ ∀ X : Carrier n t → Prop, X (.inr j) →
    (∀ u v, atoms D .parent (Fin.cases u (fun _ => v)) → X u → X v) → X (.inr i)) ↔ _
  simp only [true_and]
  constructor
  · intro h
    apply (ancestor_closed_iff i j).mpr
    intro X hj closed
    let Y : Carrier n t → Prop := fun q => match q with | .inl _ => False | .inr z => X z
    apply h Y hj
    intro u v hp hu
    cases u with
    | inl u => exact hp.elim
    | inr u =>
      cases v with
      | inl v => exact hp.elim
      | inr v =>
        obtain ⟨hz,rfl⟩ := hp
        exact closed u hz hu
  · intro h X hj closed
    apply (ancestor_closed_iff i j).mp h (fun z => X (.inr z)) hj
    intro z hz hh
    exact closed (.inr z) (.inr (T.parent z)) ⟨hz,rfl⟩ hh

theorem introduced_nodes_exact (D : Decomposition G T) (x v : Fin a)
    (env : Fin a → Carrier n t) (sets : Fin b → Carrier n t → Prop)
    (i : Fin t) (u : Fin n) (hx : env x=.inr i) (hv : env v=.inl u) :
    ActualEval (atoms D) (introducedAt x v) env sets ↔ introductionNode D u=i := by
  simpa [introducedAt,ActualEval,binary,atoms,hx,hv,Sum.forall] using introduced_iff D i u

def Introduced (D : Decomposition G T) (i v : Carrier n t) : Prop :=
  match i,v with | .inr i,.inl v => introductionNode D v=i | _,_ => False

theorem eval_introducedAt (D : Decomposition G T) (x v : Fin a)
    (env : Fin a → Carrier n t) (sets : Fin b → Carrier n t → Prop) :
    ActualEval (atoms D) (introducedAt x v) env sets ↔ Introduced D (env x) (env v) := by
  cases hx : env x with
  | inl w =>
    cases hv : env v <;> simp [introducedAt,ActualEval,binary,atoms,Introduced,hx,hv]
  | inr i =>
    cases hv : env v with
    | inl u => exact introduced_nodes_exact D x v env sets i u hx hv
    | inr j => simp [introducedAt,ActualEval,binary,atoms,Introduced,hx,hv]

theorem preorder_original_exact (D : Decomposition G T) (u v : Fin a)
    (env : Fin a → Carrier n t) (sets : Fin b → Carrier n t → Prop)
    (x y : Fin n) (hu : env u=.inl x) (hv : env v=.inl y) :
    ActualEval (atoms D) (preorderAt u v) env sets ↔
      Ancestor T (introductionNode D x) (introductionNode D y) := by
  change (∃ i j : Carrier n t,
    ActualEval (atoms D) (introducedAt 1 u.succ.succ) (Fin.cases j (Fin.cases i env)) sets ∧
    ActualEval (atoms D) (introducedAt 0 v.succ.succ) (Fin.cases j (Fin.cases i env)) sets ∧
    ActualEval (atoms D) (ancestorAt 1 0) (Fin.cases j (Fin.cases i env)) sets) ↔ _
  simp only [eval_introducedAt,Fin.cases_zero,Fin.cases_succ,hu,hv]
  constructor
  · rintro ⟨i,j,hi,hj,h⟩
    cases i with
    | inl w => exact hi.elim
    | inr i =>
      cases j with
      | inl w => exact hj.elim
      | inr j =>
        have hi' : introductionNode D x=i := hi
        have hj' : introductionNode D y=j := hj
        have h' := (ancestor_nodes_exact D 1 0 _ sets i j rfl rfl).mp h
        simpa only [hi',hj'] using h'
  · intro h
    refine ⟨.inr (introductionNode D x),.inr (introductionNode D y),rfl,rfl,?_⟩
    exact (ancestor_nodes_exact D (1 : Fin (a+2)) 0
      (Fin.cases (.inr (introductionNode D y)) (Fin.cases (.inr (introductionNode D x)) env))
      sets (introductionNode D x) (introductionNode D y) rfl rfl).mpr h

#print axioms ancestor_closed_iff
#print axioms introduced_iff
#print axioms eval_ancestorAt
#print axioms ancestor_nodes_exact
#print axioms introduced_nodes_exact
#print axioms preorder_original_exact
end StackSorting.GraphWidth.Nested.IntroductionSyntax
