import FiniteTreeMSOPositionCorrectness

set_option warningAsError true

namespace StackSorting.TreeAutomaton.Logic

variable {α β γ : Type}

/-- The address-preserving transport through annotation followed by relabelling. -/
def Position.annotateMap : (t : BinaryTree α) → (v : Position t → β) →
    (f : α × β → γ) → Position t → Position ((annotate t v).map f)
  | .nil, _, _, p => nomatch p
  | .node _ _ _, _, _, .root => .root
  | .node _ l _, v, f, .left p => .left (annotateMap l (fun q => v (.left q)) f p)
  | .node _ _ r, v, f, .right p => .right (annotateMap r (fun q => v (.right q)) f p)

/-- Inverse address transport; annotation creates no new position. -/
def Position.unannotateMap : (t : BinaryTree α) → (v : Position t → β) →
    (f : α × β → γ) → Position ((annotate t v).map f) → Position t
  | .nil, _, _, p => nomatch p
  | .node _ _ _, _, _, .root => .root
  | .node _ l _, v, f, .left p => .left (unannotateMap l (fun q => v (.left q)) f p)
  | .node _ _ r, v, f, .right p => .right (unannotateMap r (fun q => v (.right q)) f p)

@[simp] theorem Position.unannotateMap_annotateMap (t : BinaryTree α)
    (v : Position t → β) (f : α × β → γ) (p : Position t) :
    unannotateMap t v f (annotateMap t v f p) = p := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases p with
    | root => rfl
    | left p => exact congrArg Position.left (hl _ p)
    | right p => exact congrArg Position.right (hr _ p)

@[simp] theorem Position.annotateMap_unannotateMap (t : BinaryTree α)
    (v : Position t → β) (f : α × β → γ) (p : Position ((annotate t v).map f)) :
    annotateMap t v f (unannotateMap t v f p) = p := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases p with
    | root => rfl
    | left p => exact congrArg Position.left (hl _ p)
    | right p => exact congrArg Position.right (hr _ p)

/-- Annotation and relabelling preserve exactly the internal-node addresses. -/
def annotateMapEquiv (t : BinaryTree α) (v : Position t → β) (f : α × β → γ) :
    Position t ≃ Position ((annotate t v).map f) where
  toFun := Position.annotateMap t v f
  invFun := Position.unannotateMap t v f
  left_inv := Position.unannotateMap_annotateMap t v f
  right_inv := Position.annotateMap_unannotateMap t v f

@[simp] theorem annotateMapEquiv_label (t : BinaryTree α) (v : Position t → β)
    (f : α × β → γ) (p : Position t) :
    (annotateMapEquiv t v f p).label = f (p.label, v p) := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases p with
    | root => rfl
    | left p => exact hl _ p
    | right p => exact hr _ p

theorem Child.annotateMap {t : BinaryTree α} {d : Bool} {p q : Position t}
    (h : Child d p q) (v : Position t → β) (f : α × β → γ) :
    Child d (annotateMapEquiv t v f p) (annotateMapEquiv t v f q) := by
  induction h with
  | rootLeft => exact .rootLeft
  | rootRight => exact .rootRight
  | left h ih => exact .left (ih _)
  | right h ih => exact .right (ih _)

theorem Child.unannotateMap (t : BinaryTree α) (v : Position t → β)
    (f : α × β → γ) {d : Bool} {p q : Position ((annotate t v).map f)}
    (h : Child d p q) :
    Child d (Position.unannotateMap t v f p) (Position.unannotateMap t v f q) := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases l <;> cases r <;> cases h
    all_goals first
      | exact Child.rootLeft
      | exact Child.rootRight
      | (apply Child.left; apply hl; assumption)
      | (apply Child.right; apply hr; assumption)

@[simp] theorem annotateMapEquiv_child (t : BinaryTree α) (v : Position t → β)
    (f : α × β → γ) (d : Bool) (p q : Position t) :
    Child d (annotateMapEquiv t v f p) (annotateMapEquiv t v f q) ↔ Child d p q := by
  constructor
  · intro h
    simpa only [annotateMapEquiv, Equiv.coe_fn_mk,
      Position.unannotateMap_annotateMap] using h.unannotateMap t v f
  · intro h
    exact h.annotateMap v f

/-- Atomic semantics on any labelled structure with two directed child relations. -/
def Atom.EvalOn {P : Type} {n : Nat} (a : Atom α n) (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin n → P → Bool) : Prop :=
  match a with
  | .subset i j => ∀ p, v i p = true → v j p = true
  | .label i a => ∀ p, v i p = true → label p = a
  | .singleton i => ∃! p, v i p = true
  | .child d i j => ∃ p q, child d p q ∧ v i p = true ∧ v j q = true

/-- MSO semantics on a fixed domain: binders change only the valuation. -/
def Formula.EvalOn {P : Type} (label : P → α) (child : Bool → P → P → Prop) :
    {n : Nat} → Formula α n → (Fin n → P → Bool) → Prop
  | _, .atom a, v => a.EvalOn label child v
  | _, .neg p, v => ¬ p.EvalOn label child v
  | _, .conj p q, v => p.EvalOn label child v ∧ q.EvalOn label child v
  | _, .existsSet p, v => ∃ w : P → Bool, p.EvalOn label child (Fin.cons w v)
  | _, .existsFirst p, v => ∃ w : P → Bool,
      (∃! x : P, w x = true) ∧ p.EvalOn label child (Fin.cons w v)

/-- Natural fixed-tree atomic semantics on actual internal-node positions. -/
def Atom.EvalAt {n : Nat} (a : Atom α n) (t : BinaryTree α)
    (v : Fin n → Position t → Bool) : Prop := a.EvalOn Position.label (fun d p q => Child d p q) v

/-- Natural fixed-tree semantics. Every quantifier ranges over the same positions. -/
def Formula.EvalAt {n : Nat} (p : Formula α n) (t : BinaryTree α)
    (v : Fin n → Position t → Bool) : Prop := p.EvalOn Position.label (fun d p q => Child d p q) v

private theorem cons_equiv {P Q : Type} {n : Nat} (e : P ≃ Q)
    (v : Fin n → P → Bool) (w : Fin n → Q → Bool)
    (hv : ∀ i p, w i (e p) = v i p) (a : P → Bool) (b : Q → Bool)
    (hab : ∀ p, b (e p) = a p) :
    ∀ i p, (Fin.cons b w : Fin (n+1) → Q → Bool) i (e p) =
      (Fin.cons a v : Fin (n+1) → P → Bool) i p := by
  intro i p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hab p
  · exact hv _ _

/-- Formula semantics is invariant under a labelled-structure isomorphism. -/
theorem Formula.evalOn_equiv {P Q : Type} {n : Nat} (p : Formula α n)
    (e : P ≃ Q) (lP : P → α) (lQ : Q → α)
    (cP : Bool → P → P → Prop) (cQ : Bool → Q → Q → Prop)
    (hl : ∀ x, lQ (e x) = lP x)
    (hc : ∀ d x y, cQ d (e x) (e y) ↔ cP d x y)
    (v : Fin n → P → Bool) (w : Fin n → Q → Bool)
    (hv : ∀ i x, w i (e x) = v i x) :
    p.EvalOn lP cP v ↔ p.EvalOn lQ cQ w := by
  induction p with
  | atom a =>
    cases a with
    | subset i j =>
      simp only [Formula.EvalOn, Atom.EvalOn]
      rw [← e.forall_congr_right]
      simp only [hv]
    | label i a =>
      simp only [Formula.EvalOn, Atom.EvalOn]
      rw [← e.forall_congr_right]
      simp only [hv, hl]
    | singleton i =>
      exact e.existsUnique_congr (fun x => by simp only [hv])
    | child d i j =>
      simp only [Formula.EvalOn, Atom.EvalOn]
      rw [← e.exists_congr_right]
      apply exists_congr
      intro x
      rw [← e.exists_congr_right]
      simp only [hc, hv]
  | neg p ih => exact not_congr (ih _ _ hv)
  | conj p q hp hq => exact and_congr (hp _ _ hv) (hq _ _ hv)
  | existsSet p ih =>
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun x => a (e.symm x), (ih _ _ ?_).mp ha⟩
      exact cons_equiv e v w hv _ _ (by simp)
    · rintro ⟨b, hb⟩
      refine ⟨fun x => b (e x), (ih _ _ ?_).mpr hb⟩
      exact cons_equiv e v w hv _ _ (by simp)
  | existsFirst p ih =>
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨fun x => a (e.symm x), e.existsUnique_congr_left.mp ha, (ih _ _ ?_).mp h⟩
      exact cons_equiv e v w hv _ _ (by simp)
    · rintro ⟨b, hb, h⟩
      refine ⟨fun x => b (e x), e.existsUnique_congr_right.mpr hb, (ih _ _ ?_).mpr h⟩
      exact cons_equiv e v w hv _ _ (by simp)

/-- The accepted position semantics equals fixed-domain valuation semantics. -/
theorem Formula.posHolds_iff_evalOn {n : Nat} (p : Formula α n)
    (t : BinaryTree (Marked α n)) :
    p.PosHolds t ↔ p.EvalOn (fun x : Position t => x.label.1) (fun d p q => Child d p q)
      (fun i x => x.label.2 i) := by
  induction p with
  | atom a => cases a <;> rfl
  | neg p ih => exact not_congr (ih t)
  | conj p q hp hq => exact and_congr (hp t) (hq t)
  | @existsSet n p ih =>
    apply exists_congr
    intro v
    rw [ih]
    symm
    apply p.evalOn_equiv (annotateMapEquiv t v extend)
    · intro x; simp only [annotateMapEquiv_label, extend]
    · intro d x y; exact annotateMapEquiv_child t v extend d x y
    · intro i x
      simp only [annotateMapEquiv_label, extend]
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  | @existsFirst n p ih =>
    apply exists_congr
    intro v
    apply and_congr_right
    intro _
    rw [ih]
    symm
    apply p.evalOn_equiv (annotateMapEquiv t v extend)
    · intro x; simp only [annotateMapEquiv_label, extend]
    · intro d x y; exact annotateMapEquiv_child t v extend d x y
    · intro i x
      simp only [annotateMapEquiv_label, extend]
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Put every free-variable valuation into the labels of the unchanged tree. -/
def markTree {n : Nat} (t : BinaryTree α) (v : Fin n → Position t → Bool) :
    BinaryTree (Marked α n) := (annotate t (fun p i => v i p)).map id

@[simp] theorem markTree_eq_annotate {n : Nat} (t : BinaryTree α)
    (v : Fin n → Position t → Bool) :
    markTree t v = annotate t (fun p i => v i p) := by exact BinaryTree.id_map _

/-- Fixed-tree evaluation is exactly the already accepted position semantics. -/
theorem Formula.evalAt_iff_posHolds {n : Nat} (p : Formula α n)
    (t : BinaryTree α) (v : Fin n → Position t → Bool) :
    p.EvalAt t v ↔ p.PosHolds (markTree t v) := by
  rw [p.posHolds_iff_evalOn]
  apply p.evalOn_equiv (annotateMapEquiv t (fun p i => v i p) id)
  · intro x
    exact congrArg Prod.fst (annotateMapEquiv_label t (fun p i => v i p) id x)
  · intro d x y; exact annotateMapEquiv_child _ _ _ _ _ _
  · intro i x
    exact congrArg (fun a : Marked α n => a.2 i)
      (annotateMapEquiv_label t (fun p i => v i p) id x)

theorem Formula.evalAt_iff_holds [DecidableEq α] {n : Nat} (p : Formula α n)
    (t : BinaryTree α) (v : Fin n → Position t → Bool) :
    p.EvalAt t v ↔ p.Holds (markTree t v) := by
  rw [p.holds_iff_positions]
  exact p.evalAt_iff_posHolds t v

theorem annotate_label_map (t : BinaryTree α) (f : α → β) :
    annotate t (fun p => f p.label) = t.map (fun a => (a, f a)) := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    simpa only [annotate, BinaryTree.map, Position.label] using
      congrArg₂ (BinaryTree.node (a, f a)) hl hr

@[simp] theorem markTree_closed (t : BinaryTree α) :
    markTree t (Fin.elim0 : Fin 0 → Position t → Bool) =
      t.map (fun a => ((a, Fin.elim0) : Marked α 0)) := by
  rw [markTree_eq_annotate]
  have h : (fun p : Position t => fun i : Fin 0 => (Fin.elim0 i : Position t → Bool) p) =
      fun _ : Position t => (Fin.elim0 : Fin 0 → Bool) := by
    funext p i
    exact Fin.elim0 i
  rw [h]
  exact annotate_label_map t (fun _ => (Fin.elim0 : Fin 0 → Bool))

/-- Closed fixed-tree MSO properties have an actual finite-state recognizer. -/
theorem Formula.evalAt_recognizable [DecidableEq α] [Fintype α] (p : Formula α 0) :
    Recognizable {t : BinaryTree α | p.EvalAt t Fin.elim0} := by
  have h := p.positions_recognizable.preimage (fun a => ((a, Fin.elim0) : Marked α 0))
  simpa only [Set.mem_ofPred_eq, ← markTree_closed, ← Formula.evalAt_iff_posHolds] using h

/-- Extend a renaming under one fresh binder, which keeps index zero fixed. -/
def liftRename {n m : Nat} (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cons 0 (fun i => (ρ i).succ)

def Atom.rename {n m : Nat} (ρ : Fin n → Fin m) : Atom α n → Atom α m
  | .subset i j => .subset (ρ i) (ρ j)
  | .label i a => .label (ρ i) a
  | .singleton i => .singleton (ρ i)
  | .child d i j => .child d (ρ i) (ρ j)

def Formula.rename : {n m : Nat} → (Fin n → Fin m) → Formula α n → Formula α m
  | _, _, ρ, .atom a => .atom (a.rename ρ)
  | _, _, ρ, .neg p => .neg (p.rename ρ)
  | _, _, ρ, .conj p q => .conj (p.rename ρ) (q.rename ρ)
  | _, _, ρ, .existsSet p => .existsSet (p.rename (liftRename ρ))
  | _, _, ρ, .existsFirst p => .existsFirst (p.rename (liftRename ρ))

private theorem cons_rename {P : Type} {n m : Nat} (ρ : Fin n → Fin m)
    (v : Fin m → P → Bool) (w : P → Bool) :
    (fun i => (Fin.cons w v : Fin (m+1) → P → Bool) (liftRename ρ i)) =
      (Fin.cons w (fun i => v (ρ i)) : Fin (n+1) → P → Bool) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Renaming is interpreted by pulling the free valuation back along the map. -/
@[simp] theorem Formula.evalOn_rename {P : Type} {n m : Nat} (p : Formula α n)
    (ρ : Fin n → Fin m) (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin m → P → Bool) :
    (p.rename ρ).EvalOn label child v ↔ p.EvalOn label child (fun i => v (ρ i)) := by
  induction p generalizing m with
  | atom a => cases a <;> rfl
  | neg p ih => exact not_congr (ih _ _)
  | conj p q hp hq => exact and_congr (hp _ _) (hq _ _)
  | existsSet p ih =>
    simp only [Formula.rename, Formula.EvalOn]
    apply exists_congr
    intro w
    rw [ih, cons_rename]
  | existsFirst p ih =>
    simp only [Formula.rename, Formula.EvalOn]
    apply exists_congr
    intro w
    rw [ih, cons_rename]

@[simp] theorem Formula.evalAt_rename {n m : Nat} (p : Formula α n)
    (ρ : Fin n → Fin m) (t : BinaryTree α) (v : Fin m → Position t → Bool) :
    (p.rename ρ).EvalAt t v ↔ p.EvalAt t (fun i => v (ρ i)) :=
  p.evalOn_rename ρ Position.label (fun d p q => Child d p q) v

/-- A first-order binder can be evaluated by an actual domain element. -/
theorem Formula.evalOn_existsFirst {P : Type} [DecidableEq P] {n : Nat}
    (p : Formula α (n+1)) (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin n → P → Bool) :
    (Formula.existsFirst p).EvalOn label child v ↔
      ∃ x : P, p.EvalOn label child (Fin.cons (fun y => decide (y = x)) v) := by
  constructor
  · rintro ⟨w, ⟨x, hx, huniq⟩, h⟩
    have hw : w = fun y => decide (y = x) := by
      funext y
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · exact huniq y
      · intro hy; simpa only [hy] using hx
    exact ⟨x, hw ▸ h⟩
  · rintro ⟨x, h⟩
    exact ⟨fun y => decide (y = x), ⟨x, by simp, by simp⟩, h⟩

#print axioms Formula.evalAt_iff_posHolds
#print axioms Formula.evalOn_rename
#print axioms Formula.evalOn_existsFirst

end StackSorting.TreeAutomaton.Logic
