import FiniteTreeMSO
import FiniteTreePositionSemantics

namespace StackSorting.TreeAutomaton.Logic
variable {α : Type} [DecidableEq α]

private theorem bool_false_or (b : Bool) (R : Prop) :
    (b = false ∨ R) ↔ (b = true → R) := by cases b <;> simp

/-- Atomic semantics directly in the finite internal-node structure. -/
def Atom.PosHolds {n : Nat} : Atom α n → BinaryTree (Marked α n) → Prop
  | .subset i j, t => ∀ p : Position t, p.label.2 i = true → p.label.2 j = true
  | .label i a, t => ∀ p : Position t, p.label.2 i = true → p.label.1 = a
  | .singleton i, t => ∃! p : Position t, p.label.2 i = true
  | .child d i j, t => ∃ p q : Position t,
      Child d p q ∧ p.label.2 i = true ∧ q.label.2 j = true

theorem Atom.holds_iff_positions {n : Nat} (a : Atom α n)
    (t : BinaryTree (Marked α n)) : a.Holds t ↔ a.PosHolds t := by
  cases a with
  | subset i j => simp [Atom.Holds, Atom.PosHolds, all_iff_positions, bool_false_or]
  | label i a => simp [Atom.Holds, Atom.PosHolds, all_iff_positions, bool_false_or]
  | singleton i => exact count_one_iff_unique_position _ _
  | child d i j => simp [Atom.Holds, Atom.PosHolds, edge_iff_positions]

/-- Internal-position semantics: quantified sets are arbitrary Boolean functions
on the existing positions, and quantified first-order values have exactly one
true position. The same unchanged finite tree supplies every valuation. -/
def Formula.PosHolds : {n : Nat} → Formula α n → BinaryTree (Marked α n) → Prop
  | _, .atom a, t => a.PosHolds t
  | _, .neg p, t => ¬ p.PosHolds t
  | _, .conj p q, t => p.PosHolds t ∧ q.PosHolds t
  | _, .existsSet p, t => ∃ v : Position t → Bool,
      p.PosHolds ((annotate t v).map extend)
  | _, .existsFirst p, t => ∃ v : Position t → Bool,
      (∃! x : Position t, v x = true) ∧ p.PosHolds ((annotate t v).map extend)

omit [DecidableEq α] in
theorem count_extend_annotate {n : Nat} (t : BinaryTree (Marked α n))
    (v : Position t → Bool) :
    count (fun a => a.2 (0 : Fin (n+1))) ((annotate t v).map extend) =
      count Prod.snd (annotate t v) := by
  rw [count_map]
  rfl

/-- Acceptance semantics agrees with quantification on actual internal positions. -/
theorem Formula.holds_iff_positions {n : Nat} (p : Formula α n)
    (t : BinaryTree (Marked α n)) : p.Holds t ↔ p.PosHolds t := by
  induction p with
  | atom a => exact a.holds_iff_positions t
  | neg p hp => exact not_congr (hp _)
  | conj p q hp hq => exact and_congr (hp _) (hq _)
  | @existsSet n p hp =>
    change (∃ u : BinaryTree (Marked α n × Bool), u.map Prod.fst = t ∧ p.Holds (u.map extend)) ↔ _
    rw [exists_lift_iff_positions]
    exact exists_congr fun v => hp _
  | @existsFirst n p hp =>
    change (∃ u : BinaryTree (Marked α n × Bool), u.map Prod.fst = t ∧
      (count (fun a => a.2 (0 : Fin (_+1))) (u.map extend) = 1 ∧ p.Holds (u.map extend))) ↔ _
    rw [exists_lift_iff_positions]
    change (∃ v : Position t → Bool, _ ∧ _) ↔ (∃ v : Position t → Bool, _ ∧ _)
    apply exists_congr
    intro v
    rw [count_extend_annotate, annotate_singleton_iff, hp]

/-- Every atomic label test refers to actual node labels. -/
theorem label_atom_iff_positions {n : Nat} (i : Fin n) (a : α)
    (t : BinaryTree (Marked α n)) :
    (Atom.label i a).Holds t ↔
      ∀ p : Position t, p.label.2 i = true → p.label.1 = a := by
  rw [Atom.Holds, all_iff_positions]
  simp [bool_false_or]

theorem subset_atom_iff_positions {n : Nat} (i j : Fin n)
    (t : BinaryTree (Marked α n)) :
    (Atom.subset i j : Atom α n).Holds t ↔
      ∀ p : Position t, p.label.2 i = true → p.label.2 j = true := by
  rw [Atom.Holds, all_iff_positions]
  simp [bool_false_or]

theorem singleton_atom_iff_positions {n : Nat} (i : Fin n)
    (t : BinaryTree (Marked α n)) :
    (Atom.singleton i : Atom α n).Holds t ↔ ∃! p : Position t, p.label.2 i = true :=
  count_one_iff_unique_position _ _

theorem child_atom_iff_positions {n : Nat} (d : Bool) (i j : Fin n)
    (t : BinaryTree (Marked α n)) :
    (Atom.child d i j : Atom α n).Holds t ↔
      ∃ p q : Position t, Child d p q ∧ p.label.2 i = true ∧ q.label.2 j = true := by
  rw [Atom.Holds, edge_iff_positions]
  simp only [Bool.and_eq_true]

/-- Full finite-state correctness against internal-position semantics. -/
theorem Formula.positions_recognizable [Fintype α] {n : Nat} (p : Formula α n) :
    Recognizable {t | p.PosHolds t} := by
  simpa only [← Formula.holds_iff_positions] using p.recognizable

#print axioms Formula.holds_iff_positions
#print axioms Formula.positions_recognizable
end StackSorting.TreeAutomaton.Logic

namespace StackSorting.TreeAutomaton.Logic
variable {α : Type} [DecidableEq α]

/-- Under singleton first-order encodings, inclusion is ordinary membership. -/
theorem firstOrder_membership {n : Nat} (i j : Fin n)
    (t : BinaryTree (Marked α n)) (x : Position t)
    (hx : ∀ p : Position t, p.label.2 i = true ↔ p = x) :
    (Atom.subset i j : Atom α n).Holds t ↔ x.label.2 j = true := by
  rw [subset_atom_iff_positions]
  constructor
  · intro h
    exact h x ((hx x).mpr rfl)
  · intro h p hp
    have he := (hx p).mp hp
    exact he.symm ▸ h

/-- On two singleton valuations this atom expresses first-order equality. -/
theorem firstOrder_equality {n : Nat} (i j : Fin n)
    (t : BinaryTree (Marked α n)) (x y : Position t)
    (hx : ∀ p : Position t, p.label.2 i = true ↔ p = x)
    (hy : ∀ p : Position t, p.label.2 j = true ↔ p = y) :
    (Atom.subset i j : Atom α n).Holds t ↔ x = y := by
  rw [firstOrder_membership i j t x hx, hy x]

/-- Singleton label predicates are ordinary first-order node-label predicates. -/
theorem firstOrder_label {n : Nat} (i : Fin n) (a : α)
    (t : BinaryTree (Marked α n)) (x : Position t)
    (hx : ∀ p : Position t, p.label.2 i = true ↔ p = x) :
    (Atom.label i a).Holds t ↔ x.label.1 = a := by
  rw [label_atom_iff_positions]
  constructor
  · intro h
    exact h x ((hx x).mpr rfl)
  · intro h p hp
    have he := (hx p).mp hp
    exact he.symm ▸ h

/-- Singleton child predicates are exactly the immediate ordered child relation. -/
theorem firstOrder_child {n : Nat} (d : Bool) (i j : Fin n)
    (t : BinaryTree (Marked α n)) (x y : Position t)
    (hx : ∀ p : Position t, p.label.2 i = true ↔ p = x)
    (hy : ∀ p : Position t, p.label.2 j = true ↔ p = y) :
    (Atom.child d i j : Atom α n).Holds t ↔ Child d x y := by
  rw [child_atom_iff_positions]
  constructor
  · rintro ⟨p, q, h, hp, hq⟩
    have he := (hx p).mp hp
    have hf := (hy q).mp hq
    exact he ▸ hf ▸ h
  · intro h
    exact ⟨x, y, h, (hx x).mpr rfl, (hy y).mpr rfl⟩

/-- Literal finite accepting-set interface for the established counting layer. -/
theorem Formula.exists_finite_acceptor [Fintype α] {n : Nat} (p : Formula α n) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : Automaton (Marked α n) Q) (F : Finset Q),
      ∀ t, A.run t ∈ F ↔ p.PosHolds t := by
  classical
  obtain ⟨Q, hQ, A, F, hA⟩ := p.positions_recognizable
  let _ := hQ
  refine ⟨Q, hQ, inferInstance, A, Finset.univ.filter (fun q => q ∈ F), ?_⟩
  intro t
  simpa using (hA t).symm

#print axioms firstOrder_child
#print axioms Formula.exists_finite_acceptor
end StackSorting.TreeAutomaton.Logic
