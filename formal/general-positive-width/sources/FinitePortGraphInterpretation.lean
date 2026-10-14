import SparseTreeCompiler
import FiniteTreeMSOAlgebraicity

/-! Same-node finite-port interpretation. This file closes the logical bridge,
not the canonical encoding/counting bridge. A port route is explicit finite
MSO syntax on two endpoint singleton variables. It can itself contain arbitrary
first- or second-order quantifiers. No semantic oracle is a field. -/
namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic
open scoped RatFunc

variable {α : Type}

/-- Finite disjunction built from negation and conjunction, including the
empty disjunction. -/
def disjoin {n : Nat} : List (Formula α n) → Formula α n
  | [] => .neg truth
  | p :: ps => .neg (.conj (.neg p) (.neg (disjoin ps)))

theorem eval_disjoin {P : Type} {n : Nat} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin n → P → Bool)
    (ps : List (Formula α n)) :
    (disjoin ps).EvalOn label child v ↔ ∃ p ∈ ps, p.EvalOn label child v := by
  classical
  induction ps with
  | nil => simp [disjoin, Formula.EvalOn, eval_truth]
  | cons p ps ih =>
    simp only [disjoin, Formula.EvalOn, List.mem_cons, exists_eq_or_imp, ih]
    simp only [not_and_or, not_not]

/-- A finite alphabet supplies vertex colors, and a finite port index supplies
explicit two-endpoint route formulas. S and M choose finite sets of those routes.
There is exactly one vertex per internal position, rather than one per port. -/
structure FinitePortDecoder (α : Type) where
  portCount : Nat
  insertLabels : Finset α
  removeLabels : Finset α
  route : Fin portCount → Formula α 2
  successorPorts : Finset (Fin portCount)
  matchingPorts : Finset (Fin portCount)

noncomputable def FinitePortDecoder.codes (D : FinitePortDecoder α) : Codes α where
  insert := disjoin (D.insertLabels.toList.map (fun a => .atom (.label 0 a)))
  remove := disjoin (D.removeLabels.toList.map (fun a => .atom (.label 0 a)))
  successor := disjoin (D.successorPorts.toList.map D.route)
  matching := disjoin (D.matchingPorts.toList.map D.route)

theorem FinitePortDecoder.insert_iff {P : Type} (D : FinitePortDecoder α)
    (label : P → α) (child : Bool → P → P → Prop) (p : P) :
    (D.codes.relations label child).insert p ↔ label p ∈ D.insertLabels := by
  classical
  simp [codes, Codes.relations, eval_disjoin, Formula.EvalOn, Atom.EvalOn,
    unaryVal, point]

theorem FinitePortDecoder.remove_iff {P : Type} (D : FinitePortDecoder α)
    (label : P → α) (child : Bool → P → P → Prop) (p : P) :
    (D.codes.relations label child).remove p ↔ label p ∈ D.removeLabels := by
  classical
  simp [codes, Codes.relations, eval_disjoin, Formula.EvalOn, Atom.EvalOn,
    unaryVal, point]

theorem FinitePortDecoder.successor_iff {P : Type} (D : FinitePortDecoder α)
    (label : P → α) (child : Bool → P → P → Prop) (p q : P) :
    (D.codes.relations label child).successor p q ↔
      ∃ port ∈ D.successorPorts, (D.route port).EvalOn label child (binaryVal p q) := by
  simp [codes, Codes.relations, eval_disjoin]

theorem FinitePortDecoder.matching_iff {P : Type} (D : FinitePortDecoder α)
    (label : P → α) (child : Bool → P → P → Prop) (p q : P) :
    (D.codes.relations label child).matching p q ↔
      ∃ port ∈ D.matchingPorts, (D.route port).EvalOn label child (binaryVal p q) := by
  simp [codes, Codes.relations, eval_disjoin]

/-- Literal direct interpretation of the tree as a sparse graph carrier. -/
noncomputable def FinitePortDecoder.relations (D : FinitePortDecoder α)
    (t : BinaryTree α) : SparseEndpointMSO.Relations (Position t) :=
  D.codes.relations Position.label (fun d p q => Child d p q)

/-- A supplied graph is decoded by this tree precisely when its actual domain
is bijective with tree positions and all four original predicates agree there.
This is not an assertion that an encoding exists or is canonical. -/
abbrev SameNodeDecoding (D : FinitePortDecoder α) (G : SparseEndpointMSO.Model)
    (t : BinaryTree α) := SparseEndpointMSO.DomainInterpretation G (D.relations t)

noncomputable def sentence (D : FinitePortDecoder α)
    (f : SparseEndpointMSO.Formula 0 0) : Formula α 0 :=
  compile D.codes f Fin.elim0 Fin.elim0

theorem sentence_evalAt (D : FinitePortDecoder α)
    (f : SparseEndpointMSO.Formula 0 0) (t : BinaryTree α) :
    (sentence D f).EvalAt t Fin.elim0 ↔
      f.EvalOn (D.relations t) Fin.elim0 Fin.elim0 := by
  apply compile_correct Position.label (fun d p q => Child d p q)
  exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩

/-- Main semantic bridge: the full original sparse sentence is translated,
including block first-order and monadic quantifiers, into the accepted tree
syntax and its actual internal-position semantics. -/
theorem sameNode_semantic_preservation [DecidableEq α] (D : FinitePortDecoder α)
    (G : SparseEndpointMSO.Model) (t : BinaryTree α) (J : SameNodeDecoding D G t)
    (f : SparseEndpointMSO.Formula 0 0) :
    SparseEndpointMSO.Satisfies G f ↔
      (sentence D f).PosHolds (markTree t Fin.elim0) := by
  exact J.satisfies f |>.trans ((sentence_evalAt D f t).symm.trans
    ((sentence D f).evalAt_iff_posHolds t Fin.elim0))

/-- The language counts decoded trees, which may represent repeated graphs.
No graph-count equality is asserted. -/
noncomputable def decodedLanguage (D : FinitePortDecoder α)
    (f : SparseEndpointMSO.Formula 0 0) : Set (BinaryTree α) :=
  {t | f.EvalOn (D.relations t) Fin.elim0 Fin.elim0}

theorem decoded_recognizable [Fintype α] [DecidableEq α]
    (D : FinitePortDecoder α) (f : SparseEndpointMSO.Formula 0 0) :
    Recognizable (decodedLanguage D f) := by
  have he : decodedLanguage D f = {t | (sentence D f).EvalAt t Fin.elim0} := by
    ext t
    exact (sentence_evalAt D f t).symm
  rw [he]
  exact (sentence D f).evalAt_recognizable

/-- The accepted finite automaton construction applies to the translated
sentence; accepting states are a literal finite set. -/
theorem decoded_finite_acceptor [Fintype α] [DecidableEq α]
    (D : FinitePortDecoder α) (f : SparseEndpointMSO.Formula 0 0) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : Automaton α Q) (F : Finset Q),
      ∀ t, A.run t ∈ F ↔ f.EvalOn (D.relations t) Fin.elim0 Fin.elim0 := by
  classical
  obtain ⟨Q, hQ, A, F, hA⟩ := decoded_recognizable D f
  let _ := hQ
  refine ⟨Q, hQ, inferInstance, A, Finset.univ.filter (fun q => q ∈ F), ?_⟩
  intro t
  simpa [decodedLanguage] using (hA t).symm

/-- Algebraicity concerns literal distinct labelled trees by internal-node
size. Graph enumeration additionally needs a count-preserving canonical code. -/
theorem decoded_tree_series_algebraic [Fintype α] [DecidableEq α]
    (D : FinitePortDecoder α) (f : SparseEndpointMSO.Formula 0 0) :
    IsAlgebraic (RatFunc ℚ) (GeneralAlgebraicity.includePowerSeries ℚ
      (languageSeries (decodedLanguage D f))) :=
  (decoded_recognizable D f).languageSeries_algebraic

#print axioms sameNode_semantic_preservation
#print axioms decoded_finite_acceptor
#print axioms decoded_tree_series_algebraic
end StackSorting.SparseTreeCompiler
