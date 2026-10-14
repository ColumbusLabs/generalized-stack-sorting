import MultiMarginCompletionCodes
import SparseParametricComposition
import SparseParametricCompatibility

namespace StackSorting.CapturedLinkExtraction.MultiMargin
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth GraphWidth.Nested
namespace CompletionIncidence

abbrev Tag (k : Nat) := Unit ⊕ (Fin k × Fin k)
abbrev count (k : Nat) := Fintype.card (Tag k)
noncomputable def tagEquiv (k : Nat) : Tag k ≃ Fin (count k) := Fintype.equivFin _

theorem count_eq (k : Nat) : count k = 1+k*k := by
  simp [count,Tag]

/-- Exactly one selected unary base predicate per ordered color pair. -/
def domain (I : LinkIndices k b) : Tag k → IFormula 1 b
  | .inl _ => .truth
  | .inr (i,j) => .member 0 (I.candidate i j)

/-- Synthetic incidence is the disjunction of the two rigid root endpoints.
No new binary relation symbol occurs in this formula. -/
def endpoint (I : LinkIndices k b) (i j : Fin k) (u z : Fin a) : IFormula a b :=
  orFormula (rootFormula (I.color i 0) (I.color i 1) (I.color i 2) z u)
    (rootFormula (I.color j 0) (I.color j 1) (I.color j 2) z u)

inductive Atom : Nat → Type where
  | vertex : Atom 1
  | edge : Atom 1
  | originalEdge : Atom 1
  | extraEdge : Atom 1
  | incidence : Atom 2
  | originalIncidence : Atom 2
  | insert : Atom 1
  | remove : Atom 1

def atom (I : LinkIndices k b) : {r : Nat} → Atom r →
    (Fin r → Tag k) → IFormula r b
  | _, .vertex, tags => match tags 0 with
    | .inl _ => vertexFormula 0
    | .inr _ => .neg .truth
  | _, .edge, tags => match tags 0 with
    | .inl _ => edgeFormula 0
    | .inr _ => .truth
  | _, .originalEdge, tags => match tags 0 with
    | .inl _ => edgeFormula 0
    | .inr _ => .neg .truth
  | _, .extraEdge, tags => match tags 0 with
    | .inl _ => .neg .truth
    | .inr _ => .truth
  | _, .originalIncidence, tags => match tags 0, tags 1 with
    | .inl _, .inl _ => incidentFormula 0 1
    | _, _ => .neg .truth
  | _, .insert, tags => match tags 0 with
    | .inl _ => .atom .insert (fun _ => 0)
    | .inr _ => .neg .truth
  | _, .remove, tags => match tags 0 with
    | .inl _ => .atom .remove (fun _ => 0)
    | .inr _ => .neg .truth
  | _, .incidence, tags => match tags 0, tags 1 with
    | .inl _, .inl _ => incidentFormula 0 1
    | .inl _, .inr (i,j) => endpoint I i j 0 1
    | .inr _, _ => .neg .truth

noncomputable def copies (k : Nat) :
    Parametric.CopyInterpretation IncidenceAtom Atom (count k) (parameterCount k) where
  domain t := domain (fixedIndices k) ((tagEquiv k).symm t)
  atom A tags := atom (fixedIndices k) A (fun i => (tagEquiv k).symm (tags i))

/-- Literal original I/R/S/M syntax, using the independently checked
capture-avoiding compiler. Both original and synthetic codes retain the
physical incidence-domain guard from the three-copy first stage. -/
noncomputable def interpretation (k : Nat) :
    Parametric.Interpretation Atom (count k * 3) (0 + parameterCount k * 3) :=
  Parametric.compose (Parametric.ofPlain IncidenceOwnership.interpretation) (copies k)

theorem copy_count (k : Nat) : count k * 3 = completionCopyCount k := by
  rw [count_eq]
  simp only [completionCopyCount,Nat.add_mul,Nat.one_mul]
  rw [Nat.mul_comm (k*k) 3,Nat.mul_assoc]

theorem parameter_count (k : Nat) : 0+parameterCount k*3 = (k*3+k*k+2)*3 := by
  rw [parameterCount_eq]
  omega

variable {D : Model} {n t k : Nat} {G : Graph n} {T : FinitePort.RootedTree t}
variable (dec : Decomposition G T) (names : Fin n ≃ Vertex D) (C : Colors D k)
variable (hcap : Captured dec names C)

abbrev Actual := IncidenceOwnership.Element D ⊕ ExtraEdge dec

def sets : Fin (parameterCount k) → IncSet D :=
  chosenSets C { original := fun _ => False
                 candidate := chosenCandidateSets names C hcap
                 roots := fun _ => False }

@[simp] theorem sets_candidate (i j : Fin k) :
    sets dec names C hcap ((fixedIndices k).candidate i j) =
      chosenCandidateSets names C hcap i j := by
  exact chosenSets_candidate _ _ _ _

@[simp] theorem sets_color (i : Fin k) (j : Fin 3) :
    sets dec names C hcap ((fixedIndices k).color i j) =
      Fin.cases (C i).vertices (Fin.cases (C i).edges (fun _ => (C i).roots)) j := by
  exact chosenSets_color _ _ _ _

abbrev Step := Parametric.StepElement (copies k) AtomEval (sets dec names C hcap)

noncomputable def encode : Actual (D := D) dec → Step dec names C hcap
  | .inl x => ⟨(tagEquiv k (.inl ()), x), by
      simp only [copies,Equiv.symm_apply_apply,domain,ActualEval]⟩
  | .inr e =>
    let q := chosenCandidate names C hcap e
    ⟨(tagEquiv k (.inr (q.1,q.2.1)), q.2.2), by
      simp only [copies,Equiv.symm_apply_apply,domain,ActualEval,sets_candidate]
      exact ⟨e,rfl⟩⟩

/-- Original incidence objects and actual extra edges have distinct tags;
synthetic duplicate elimination is supplied by root rigidity, not a quotient. -/
theorem encode_injective (hc : C.Valid) : Function.Injective (encode dec names C hcap) := by
  intro x y h
  have hp := congrArg Subtype.val h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (congrArg Prod.snd hp)
    | inr e =>
      have hh := (tagEquiv k).injective (congrArg Prod.fst hp)
      cases hh
  | inr e =>
    cases y with
    | inl y =>
      have hh := (tagEquiv k).injective (congrArg Prod.fst hp)
      cases hh
    | inr f =>
      apply congrArg Sum.inr
      apply chosenCandidate_injective names C hc hcap
      have ht := Sum.inr.inj ((tagEquiv k).injective (congrArg Prod.fst hp))
      exact Prod.ext (congrArg (fun p : Fin k × Fin k => p.1) ht)
        (Prod.ext (congrArg (fun p : Fin k × Fin k => p.2) ht)
          (congrArg (fun p : Fin (count k) × IncidenceOwnership.Element D => p.2) hp))

theorem encode_surjective : Function.Surjective (encode dec names C hcap) := by
  rintro ⟨⟨tag,x⟩,hx⟩
  obtain ⟨tag,rfl⟩ := (tagEquiv k).surjective tag
  cases tag with
  | inl z =>
    cases z
    exact ⟨.inl x,rfl⟩
  | inr ij =>
    rcases ij with ⟨i,j⟩
    change ActualEval AtomEval (domain (fixedIndices k) ((tagEquiv k).symm
      (tagEquiv k (.inr (i,j))))) (fun _ => x) (sets dec names C hcap) at hx
    simp only [Equiv.symm_apply_apply,domain,ActualEval,sets_candidate] at hx
    obtain ⟨e,he⟩ := hx
    refine ⟨.inr e,?_⟩
    apply Subtype.ext
    change (tagEquiv k (.inr ((chosenCandidate names C hcap e).1,
      (chosenCandidate names C hcap e).2.1)),(chosenCandidate names C hcap e).2.2) = _
    rw [he]

noncomputable def codeEquiv (hc : C.Valid) : Actual (D := D) dec ≃ Step dec names C hcap :=
  Equiv.ofBijective (encode dec names C hcap)
    ⟨encode_injective dec names C hcap hc,encode_surjective dec names C hcap⟩

#print axioms encode_injective
#print axioms encode_surjective
#print axioms codeEquiv
#print axioms copy_count
end CompletionIncidence
end StackSorting.CapturedLinkExtraction.MultiMargin
