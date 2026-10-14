import MarginalIncidenceSyntax
import SparseIncidenceOwnership

namespace StackSorting.GraphWidth.MarginalA2
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric FinitePort Nested
namespace Carrier
variable {A : Model} {n t W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A) (C : AdhesionColoring D W)

/-- Exact C.2 output carrier, retaining original incidence and actual nodes. -/
abbrev Base (A : Model) (t : Nat) := IncidenceOwnership.Element A ⊕ Fin t
abbrev Actual := Base A t ⊕ ExtraEdge D

def parameter : Syntax.Parameter W → Base A t → Prop
  | .inl i, .inl (.inl v) => C.color (names.symm v)=i
  | .inl _, _ => False
  | .inr (i,j), .inr y => selected D C i j y
  | .inr _, .inl _ => False

noncomputable def sets : Fin (Syntax.parameters W) → Base A t → Prop :=
  fun i => parameter D names C ((Syntax.parameterEquiv W).symm i)

@[simp] theorem sets_color (i : Fin W) (z : Base A t) :
    sets D names C ((Syntax.fixed W).color i) z=parameter D names C (.inl i) z := by
  simp only [sets,Syntax.fixed,Equiv.symm_apply_apply]

@[simp] theorem sets_selected (i j : Fin W) (z : Base A t) :
    sets D names C ((Syntax.fixed W).selected i j) z=parameter D names C (.inr (i,j)) z := by
  simp only [sets,Syntax.fixed,Equiv.symm_apply_apply]

variable (ats : {r : Nat} → Syntax.InputAtom r → (Fin r → Base A t) → Prop)
abbrev Step := StepElement (Syntax.interpretation W) ats (sets D names C)

/-- Actual vertices, original edge IDs, and outer nodes retain the same base
object at one fixed tag. Only selected actual missing pairs add elements. -/
noncomputable def encode : Actual (A := A) D → Step D names C ats
  | .inl z => ⟨(Syntax.tagEquiv W (.inl ()),z),by
      simp only [Syntax.interpretation,Equiv.symm_apply_apply,Syntax.domain,ActualEval]⟩
  | .inr e =>
    let q := chosenCandidate D C e
    ⟨(Syntax.tagEquiv W (.inr (q.1,q.2.1)),.inr q.2.2),by
      simp only [Syntax.interpretation,Equiv.symm_apply_apply,Syntax.domain,ActualEval,sets_selected,parameter]
      exact ⟨e,rfl⟩⟩

/-- In particular no graph vertex is copied once per outer bag. -/
theorem vertex_code (u : Fin n) :
    (encode D names C ats (.inl (.inl (.inl (names u))))).val =
      (Syntax.tagEquiv W (.inl ()),.inl (.inl (names u))) := rfl

theorem encode_injective : Function.Injective (encode D names C ats) := by
  intro x y h
  have hp := congrArg Subtype.val h
  cases x with
  | inl x => cases y with
    | inl y => exact congrArg Sum.inl (congrArg Prod.snd hp)
    | inr e =>
      have hh := (Syntax.tagEquiv W).injective (congrArg Prod.fst hp)
      cases hh
  | inr e => cases y with
    | inl y =>
      have hh := (Syntax.tagEquiv W).injective (congrArg Prod.fst hp)
      cases hh
    | inr f =>
      apply congrArg Sum.inr
      apply chosenCandidate_injective D C
      have ht := Sum.inr.inj ((Syntax.tagEquiv W).injective (congrArg Prod.fst hp))
      have hn := Sum.inr.inj (congrArg Prod.snd hp)
      exact Prod.ext (congrArg (fun p : Fin W × Fin W => p.1) ht)
        (Prod.ext (congrArg (fun p : Fin W × Fin W => p.2) ht) hn)

theorem encode_surjective : Function.Surjective (encode D names C ats) := by
  rintro ⟨⟨tag,z⟩,hz⟩
  obtain ⟨tag,rfl⟩ := (Syntax.tagEquiv W).surjective tag
  cases tag with
  | inl q => cases q; exact ⟨.inl z,rfl⟩
  | inr ij =>
    rcases ij with ⟨i,j⟩
    change ActualEval ats (Syntax.domain (Syntax.fixed W)
      ((Syntax.tagEquiv W).symm (Syntax.tagEquiv W (.inr (i,j))))) (fun _ => z) (sets D names C) at hz
    simp only [Equiv.symm_apply_apply,Syntax.domain,ActualEval,sets_selected] at hz
    cases z with
    | inl a => exact hz.elim
    | inr y =>
      obtain ⟨e,he⟩ := hz
      refine ⟨.inr e,?_⟩
      apply Subtype.ext
      change (Syntax.tagEquiv W (.inr ((chosenCandidate D C e).1,(chosenCandidate D C e).2.1)),
        Sum.inr (chosenCandidate D C e).2.2)=_
      rw [he]

noncomputable def codeEquiv : Actual (A := A) D ≃ Step D names C ats :=
  Equiv.ofBijective (encode D names C ats)
    ⟨encode_injective D names C ats,encode_surjective D names C ats⟩

/-- Literal code equality, not equality modulo shared endpoints. -/
theorem code_equal_iff (u v : Actual (A := A) D) :
    encode D names C ats u=encode D names C ats v ↔ u=v :=
  (encode_injective D names C ats).eq_iff

#print axioms vertex_code
#print axioms encode_injective
#print axioms encode_surjective
#print axioms codeEquiv
#print axioms code_equal_iff
end Carrier
end StackSorting.GraphWidth.MarginalA2
