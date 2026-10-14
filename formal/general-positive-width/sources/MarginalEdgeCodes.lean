import NestedCliqueAttachment
import SparseParametricComposition

namespace StackSorting.GraphWidth.MarginalA2
open FinitePort Nested
variable {n t W : Nat} {G : Graph n} {T : RootedTree t}

/-- Only inherited adhesions are separated. No outer-bag coloring is assumed. -/
structure AdhesionColoring (D : Decomposition G T) (W : Nat) where
  color : Fin n → Fin W
  separates : ∀ y u v, outerAdhesion D y u → outerAdhesion D y v →
    color u=color v → u=v

/-- Concrete simple marginal adjacency, with the owner recorded explicitly. -/
def MarginalAdj (D : Decomposition G T) (x : Fin t) (u v : Fin n) : Prop :=
  introductionNode D u=x ∧ introductionNode D v=x ∧ u≠v ∧
    (G.Adj u v ∨ ∃ y, y.val≠0 ∧ T.parent y=x ∧
      outerAdhesion D y u ∧ outerAdhesion D y v)

/-- One actual unordered missing edge. Numerical order is used solely to name
an unordered pair in the mathematical carrier, never as an input atom. -/
abbrev ExtraEdge (D : Decomposition G T) :=
  {p : Fin n × Fin n // p.1.val<p.2.val ∧ ¬G.Adj p.1 p.2 ∧
    MarginalAdj D (introductionNode D p.1) p.1 p.2}

abbrev Candidate (t W : Nat) := Fin W × Fin W × Fin t

def CandidateRep (D : Decomposition G T) (C : AdhesionColoring D W)
    (q : Candidate t W) (e : ExtraEdge D) : Prop :=
  q.2.2.val≠0 ∧ T.parent q.2.2=introductionNode D e.val.1 ∧
    outerAdhesion D q.2.2 e.val.1 ∧ outerAdhesion D q.2.2 e.val.2 ∧
    C.color e.val.1=q.1 ∧ C.color e.val.2=q.2.1

/-- Endpoint uniqueness follows from the actual adhesion coloring. -/
theorem candidate_functional (D : Decomposition G T) (C : AdhesionColoring D W)
    {q : Candidate t W} {e f : ExtraEdge D}
    (he : CandidateRep D C q e) (hf : CandidateRep D C q f) : e=f := by
  apply Subtype.ext
  exact Prod.ext
    (C.separates q.2.2 _ _ he.2.2.1 hf.2.2.1 (he.2.2.2.2.1.trans hf.2.2.2.2.1.symm))
    (C.separates q.2.2 _ _ he.2.2.2.1 hf.2.2.2.1 (he.2.2.2.2.2.trans hf.2.2.2.2.2.symm))

theorem extra_has_candidate (D : Decomposition G T) (C : AdhesionColoring D W)
    (e : ExtraEdge D) : ∃ q, CandidateRep D C q e := by
  rcases e.property.2.2.2.2.2 with ho | ⟨y,hy,hp,hu,hv⟩
  · exact (e.property.2.1 ho).elim
  · exact ⟨(C.color e.val.1,C.color e.val.2,y),hy,hp,hu,hv,rfl,rfl⟩

noncomputable def chosenCandidate (D : Decomposition G T) (C : AdhesionColoring D W)
    (e : ExtraEdge D) : Candidate t W := Classical.choose (extra_has_candidate D C e)

theorem chosenCandidate_spec (D : Decomposition G T) (C : AdhesionColoring D W)
    (e : ExtraEdge D) : CandidateRep D C (chosenCandidate D C e) e :=
  Classical.choose_spec (extra_has_candidate D C e)

theorem chosenCandidate_injective (D : Decomposition G T) (C : AdhesionColoring D W) :
    Function.Injective (chosenCandidate D C) := by
  intro e f he
  have hf := chosenCandidate_spec D C f
  rw [←he] at hf
  exact candidate_functional D C (chosenCandidate_spec D C e) hf

/-- Exactly W² sets of actual outer nodes; the choice is an MSO parameter,
not a presumed definable sibling order. -/
def selected (D : Decomposition G T) (C : AdhesionColoring D W)
    (i j : Fin W) (y : Fin t) : Prop := ∃ e, chosenCandidate D C e=(i,j,y)

theorem selected_candidate_exact (D : Decomposition G T) (C : AdhesionColoring D W)
    (q : Candidate t W) (e : ExtraEdge D) :
    chosenCandidate D C e=q ↔ selected D C q.1 q.2.1 q.2.2 ∧ CandidateRep D C q e := by
  constructor
  · intro h
    exact ⟨⟨e,h⟩,h ▸ chosenCandidate_spec D C e⟩
  · rintro ⟨⟨f,hf⟩,he⟩
    have hr := chosenCandidate_spec D C f
    rw [hf] at hr
    exact (candidate_functional D C he hr) ▸ hf

/-- Literal selected-code equality is equivalent to actual edge equality. -/
noncomputable def selectedEquiv (D : Decomposition G T) (C : AdhesionColoring D W) :
    ExtraEdge D ≃ {q : Candidate t W // selected D C q.1 q.2.1 q.2.2} :=
  Equiv.ofBijective (fun e => ⟨chosenCandidate D C e,⟨e,rfl⟩⟩) ⟨
    fun e f h => chosenCandidate_injective D C (congrArg Subtype.val h),
    by rintro ⟨q,e,h⟩; exact ⟨e,Subtype.ext h⟩⟩

theorem candidate_owner (D : Decomposition G T) (C : AdhesionColoring D W)
    {q : Candidate t W} {e : ExtraEdge D} (h : CandidateRep D C q e) :
    T.parent q.2.2=introductionNode D e.val.1 := h.2.1

theorem extra_same_owner (D : Decomposition G T) (e : ExtraEdge D) :
    introductionNode D e.val.2=introductionNode D e.val.1 := e.property.2.2.2.1

theorem extra_not_original (D : Decomposition G T) (e : ExtraEdge D) :
    ¬G.Adj e.val.1 e.val.2 := e.property.2.1

theorem extra_colors_distinct (D : Decomposition G T) (C : AdhesionColoring D W)
    (e : ExtraEdge D) : C.color e.val.1≠C.color e.val.2 := by
  intro he
  have h := chosenCandidate_spec D C e
  have hv := C.separates _ _ _ h.2.2.1 h.2.2.2.1 he
  have hi := congrArg Fin.val hv
  have hlt := e.property.1
  omega

theorem marginalGraph_exact (D : Decomposition G T) (x : Fin t) {q : Nat}
    (names : Fin q ≃ {v : Fin n // introductionNode D v=x}) (u v : Fin q) :
    (marginalGraph D x names).Adj u v ↔ MarginalAdj D x (names u).val (names v).val := by
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨(names u).property,(names v).property,?_,h⟩
    intro he
    exact hne (names.injective (Subtype.ext he))
  · rintro ⟨_,_,hne,h⟩
    refine ⟨?_,h⟩
    intro he
    exact hne (congrArg (fun z => (names z).val) he)

/-- All copy and free-parameter bounds are independent of graph size. The
retained channel contains vertices and original induced edges together. -/
def copyCount (W : Nat) : Nat := 1+W*W
def parameterCount (W : Nat) : Nat := W+W*W

#print axioms candidate_functional
#print axioms selected_candidate_exact
#print axioms selectedEquiv
#print axioms marginalGraph_exact
end StackSorting.GraphWidth.MarginalA2
