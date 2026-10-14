import CliqueRootBag
import SubstitutedParentTree

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- The original adhesion, expressed using the already proved introduction
node. Running intersection later identifies this with the parent-bag overlap. -/
def outerAdhesion (D : Decomposition G T) (x : Fin t) (v : Fin n) : Prop :=
  v ∈ D.bag x ∧ introductionNode D v ≠ x

/-- Actual marginal adjacency: original edges plus child-adhesion cliques,
restricted to the vertices introduced at this outer node. -/
def marginalGraph (D : Decomposition G T) (x : Fin t) {q : Nat}
    (names : Fin q ≃ {v : Fin n // introductionNode D v=x}) : Graph q where
  Adj u v := u≠v ∧ (G.Adj (names u).val (names v).val ∨
    ∃ y, y.val≠0 ∧ T.parent y=x ∧
      outerAdhesion D y (names u).val ∧ outerAdhesion D y (names v).val)
  symm := by
    intro u v h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with he | ⟨y,hy,hp,hu,hv⟩
    · exact Or.inl (G.symm he)
    · exact Or.inr ⟨y,hy,hp,hv,hu⟩
  loopless _ h := h.1 rfl

/-- The actual sane outer decomposition and actual local decompositions
needed by combinatorial flattening. No attachment node or global flattened
decomposition is supplied. `connector` is the explicit sane parent-margin
intersection law, to be derived by the outer-construction owner. -/
structure NestedInput (D : Decomposition G T) where
  outerNonempty : 0<t
  vertices : Fin t → Nat
  names : ∀ x, Fin (vertices x) ≃ {v : Fin n // introductionNode D v=x}
  marginNonempty : ∀ x, ∃ v, introductionNode D v=x
  nodes : Fin t → Nat
  localTree : ∀ x, RootedTree (nodes x)
  localDecomp : ∀ x, Decomposition (marginalGraph D x (names x)) (localTree x)
  connector : ∀ x, x.val≠0 →
    ∃ v, introductionNode D v=T.parent x ∧ outerAdhesion D x v

namespace NestedInput
variable {D : Decomposition G T} (N : NestedInput D)

noncomputable def interface (x : Fin t) : Finset (Fin (N.vertices (T.parent x))) := by
  classical
  exact Finset.univ.filter (fun v => outerAdhesion D x ((N.names (T.parent x)) v).val)

@[simp] theorem mem_interface (x : Fin t) (v : Fin (N.vertices (T.parent x))) :
    v ∈ N.interface x ↔ outerAdhesion D x ((N.names (T.parent x)) v).val := by
  classical
  simp [interface]

theorem interface_nonempty (x : Fin t) (hx : x.val≠0) : (N.interface x).Nonempty := by
  obtain ⟨v,hv,ha⟩ := N.connector x hx
  let u := (N.names (T.parent x)).symm ⟨v,hv⟩
  refine ⟨u,(N.mem_interface x u).mpr ?_⟩
  simpa only [u,Equiv.apply_symm_apply] using ha

theorem interface_clique (x : Fin t) (hx : x.val≠0) :
    Clique (marginalGraph D (T.parent x) (N.names (T.parent x))) (N.interface x) := by
  intro u hu v hv hne
  exact ⟨hne,Or.inr ⟨x,hx,rfl,(N.mem_interface x u).mp hu,(N.mem_interface x v).mp hv⟩⟩

theorem local_nonempty (x : Fin t) : 0<N.nodes x := by
  obtain ⟨v,hv⟩ := N.marginNonempty x
  obtain ⟨i,_⟩ := (N.localDecomp x).vertex ((N.names x).symm ⟨v,hv⟩)
  have := i.isLt
  omega

/-- The exact root-nearest local attachment, chosen from a proved nonempty
connected clique-covering family. At the outer root this unused field is the
root of the parent-indexed local tree. -/
noncomputable def attachment (x : Fin t) : Fin (N.nodes (T.parent x)) := by
  classical
  by_cases hx : x.val=0
  · exact ⟨0,N.local_nonempty _⟩
  · exact Classical.choose (exists_rootNearest (N.localDecomp (T.parent x))
      (N.interface x) (N.interface_nonempty x hx) (N.interface_clique x hx))

theorem attachment_spec (x : Fin t) (hx : x.val≠0) :
    RootNearest (N.localDecomp (T.parent x)) (N.interface x) (N.attachment x) := by
  classical
  simp only [attachment,dite_eq_right hx]
  exact Classical.choose_spec (exists_rootNearest (N.localDecomp (T.parent x))
    (N.interface x) (N.interface_nonempty x hx) (N.interface_clique x hx))

noncomputable def substitution : TreeSubstitution T where
  outerNonempty := N.outerNonempty
  size := N.nodes
  positive := N.local_nonempty
  localTree := N.localTree
  attachment := N.attachment

#print axioms interface_clique
#print axioms attachment_spec
end NestedInput
end StackSorting.GraphWidth.Nested
