import NestedFlattenedRunning
import NestedFlatteningSyntax

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.CarrierSemantics
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

abbrev Carrier (N : NestedInput D) := Fin n ⊕ (Fin t ⊕ N.substitution.Node)
def vertex (N : NestedInput D) (v : Fin n) : Carrier N := Sum.inl v
def outer (N : NestedInput D) (x : Fin t) : Carrier N := Sum.inr (Sum.inl x)
def localNode (N : NestedInput D) (a : N.substitution.Node) : Carrier N := Sum.inr (Sum.inr a)

def relations (N : NestedInput D) : Syntax.Relations (Carrier N) where
  original a := match a with | .inl _ => True | _ => False
  localNode a := match a with | .inr (.inr _) => True | _ => False
  localRoot a := match a with | .inr (.inr a) => a.2.val=0 | _ => False
  owner a x := match a,x with | .inr (.inr a),.inr (.inl x) => a.1=x | _,_ => False
  margin x v := match x,v with | .inr (.inl x),.inl v => introductionNode D v=x | _,_ => False
  adhesion x v := match x,v with | .inr (.inl x),.inl v => outerAdhesion D x v | _,_ => False
  outerParent x y := match x,y with
    | .inr (.inl x),.inr (.inl y) => x.val≠0 ∧ T.parent x=y
    | _,_ => False
  localParent a b := match a,b with
    | .inr (.inr a),.inr (.inr b) => a.2.val≠0 ∧ b=⟨a.1,(N.localTree a.1).parent a.2⟩
    | _,_ => False
  localBag a v := match a,v with
    | .inr (.inr a),.inl v => ∃ u, u∈(N.localDecomp a.1).bag a.2 ∧ (N.names a.1 u).val=v
    | _,_ => False
  originalEdge u v := match u,v with | .inl u,.inl v => G.Adj u v | _,_ => False

@[simp] theorem owner_local_iff (N : NestedInput D) (a : N.substitution.Node) (q : Carrier N) :
    (relations N).owner (localNode N a) q ↔ q=outer N a.1 := by
  rcases q with v | (x | b) <;> simp [relations,localNode,outer,eq_comm]

@[simp] theorem localParent_iff (N : NestedInput D) (a : N.substitution.Node) (q : Carrier N) :
    (relations N).localParent (localNode N a) q ↔
      a.2.val≠0 ∧ q=localNode N ⟨a.1,(N.localTree a.1).parent a.2⟩ := by
  rcases q with v | (x | b) <;> simp [relations,localNode]

@[simp] theorem interface_iff (N : NestedInput D) (x : Fin t) (hx : x.val≠0) (v : Fin n) :
    Syntax.Interface (relations N) (outer N x) (vertex N v) ↔
      outerAdhesion D x v ∧ introductionNode D v=T.parent x := by
  simp [Syntax.Interface,relations,outer,vertex,Sum.exists,hx]

/-- Literal clique coverage agrees with actual local decomposition coverage
on the unchanged original vertices. Wrong-sort elements cannot satisfy the
interface's original-vertex endpoint guard. -/
theorem covers_local_iff (N : NestedInput D) (x : Fin t) (hx : x.val≠0)
    (j : Fin (N.nodes (T.parent x))) :
    Syntax.Covers (relations N) (outer N x) (localNode N ⟨T.parent x,j⟩) ↔
      Covers (N.localDecomp (T.parent x)) (N.interface x) j := by
  constructor
  · intro h u hu
    have hi : Syntax.Interface (relations N) (outer N x)
        (vertex N (N.names (T.parent x) u).val) :=
      (interface_iff N x hx _).mpr ⟨(N.mem_interface x u).mp hu,(N.names _ u).property⟩
    obtain ⟨w,hw,he⟩ := h _ hi
    have hwu : w=u := (N.names (T.parent x)).injective (Subtype.ext he)
    simpa only [hwu] using hw
  · intro h q hq
    rcases q with v | (y | a)
    · have hi := (interface_iff N x hx v).mp hq
      let u := (N.names (T.parent x)).symm ⟨v,hi.2⟩
      have hu : u∈N.interface x := by
        apply (N.mem_interface x u).mpr
        simpa only [u,Equiv.apply_symm_apply] using hi.1
      exact ⟨u,h u hu,by simp only [u,Equiv.apply_symm_apply]⟩
    · exact hq.1.elim
    · exact hq.1.elim

/-- The literal parent-noncoverage test selects exactly the root-nearest
covering local bag supplied by the genuine clique theorem. -/
theorem nearest_local_iff (N : NestedInput D) (x : Fin t) (hx : x.val≠0)
    (j : Fin (N.nodes (T.parent x))) :
    Syntax.Nearest (relations N) (outer N x) (localNode N ⟨T.parent x,j⟩) ↔
      RootNearest (N.localDecomp (T.parent x)) (N.interface x) j := by
  classical
  have hp : (∀ q, (relations N).localParent (localNode N ⟨T.parent x,j⟩) q →
      ¬ Syntax.Covers (relations N) (outer N x) q) ↔
      (j.val≠0 → ¬ Syntax.Covers (relations N) (outer N x)
        (localNode N ⟨T.parent x,(N.localTree (T.parent x)).parent j⟩)) := by
    constructor
    · intro h hj
      exact h _ ((localParent_iff N _ _).mpr ⟨hj,rfl⟩)
    · intro h q hq
      obtain ⟨hj,rfl⟩ := (localParent_iff N _ _).mp hq
      exact h hj
  rw [rootNearest_iff_parent_not_cover (N.localDecomp (T.parent x)) (N.interface x)
    (N.interface_nonempty x hx) (N.interface_clique x hx) j]
  unfold Syntax.Nearest
  rw [hp,covers_local_iff N x hx,covers_local_iff N x hx]
  change (Covers _ _ _ ∧ (j.val=0 ∨ (j.val≠0 → ¬ Covers _ _ _))) ↔ _
  tauto

#print axioms covers_local_iff
#print axioms nearest_local_iff
end StackSorting.GraphWidth.Nested.CarrierSemantics
