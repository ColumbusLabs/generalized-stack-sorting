import OwnerParameterMerge

namespace StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
variable {ι α : Type} {β : ι → Type}

/-- Union of a fixed local parameter tuple along actual disjoint embeddings.
Auxiliary ambient elements, including old outer nodes and crossing edges,
receive no local membership. -/
def union (embed : (Sigma β) → α) (parameters : ∀ i, Fin d → β i → Prop) :
    Fin d → α → Prop := fun j z => ∃ u, embed u=z ∧ merge parameters j u

@[simp] theorem union_restrict (embed : (Sigma β) → α) (hi : Function.Injective embed)
    (parameters : ∀ i, Fin d → β i → Prop) (i : ι) (j : Fin d) (v : β i) :
    union embed parameters j (embed ⟨i,v⟩) ↔ parameters i j v := by
  constructor
  · rintro ⟨u,hu,hp⟩
    have he := hi hu
    subst u
    exact hp
  · intro hp
    exact ⟨⟨i,v⟩,rfl,hp⟩

theorem union_supported (embed : (Sigma β) → α)
    (parameters : ∀ i, Fin d → β i → Prop) {j : Fin d} {z : α}
    (hz : union embed parameters j z) : ∃ u, embed u=z := by
  obtain ⟨u,hu,_⟩ := hz
  exact ⟨u,hu⟩

theorem outside_union (embed : (Sigma β) → α)
    (parameters : ∀ i, Fin d → β i → Prop) (z : α)
    (hz : ∀ u, embed u≠z) (j : Fin d) : ¬union embed parameters j z := by
  rintro ⟨u,hu,_⟩
  exact hz u hu

/-- Disjoint ownership and fiberwise injectivity imply global injectivity. -/
theorem family_injective (embed : ∀ i, β i → α) (owner : α → ι → Prop)
    (owned : ∀ i v, owner (embed i v) i)
    (unique : ∀ z i j, owner z i → owner z j → i=j)
    (hi : ∀ i, Function.Injective (embed i)) :
    Function.Injective (fun u : Sigma β => embed u.1 u.2) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ he
  have hij := unique (embed i u) i j (owned i u) (by simpa only [he] using owned j v)
  subst j
  have huv := hi i he
  change u=v at huv
  subst v
  rfl

#print axioms union_restrict
#print axioms family_injective
end StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
