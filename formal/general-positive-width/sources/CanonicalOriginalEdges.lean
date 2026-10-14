import OriginalEdgeForgetting

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}

def canonicalEdge : ((Fin n × Fin n) ⊕ Fin n) → ((Fin n × Fin n) ⊕ Fin n)
  | .inl (a,b) => if a ≤ b then .inl (a,b) else .inl (b,a)
  | .inr z => .inr z

theorem canonicalEdge_idempotent (e : (Fin n × Fin n) ⊕ Fin n) :
    canonicalEdge (canonicalEdge e) = canonicalEdge e := by
  cases e with
  | inr z => rfl
  | inl e =>
    rcases e with ⟨a,b⟩
    by_cases h : a ≤ b
    · simp [canonicalEdge,h]
    · have hba : b ≤ a := le_of_not_ge h
      simp [canonicalEdge,h,hba]

theorem prefix_canonical_incidence (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (x : Fin n) (e : (Fin n × Fin n) ⊕ Fin n) :
    PrefixHypertorsoInc G O r Z x (canonicalEdge e) ↔ PrefixHypertorsoInc G O r Z x e := by
  cases e with
  | inr z => rfl
  | inl e =>
    rcases e with ⟨a,b⟩
    by_cases h : a ≤ b
    · simp only [canonicalEdge,ite_eq_left h]
    · simp only [canonicalEdge,ite_eq_right h,PrefixHypertorsoInc]
      constructor
      · rintro ⟨hab,hb,ha,hx⟩
        exact ⟨G.symm hab,ha,hb,hx.symm⟩
      · rintro ⟨hab,ha,hb,hx⟩
        exact ⟨G.symm hab,hb,ha,hx.symm⟩

/-- One identifier per undirected original edge, while each frontier node
retains its own adhesion identifier, including parallel equal adhesions. -/
def CanonicalPrefixInc (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (x : Fin n) (e : (Fin n × Fin n) ⊕ Fin n) : Prop :=
  PrefixHypertorsoInc G O r Z x e ∧ canonicalEdge e = e

noncomputable def canonicalActiveEdge (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (e : ActiveEdge (PrefixHypertorsoInc G O r Z)) :
    ActiveEdge (CanonicalPrefixInc G O r Z) :=
  ⟨canonicalEdge e.val,by
    obtain ⟨x,hx⟩ := e.property
    exact ⟨x,(prefix_canonical_incidence G O r Z x e.val).mpr hx,canonicalEdge_idempotent e.val⟩⟩

theorem canonicalActive_incidence (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (x : Fin n) (e : ActiveEdge (PrefixHypertorsoInc G O r Z)) :
    ActiveIncidence (CanonicalPrefixInc G O r Z) x (canonicalActiveEdge G O r Z e) ↔
      ActiveIncidence (PrefixHypertorsoInc G O r Z) x e := by
  constructor
  · intro h
    exact (prefix_canonical_incidence G O r Z x e.val).mp h.1
  · intro h
    exact ⟨(prefix_canonical_incidence G O r Z x e.val).mpr h,canonicalEdge_idempotent e.val⟩

theorem canonicalActive_surjective (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) : Function.Surjective (canonicalActiveEdge G O r Z) := by
  intro e
  obtain ⟨x,hx,hcan⟩ := e.property
  refine ⟨⟨e.val,⟨x,hx⟩⟩,?_⟩
  exact Subtype.ext hcan

def IsOriginal (e : (Fin n × Fin n) ⊕ Fin n) : Prop := ∃ a b, e = .inl (a,b)

theorem canonical_original_iff (e : (Fin n × Fin n) ⊕ Fin n) :
    IsOriginal (canonicalEdge e) ↔ IsOriginal e := by
  cases e with
  | inr z => simp [canonicalEdge,IsOriginal]
  | inl e =>
    rcases e with ⟨a,b⟩
    by_cases h : a ≤ b <;> simp [canonicalEdge,h,IsOriginal]

theorem canonical_boundary_fiber (e d : (Fin n × Fin n) ⊕ Fin n)
    (h : canonicalEdge e = canonicalEdge d) (hn : ¬ IsOriginal (canonicalEdge e)) : e = d := by
  have he : ¬ IsOriginal e := fun he => hn ((canonical_original_iff e).mpr he)
  have hd : ¬ IsOriginal d := fun hd => hn (h.symm ▸ (canonical_original_iff d).mpr hd)
  cases e with
  | inl e => exact (he ⟨e.1,e.2,rfl⟩).elim
  | inr z =>
    cases d with
    | inl d => exact (hd ⟨d.1,d.2,rfl⟩).elim
    | inr w => exact h

/-- Original orientations are now forgotten in the concrete 5.2 output;
parallel boundary adhesions remain separate, and all bags keep their bounds. -/
theorem exists_canonical_prefix_separation (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r s t : Fin n) (hs : s ∈ regionBagSet G O r) (ht : t ∈ regionBagSet G O r) :
    ∃ Z : Finset (Fin n), RelativePrefix O r Z ∧
      (∃ p q : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t,
        ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → IsOriginal e.val) ∧
      ∃ D : BagPath (Finset.univ : Finset {x : Fin n // x ∈ prefixVertices G O r Z}) (2*k+2),
        D.Covers (SupportedIncidence (inc := ActiveIncidence (CanonicalPrefixInc G O r Z))
          (↑(prefixVertices G O r Z))) := by
  classical
  obtain ⟨Z,hZ,⟨p,q,hpq⟩,D,hD⟩ := exists_prefix_separation G O helim cones k width r s t hs ht
  let f := canonicalActiveEdge G O r Z
  have forward : ∀ x e, ActiveIncidence (PrefixHypertorsoInc G O r Z) x e →
      ActiveIncidence (CanonicalPrefixInc G O r Z) x (f e) :=
    fun x e he => (canonicalActive_incidence G O r Z x e).mpr he
  obtain ⟨a,b,hab⟩ := forget_original_copies f forward (fun e => IsOriginal e.val)
    (fun e => IsOriginal e.val)
    (fun e he => (canonical_original_iff e.val).mpr he)
    (fun e d he hn => Subtype.ext (canonical_boundary_fiber e.val d.val (congrArg Subtype.val he) hn))
    p q hpq
  refine ⟨Z,hZ,⟨a,b,hab⟩,D,?_⟩
  exact covers_original_quotient D hD f (canonicalActive_surjective G O r Z)
    (fun x e => canonicalActive_incidence G O r Z x.val e)

end StackSorting.PrefixGrowth
