import GraphIso
import TorsoGraph

namespace StackSorting.BiInterface
variable {k : ℕ} {V W : Type*} {G : Graph k V} {H : Graph k W}

private theorem sameCode_presence (h : abstraction G = abstraction H) (p : Port k) :
    (∃ v, G.port p = some v) ↔ (∃ w, H.port p = some w) := by
  rw [← abstraction_presence G, ← abstraction_presence H,h]

private theorem sameCode_identity (h : abstraction G = abstraction H) (p q : Port k) :
    (∃ v, G.port p = some v ∧ G.port q = some v) ↔
    (∃ w, H.port p = some w ∧ H.port q = some w) := by
  rw [← abstraction_identity G, ← abstraction_identity H,h]

private theorem matching_boundary_exists (h : abstraction G = abstraction H) (v : G.boundary) :
    ∃ w : H.boundary, ∀ p, G.port p = some v.val → H.port p = some w.val := by
  obtain ⟨p,hp⟩ := v.property
  obtain ⟨w,hw⟩ := (sameCode_presence h p).mp ⟨v.val,hp⟩
  refine ⟨⟨w,⟨p,hw⟩⟩,?_⟩
  intro q hq
  obtain ⟨z,hzp,hzq⟩ := (sameCode_identity h p q).mp ⟨v.val,hp,hq⟩
  have he : z = w := Option.some.inj (hzp.symm.trans hw)
  exact he ▸ hzq

noncomputable def boundaryMatch (h : abstraction G = abstraction H) (v : G.boundary) : H.boundary :=
  Classical.choose (matching_boundary_exists h v)

theorem boundaryMatch_port (h : abstraction G = abstraction H) (v : G.boundary) (p : Port k)
    (hp : G.port p = some v.val) : H.port p = some (boundaryMatch h v).val :=
  Classical.choose_spec (matching_boundary_exists h v) p hp

private theorem boundaryMatch_inverse (h : abstraction G = abstraction H) (v : G.boundary) :
    boundaryMatch h.symm (boundaryMatch h v) = v := by
  obtain ⟨p,hp⟩ := v.property
  apply Subtype.ext
  apply Option.some.inj
  exact (boundaryMatch_port h.symm _ p (boundaryMatch_port h v p hp)).symm.trans hp

noncomputable def codeBoundaryEquiv (h : abstraction G = abstraction H) : G.boundary ≃ H.boundary where
  toFun := boundaryMatch h
  invFun := boundaryMatch h.symm
  left_inv := boundaryMatch_inverse h
  right_inv := boundaryMatch_inverse h.symm

private theorem torsoAdj_iff_code (G : Graph k V) (v w : G.boundary) (p q : Port k)
    (hp : G.port p = some v.val) (hq : G.port q = some w.val) :
    (torso G).Adj v w ↔ (abstraction G).2.2 p q = true := by
  rw [abstraction_edge]
  constructor
  · intro h
    exact ⟨v.val,w.val,hp,hq,fun he => h.1 (Subtype.ext he),h.2⟩
  · rintro ⟨a,b,ha,hb,hne,hpath⟩
    have hea : a = v.val := Option.some.inj (ha.symm.trans hp)
    have heb : b = w.val := Option.some.inj (hb.symm.trans hq)
    subst a b
    exact ⟨fun he => hne (congrArg Subtype.val he),hpath⟩

private theorem codeBoundaryEquiv_port (h : abstraction G = abstraction H) (p : Port k) :
    (boundaryPort G p).map (codeBoundaryEquiv h) = boundaryPort H p := by
  cases hg : boundaryPort G p with
  | none =>
    cases hh : boundaryPort H p with
    | none => rfl
    | some w =>
      obtain ⟨v,hv⟩ := (sameCode_presence h p).mpr
        ⟨w.val,(boundaryPort_eq_some H p w).mp hh⟩
      have hvB : v ∈ G.boundary := ⟨p,hv⟩
      have hsome := (boundaryPort_eq_some G p ⟨v,hvB⟩).mpr hv
      rw [hg] at hsome
      contradiction
  | some v =>
    have hv := (boundaryPort_eq_some G p v).mp hg
    have hh := (boundaryPort_eq_some H p (codeBoundaryEquiv h v)).mpr (boundaryMatch_port h v p hv)
    simp [hh]

/-- Equality of the finite code reconstructs an actual isomorphism of torsos;
identity information in the code makes the vertex correspondence well-defined. -/
noncomputable def torsoIsoOfCode (h : abstraction G = abstraction H) : Iso (torso G) (torso H) where
  vertex := codeBoundaryEquiv h
  adj := by
    intro v w
    obtain ⟨p,hp⟩ := v.property
    obtain ⟨q,hq⟩ := w.property
    change (torso H).Adj (boundaryMatch h v) (boundaryMatch h w) ↔ (torso G).Adj v w
    rw [torsoAdj_iff_code H _ _ p q (boundaryMatch_port h v p hp) (boundaryMatch_port h w q hq),
      torsoAdj_iff_code G v w p q hp hq,h]
  left := fun i => codeBoundaryEquiv_port h (false,i)
  right := fun i => codeBoundaryEquiv_port h (true,i)

#print axioms torsoIsoOfCode
end StackSorting.BiInterface
