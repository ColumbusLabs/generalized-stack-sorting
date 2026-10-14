import PortCodePrefix

namespace StackSorting.FinitePort

/-- Semantic normal-form clauses for a stored code. These are intended to be
proved from bounded finite MSO syntax in a later step; no such syntax theorem
or arbitrary-code canonicity is assumed here. -/
structure PortNormalForm {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (C : Code n colors relations) : Prop where
  color : ∀ v, (C v).color=G.color v
  length : ∀ v, (C v).ports.length=(inherited T O G v).length
  resolved : ∀ v i (_hi : i<(C v).ports.length) (hj : i<(inherited T O G v).length),
    readPort T C n v (i+1)=some ((inherited T O G v)[i])
  bits : ∀ v i e, (C v).ports[i]?=some e → ∀ u,
    readPort T C n v (i+1)=some u → ∀ r forward,
      e.bit r forward = if forward then G.rel r v u else G.rel r u v

theorem PortNormalForm.root_empty {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : PortNormalForm T O G C) (v : Vertex n) (hv : v.val=0) : (C v).ports=[] := by
  apply List.length_eq_zero_iff.mp
  rw [h.length v,inherited_root_empty T O G v hv]
  rfl

/-- The actual encoding satisfies every semantic normal-form clause, including
all inherited entries with zero relation bits. -/
theorem encode_normalForm {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) :
    PortNormalForm T O G (encode T O G) := by
  constructor
  · intro v; rfl
  · intro v; simp only [encode,List.length_map]
  · intro v i _ hj
    apply encoded_port_identity T O G v _ (i+1)
    exact List.getElem?_eq_getElem hj
  · intro v i e he u hr r forward
    have hm : ((inherited T O G v)[i]?).map (entry T O G v)=some e := by
      simpa only [encode,List.getElem?_map] using he
    obtain ⟨w,hw,hwe⟩ := Option.map_eq_some_iff.mp hm
    have hh := encoded_port_identity T O G v w (i+1) hw
    have hwu : w=u := Option.some.inj (hh.symm.trans hr)
    subst w
    subst e
    rfl

/-- Rank induction identifies a semantically normalized stored code with the
actual encoding. This is uniqueness under explicit normal-form clauses, not
existence of an MSO canonical language. -/
theorem PortNormalForm.eq_encode {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : PortNormalForm T O G C) : C=encode T O G := by
  funext v
  have all : ∀ m, ∀ v : Vertex n, v.val=m → C v=encode T O G v := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro v hm
      have hp : (C v).ports=(encode T O G v).ports := by
        apply List.ext_getElem
        · simpa only [encode,List.length_map] using h.length v
        · intro i hi hj
          have hiG : i<(inherited T O G v).length := by rw [←h.length v]; exact hi
          let u := (inherited T O G v)[i]
          let e := (C v).ports[i]
          have he : (C v).ports[i]?=some e := List.getElem?_eq_getElem hi
          have hr : readPort T C n v (i+1)=some u := h.resolved v i hi hiG
          have hv : v.val≠0 := by
            intro hz
            have hc := h.root_empty v hz
            simp only [hc,List.length_nil] at hi
            omega
          have hparent := T.parent_lt v hv
          have heq : ∀ w, w.val≤(T.parent v).val → C w=encode T O G w := by
            intro w hw
            exact ih w.val (by omega) w rfl
          cases n with
          | zero => exact Fin.elim0 v
          | succ fuel =>
            have hc : readPort T C fuel (T.parent v) e.parentPort=some u := by
              simpa only [readPort,he,Option.bind_some] using hr
            have hD : readPort T (encode T O G) fuel (T.parent v) e.parentPort=some u := by
              rw [←readPort_eq_of_prefix T C (encode T O G) h.root_empty fuel (T.parent v)
                e.parentPort heq]
              exact hc
            have hb := (readPort_encode_iff T O G fuel (T.parent v) u e.parentPort
              (by have := v.isLt; omega)).mp hD
            obtain ⟨hbnd,hval⟩ := List.getElem?_eq_some_iff.mp hb
            have hind : e.parentPort=(bag T O G (T.parent v)).idxOf u := by
              rw [←hval]
              exact ((bag_nodup T O G (T.parent v)).idxOf_getElem _ hbnd).symm
            have hbits : e.bit=(entry T O G v u).bit := by
              funext r forward
              exact h.bits v i e he u hr r forward
            have heqEntry : e=entry T O G v u := by
              change PortEntry.mk e.parentPort e.bit =
                PortEntry.mk ((bag T O G (T.parent v)).idxOf u) (entry T O G v u).bit
              rw [hind,hbits]
            simpa only [encode,List.getElem_map] using heqEntry
      have hc := h.color v
      change NodeLabel.mk (C v).color (C v).ports = NodeLabel.mk (G.color v)
        ((inherited T O G v).map (entry T O G v))
      rw [hc]
      exact congrArg (NodeLabel.mk (G.color v)) hp
  exact all v.val v rfl

#print axioms encode_normalForm
#print axioms PortNormalForm.eq_encode
end StackSorting.FinitePort
