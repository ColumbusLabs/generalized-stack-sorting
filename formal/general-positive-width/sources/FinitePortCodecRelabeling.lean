import FinitePortEncoding
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.Nodup

/-!
Exact finite-port codec transport under a temporary change of vertex names.
The independent bag order is transported, never replaced by numeric order.
No graph edges, inherited entries, or all-zero directional bit vectors are
removed. No canonical-decomposition or counting premise is used.
-/
namespace StackSorting.FinitePort.CodecRelabeling

variable {n colors relations : Nat}

/-- The same literal order transport used by first-child/next-sibling coding. -/
def relabelOrder (e : Fin n ≃ Fin n) (O : FixedOrder n) : FixedOrder n where
  vertices := O.vertices.map e
  nodup := O.nodup.map e.injective
  complete v := List.mem_map.mpr ⟨e.symm v, O.complete _, e.apply_symm_apply v⟩

theorem ancestor_relabel (T U : RootedTree n) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    {u v : Fin n} (h : Ancestor T u v) : Ancestor U (e u) (e v) := by
  induction h with
  | refl => exact .refl _
  | @step v hv _ ih =>
    apply Ancestor.step (fun he => hv ((hz v).mp he))
    rw [hp v]
    exact ih

theorem ancestor_relabel_iff (T U : RootedTree n) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v)) (u v : Fin n) :
    Ancestor U (e u) (e v) ↔ Ancestor T u v := by
  constructor
  · intro h
    have hzi : ∀ w, (e.symm w).val = 0 ↔ w.val = 0 := by
      intro w
      simpa only [e.apply_symm_apply] using (hz (e.symm w)).symm
    have hpi : ∀ w, T.parent (e.symm w) = e.symm (U.parent w) := by
      intro w
      apply e.injective
      simpa only [e.apply_symm_apply] using (hp (e.symm w)).symm
    simpa only [e.symm_apply_apply] using ancestor_relabel U T e.symm hzi hpi h
  · exact ancestor_relabel T U e hz hp

theorem adjacent_relabel_iff (G H : Diagram n colors relations)
    (e : Fin n ≃ Fin n)
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (u v : Fin n) :
    Adjacent H (e u) (e v) ↔ Adjacent G u v := by
  simp only [Adjacent, hr]

theorem inherited_relabel_iff (T U : RootedTree n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v u : Fin n) :
    Inherited U H (e v) (e u) ↔ Inherited T G v u := by
  constructor
  · rintro ⟨ha, hn, z, hvz, huz⟩
    obtain ⟨w, rfl⟩ := e.surjective z
    exact ⟨(ancestor_relabel_iff T U e hz hp u v).mp ha,
      fun h => hn (congrArg e h), w,
      (ancestor_relabel_iff T U e hz hp v w).mp hvz,
      (adjacent_relabel_iff G H e hr u w).mp huz⟩
  · rintro ⟨ha, hn, z, hvz, huz⟩
    exact ⟨(ancestor_relabel_iff T U e hz hp u v).mpr ha,
      fun h => hn (e.injective h), e z,
      (ancestor_relabel_iff T U e hz hp v z).mpr hvz,
      (adjacent_relabel_iff G H e hr u z).mpr huz⟩

/-- Ordered list equality, stronger than equality of inherited vertex sets. -/
theorem inherited_relabel (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v : Fin n) :
    inherited U (relabelOrder e O) H (e v) = (inherited T O G v).map e := by
  classical
  simp only [inherited, relabelOrder, List.filter_map, Function.comp_def]
  have hpred : (fun u => decide (Inherited U H (e v) (e u))) =
      (fun u => decide (Inherited T G v u)) := by
    funext u
    simp only [inherited_relabel_iff T U G H e hz hp hr v u]
  rw [hpred]

theorem bag_relabel (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v : Fin n) :
    bag U (relabelOrder e O) H (e v) = (bag T O G v).map e := by
  simp only [bag, inherited_relabel T U O G H e hz hp hr, List.map_cons]

/-- Mapping a list by a bijection preserves the exact first-occurrence index,
including the out-of-list convention. No membership hypothesis is needed. -/
theorem idxOf_map_equiv (e : Fin n ≃ Fin n) (xs : List (Fin n)) (u : Fin n) :
    (xs.map e).idxOf (e u) = xs.idxOf u := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.idxOf_cons, beq_iff_eq, e.apply_eq_iff_eq, ih]

/-- The stored parent-port is preserved exactly, not merely bounded or decoded
up to isomorphism. The statement also holds outside the inherited list. -/
theorem parentPort_relabel (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v u : Fin n) :
    (entry U (relabelOrder e O) H (e v) (e u)).parentPort =
      (entry T O G v u).parentPort := by
  change (bag U (relabelOrder e O) H (U.parent (e v))).idxOf (e u) =
    (bag T O G (T.parent v)).idxOf u
  rw [hp v, bag_relabel T U O G H e hz hp hr, idxOf_map_equiv]

theorem entry_relabel (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v u : Fin n) :
    entry U (relabelOrder e O) H (e v) (e u) = entry T O G v u := by
  have hport := parentPort_relabel T U O G H e hz hp hr v u
  have hbit : (entry U (relabelOrder e O) H (e v) (e u)).bit =
      (entry T O G v u).bit := by
    funext r forward
    simp only [entry, hr]
  exact congrArg₂ (@PortEntry.mk relations) hport hbit

/-- Literal node-label equality under temporary vertex renumbering. -/
theorem encode_relabel (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hc : ∀ v c, H.color (e v) c = G.color v c)
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (v : Fin n) :
    encode U (relabelOrder e O) H (e v) = encode T O G v := by
  have hcolor : H.color (e v) = G.color v := funext (hc v)
  simp only [encode, hcolor, inherited_relabel T U O G H e hz hp hr,
    List.map_map, Function.comp_def, entry_relabel T U O G H e hz hp hr]

/-- Every inherited entry survives in the very same list slot and decodes to
the renamed vertex. In particular no positive edge bit is required: all-zero
entries are retained with their parent-port identity and their multiplicity. -/
theorem every_inherited_port_kept_under_relabeling
    (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hc : ∀ v c, H.color (e v) c = G.color v c)
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v)
    (v u : Fin n) (hu : Inherited T G v u) :
    ∃ i, (encode T O G v).ports[i]? = some (entry T O G v u) ∧
      (encode U (relabelOrder e O) H (e v)).ports[i]? = some (entry T O G v u) ∧
      readPort T (encode T O G) n v (i + 1) = some u ∧
      readPort U (encode U (relabelOrder e O) H) n (e v) (i + 1) = some (e u) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((mem_inherited T O G v u).mpr hu)
  have hslot : (encode T O G v).ports[i]? = some (entry T O G v u) := by
    simp [encode, hi]
  refine ⟨i, hslot, ?_, encoded_port_identity T O G v u (i + 1) hi, ?_⟩
  · rw [encode_relabel T U O G H e hz hp hc hr]
    exact hslot
  · apply encoded_port_identity U (relabelOrder e O) H (e v) (e u) (i + 1)
    change (inherited U (relabelOrder e O) H (e v))[i]? = some (e u)
    simp only [inherited_relabel T U O G H e hz hp hr, List.getElem?_map, hi,
      Option.map_some]

theorem widthAtMost_relabel_iff (T U : RootedTree n) (O : FixedOrder n)
    (G H : Diagram n colors relations) (e : Fin n ≃ Fin n)
    (hz : ∀ v, (e v).val = 0 ↔ v.val = 0)
    (hp : ∀ v, U.parent (e v) = e (T.parent v))
    (hr : ∀ r u v, H.rel r (e u) (e v) = G.rel r u v) (W : Nat) :
    WidthAtMost U (relabelOrder e O) H W ↔ WidthAtMost T O G W := by
  constructor
  · intro h v
    simpa only [inherited_relabel T U O G H e hz hp hr, List.length_map] using h (e v)
  · intro h w
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [inherited_relabel T U O G H e hz hp hr, List.length_map] using h v

#print axioms ancestor_relabel_iff
#print axioms inherited_relabel
#print axioms bag_relabel
#print axioms parentPort_relabel
#print axioms entry_relabel
#print axioms encode_relabel
#print axioms every_inherited_port_kept_under_relabeling
#print axioms widthAtMost_relabel_iff

end StackSorting.FinitePort.CodecRelabeling
