import FinitePortEncoding

namespace StackSorting.FinitePort

/-- Complete readback for the actual encoding, including invalid indices.
The existing recovery theorem gives the reverse implication; the new direction
rules out a successful read at an absent or differently named bag entry. -/
theorem readPort_encode_iff {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (fuel : Nat)
    (v u : Vertex n) (i : Nat) (hv : v.val ≤ fuel) :
    readPort T (encode T O G) fuel v i = some u ↔
      (bag T O G v)[i]? = some u := by
  constructor
  · intro h
    cases i with
    | zero =>
      simp only [readPort,Option.some.injEq] at h
      subst u
      simp only [bag,List.getElem?_cons_zero]
    | succ i =>
      cases fuel with
      | zero => simp only [readPort] at h; contradiction
      | succ fuel =>
        have hb : ∃ e, (encode T O G v).ports[i]? = some e := by
          cases he : (encode T O G v).ports[i]? with
          | none => simp only [readPort,he,Option.bind_none] at h; contradiction
          | some e => exact ⟨e,rfl⟩
        obtain ⟨e,he⟩ := hb
        have hm : ((inherited T O G v)[i]?).map (entry T O G v) = some e := by
          simpa only [encode,List.getElem?_map] using he
        obtain ⟨w,hw,_⟩ := Option.map_eq_some_iff.mp hm
        have hbag : (bag T O G v)[i+1]? = some w := hw
        have hr := readPort_encode T O G (fuel+1) v w (i+1) hv hbag
        have hwu : w=u := Option.some.inj (hr.symm.trans h)
        exact hwu ▸ hbag
  · exact readPort_encode T O G fuel v u i hv

/-- In an actual encoding, a resolved endpoint has exactly one bag index. -/
theorem readPort_encode_index_unique {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (v u : Vertex n) (i j : Nat)
    (hi : readPort T (encode T O G) n v i = some u)
    (hj : readPort T (encode T O G) n v j = some u) : i=j := by
  have hv := Nat.le_of_lt v.isLt
  have hi' := (readPort_encode_iff T O G n v u i hv).mp hi
  have hj' := (readPort_encode_iff T O G n v u j hv).mp hj
  have hlt := (List.getElem?_eq_some_iff.mp hi').1
  exact (List.Nodup.getElem?_inj hlt (bag_nodup T O G v)).mp (hi'.trans hj'.symm)

#print axioms readPort_encode_iff
#print axioms readPort_encode_index_unique
end StackSorting.FinitePort
