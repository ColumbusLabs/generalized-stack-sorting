import BoundedSourceTree
import UCurveStemDistance

namespace StackSorting.GraphWidth.UCurve
open FinitePort

/-- The anchor subset remembers only actual endpoint vertices of the drawing. -/
def endpointAnchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (q : Node D) : Prop := ∃ e, anchor D e = q

theorem stems_give_apex_radius {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (k : Nat) (hbound : ∀ e, (stemCrossings D e).length < k) :
    SourceApex.Radius (sourceGraph D) (endpointAnchor D) k := by
  intro q
  obtain ⟨e, length, hl, hw⟩ := source_radius_from_stems D k hbound q
  exact ⟨anchor D e, length, ⟨e, rfl⟩, hl, hw⟩

/-- The actual source-radius theorem now supplies a constructed bounded
source-ancestor tree, with no assumed tree or depth certificate. -/
theorem stem_source_ancestor_bound {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (k : Nat) (hk : 0 < k)
    (hbound : ∀ e, (stemCrossings D e).length < k)
    (i : Fin ((vertices D).length+1)) (xs : List (Node D)) (hn : xs.Nodup)
    (ha : ∀ v ∈ xs,
      let R := SourceApex.reachable (sourceGraph D) (endpointAnchor D)
        (stems_give_apex_radius D k hbound)
      Ancestor R.numbered.tree (R.numbered.index v.succ) i) : xs.length ≤ k := by
  exact SourceApex.source_ancestor_bound (sourceGraph D) (endpointAnchor D)
    (stems_give_apex_radius D k hbound) hk i xs hn ha

end StackSorting.GraphWidth.UCurve
