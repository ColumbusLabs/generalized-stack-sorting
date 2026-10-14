import ConnectedFiberDecomposition

namespace StackSorting.GraphWidth
open FinitePort

/-- Each event has a token owner, and each token has its two event endpoints. -/
structure EndpointPairing (tokens events : Nat) where
  left : Fin tokens → Fin events
  right : Fin tokens → Fin events
  owner : Fin events → Fin tokens
  owner_left : ∀ v, owner (left v) = v
  owner_right : ∀ v, owner (right v) = v
  complete : ∀ e, e = left (owner e) ∨ e = right (owner e)

/-- Abstract combinatorial data of planarized token curves. The source graph
need not be planar for the lifting theorem. A source vertex carries at most c
tokens, and each token's vertices form a connected source subgraph. -/
structure CurveCover {p tokens events} (G : Graph p) (H : Graph events)
    (E : EndpointPairing tokens events) where
  labels : Fin p → List (Fin tokens)
  anchor : Fin events → Fin p
  anchored : ∀ e, E.owner e ∈ labels (anchor e)
  fiber : ∀ {v q r}, v ∈ labels q → v ∈ labels r →
    Walk G.Adj (fun x => v ∈ labels x) q r
  edge : ∀ {e f}, H.Adj e f →
    E.owner e = E.owner f ∨ G.Adj (anchor e) (anchor f)

def endpointLabels {p tokens events} {G : Graph p} {H : Graph events}
    {E : EndpointPairing tokens events} (C : CurveCover G H E) (q : Fin p) :
    List (Fin events) := (C.labels q).flatMap (fun v => [E.left v, E.right v])

@[simp] theorem mem_endpointLabels {p tokens events} {G : Graph p} {H : Graph events}
    {E : EndpointPairing tokens events} (C : CurveCover G H E) (q e) :
    e ∈ endpointLabels C q ↔ E.owner e ∈ C.labels q := by
  simp only [endpointLabels, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨v, hv, he | he⟩
    · subst e; simpa [E.owner_left] using hv
    · subst e; simpa [E.owner_right] using hv
  · intro he
    exact ⟨E.owner e, he, E.complete e⟩

def CurveCover.connectedLift {p tokens events} {G : Graph p} {H : Graph events}
    {E : EndpointPairing tokens events} (C : CurveCover G H E) : ConnectedLift G H where
  labels := endpointLabels C
  vertex := fun e => ⟨C.anchor e, (mem_endpointLabels C _ e).mpr (C.anchored e)⟩
  edge := by
    intro e f hef
    obtain he | he := C.edge hef
    · left
      refine ⟨C.anchor e, (mem_endpointLabels C _ e).mpr (C.anchored e), ?_⟩
      exact (mem_endpointLabels C _ f).mpr (he ▸ C.anchored e)
    · right
      exact ⟨C.anchor e, C.anchor f, he,
        (mem_endpointLabels C _ e).mpr (C.anchored e),
        (mem_endpointLabels C _ f).mpr (C.anchored f)⟩
  fiber := by
    intro e q r hq hr
    exact (C.fiber ((mem_endpointLabels C q e).mp hq)
      ((mem_endpointLabels C r e).mp hr)).mono
      (fun z hz => (mem_endpointLabels C z e).mpr hz)

theorem endpointLabels_length_le {p tokens events} {G : Graph p} {H : Graph events}
    {E : EndpointPairing tokens events} (C : CurveCover G H E) (q) :
    (endpointLabels C q).length ≤ (C.labels q).length * 2 := by
  apply length_flatMap_le
  intro v _
  simp

/-- Exact multiplicative bound from a source decomposition and connected token
curves. The resulting bags and their running-intersection proof are constructed. -/
theorem CurveCover.lift_bound {p tokens events t} {G : Graph p} {H : Graph events}
    {E : EndpointPairing tokens events} {T : RootedTree t}
    (C : CurveCover G H E) (D : Decomposition G T) {b c}
    (hb : D.BagBound b) (hc : ∀ q, (C.labels q).length ≤ c) :
    (D.lift C.connectedLift).BagBound (b * (c * 2)) := by
  apply D.lift_bagBound C.connectedLift hb
  intro q
  exact Nat.le_trans (endpointLabels_length_le C q) (Nat.mul_le_mul_right 2 (hc q))

/-- The geometric manuscript's last step: two tokens at a source vertex and
source bags of size 3k give actual endpoint bags of size 12k. No existence of
the source graph, its curve cover or its 3k decomposition is assumed as a goal. -/
theorem CurveCover.endpoint_bag_bound {p tokens events t} {G : Graph p}
    {H : Graph events} {E : EndpointPairing tokens events} {T : RootedTree t}
    (C : CurveCover G H E) (D : Decomposition G T) (k : Nat)
    (hb : D.BagBound (3*k)) (hc : ∀ q, (C.labels q).length ≤ 2) :
    (D.lift C.connectedLift).BagBound (12*k) := by
  have h := C.lift_bound D hb hc
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem CurveCover.endpoint_treewidth {p tokens events t} {G : Graph p}
    {H : Graph events} {E : EndpointPairing tokens events} {T : RootedTree t}
    (C : CurveCover G H E) (D : Decomposition G T) (k : Nat) (hk : 0 < k)
    (hb : D.BagBound (3*k)) (hc : ∀ q, (C.labels q).length ≤ 2) :
    HasTreewidthAtMost H (12*k-1) :=
  (D.lift C.connectedLift).treewidthAtMost (C.endpoint_bag_bound D k hb hc) (by omega)

end StackSorting.GraphWidth
