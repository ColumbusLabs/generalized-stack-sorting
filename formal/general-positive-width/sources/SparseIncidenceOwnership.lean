import SparseFullClass

/-! Exact three-copy representation of the simple undirected successor/matching
union. Vertex names are arbitrary: orientation uses intrinsic path chronology,
not the numerical order on names. -/
namespace StackSorting.SparseEndpointMSO
namespace IncidenceOwnership

/-- Intrinsic strict chronology in the sparse vocabulary. -/
def Before (D : Model) (x y : Nat) : Prop := x ≠ y ∧ ClosedReach D x y

/-- These are properties, not added axioms. They are proved below for every
model satisfying the actual full accepted sentence. -/
structure Laws (D : Model) : Prop where
  total : ∀ x ∈ D.domain, ∀ y ∈ D.domain, x = y ∨ Before D x y ∨ Before D y x
  asymm : ∀ x ∈ D.domain, ∀ y ∈ D.domain, Before D x y → ¬ Before D y x
  successor_before : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.S x y → Before D x y
  successor_functional : ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    D.S x y → D.S x z → y = z
  matching_symmetric : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → D.M y x
  matching_irrefl : ∀ x ∈ D.domain, ¬ D.M x x
  matching_functional : ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    D.M x y → D.M x z → y = z

theorem before_iff_rank_lt {D : Model} {output : List Nat}
    (iso : Isomorphism D (canonicalDiagram output)) {x y : Nat}
    (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    Before D x y ↔ iso.toFun x < iso.toFun y := by
  have hp := eventDiagram_path (Generalized.canonicalEvents 0 output)
  have hr : ClosedReach D x y ↔ iso.toFun x ≤ iso.toFun y :=
    (iso.closedReach hx hy).trans ((closedReach_iff_walk _ (iso.to_mem x hx)).trans
      (walk_iff_le _ _ hp (iso.to_mem x hx) (iso.to_mem y hy)))
  constructor
  · rintro ⟨hne, hb⟩
    have hle := hr.mp hb
    have hn : iso.toFun x ≠ iso.toFun y := fun h => hne (iso.injective hx hy h)
    omega
  · intro hlt
    refine ⟨?_, hr.mpr (Nat.le_of_lt hlt)⟩
    intro he
    subst y
    omega

theorem laws_of_canonical_isomorphism {D : Model} {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (iso : Isomorphism D (canonicalDiagram output)) :
    Laws D := by
  have hpath := eventDiagram_path (Generalized.canonicalEvents 0 output)
  have hm := canonicalMatchingAxioms hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases Nat.lt_trichotomy (iso.toFun x) (iso.toFun y) with h | h | h
    · exact Or.inr (Or.inl ((before_iff_rank_lt iso hx hy).mpr h))
    · exact Or.inl (iso.injective hx hy h)
    · exact Or.inr (Or.inr ((before_iff_rank_lt iso hy hx).mpr h))
  · intro x hx y hy hxy hyx
    have h₁ := (before_iff_rank_lt iso hx hy).mp hxy
    have h₂ := (before_iff_rank_lt iso hy hx).mp hyx
    omega
  · intro x hx y hy hs
    have h := (hpath.2 _ (iso.to_mem x hx) _ (iso.to_mem y hy)).mp
      ((iso.successor_iff x hx y hy).mp hs)
    exact (before_iff_rank_lt iso hx hy).mpr (by omega)
  · intro x hx y hy z hz hxy hxz
    have h₁ := (hpath.2 _ (iso.to_mem x hx) _ (iso.to_mem y hy)).mp
      ((iso.successor_iff x hx y hy).mp hxy)
    have h₂ := (hpath.2 _ (iso.to_mem x hx) _ (iso.to_mem z hz)).mp
      ((iso.successor_iff x hx z hz).mp hxz)
    exact iso.injective hy hz (h₁.symm.trans h₂)
  · intro x hx y hy hxy
    exact (iso.matching_iff y hy x hx).mpr
      (hm.symmetric _ (iso.to_mem x hx) _ (iso.to_mem y hy)
        ((iso.matching_iff x hx y hy).mp hxy))
  · intro x hx hxx
    have hmxx := (iso.matching_iff x hx x hx).mp hxx
    have he := hm.opposite _ (iso.to_mem x hx) _ (iso.to_mem x hx) hmxx
    rcases (hm.partition _ (iso.to_mem x hx)).1 with hi | hr
    · exact (hm.partition _ (iso.to_mem x hx)).2 ⟨hi, he.mp hi⟩
    · exact (hm.partition _ (iso.to_mem x hx)).2 ⟨he.mpr hr, hr⟩
  · intro x hx y hy z hz hxy hxz
    obtain ⟨w, _, _, hw⟩ := hm.perfect _ (iso.to_mem x hx)
    exact iso.injective hy hz ((hw _ (iso.to_mem y hy)
      ((iso.matching_iff x hx y hy).mp hxy)).trans
      (hw _ (iso.to_mem z hz) ((iso.matching_iff x hx z hz).mp hxz)).symm)

/-- No extra graph-ownership hypothesis is needed for accepted physical models;
this includes empty domains and arbitrary renamings. -/
theorem laws_of_fullAcceptedSentence {D : Model} {r s : Nat}
    (h : Satisfies D (fullAcceptedSentence r s)) : Laws D := by
  obtain ⟨_, _, hp, _, ⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp h
  exact laws_of_canonical_isomorphism hp iso

/-- The simple undirected union, restricted to the genuine finite domain. -/
def Adjacent (D : Model) (x y : Nat) : Prop :=
  x ∈ D.domain ∧ y ∈ D.domain ∧ x ≠ y ∧
    (D.S x y ∨ D.S y x ∨ D.M x y ∨ D.M y x)

theorem adjacent_symm {D : Model} {x y : Nat} : Adjacent D x y → Adjacent D y x := by
  rintro ⟨hx, hy, hn, h⟩
  refine ⟨hy, hx, Ne.symm hn, ?_⟩
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- One canonical ordered pair per undirected edge. -/
def Edge (D : Model) := {p : Nat × Nat // Before D p.1 p.2 ∧ Adjacent D p.1 p.2}
def Vertex (D : Model) := {x : Nat // x ∈ D.domain}
def Element (D : Model) := Sum (Vertex D) (Edge D)

def Incident {D : Model} (v : Vertex D) (e : Edge D) : Prop :=
  v.val = e.val.1 ∨ v.val = e.val.2

/-- A matching copy exists only if this undirected edge has no successor copy. -/
def MatchingOnly (D : Model) (x y : Nat) : Prop :=
  Before D x y ∧ D.M x y ∧ ¬ (D.S x y ∨ D.S y x)

def ValidCode (D : Model) (c : Fin 3) (x : Nat) : Prop :=
  x ∈ D.domain ∧
    Fin.cases True (Fin.cases (∃ y ∈ D.domain, D.S x y)
      (fun _ => ∃ y ∈ D.domain, MatchingOnly D x y)) c

def Code (D : Model) := {p : Fin 3 × Nat // ValidCode D p.1 p.2}

@[simp] theorem valid_vertex (D : Model) (x : Nat) :
    ValidCode D 0 x ↔ x ∈ D.domain := by simp [ValidCode]
@[simp] theorem valid_successor (D : Model) (x : Nat) :
    ValidCode D 1 x ↔ x ∈ D.domain ∧ ∃ y ∈ D.domain, D.S x y := Iff.rfl
@[simp] theorem valid_matching (D : Model) (x : Nat) :
    ValidCode D 2 x ↔ x ∈ D.domain ∧ ∃ y ∈ D.domain, MatchingOnly D x y := Iff.rfl

/-- Endpoints, with no hidden chosen target. This is the interface useful to a
finite-copy interpretation of incidence predicates. -/
def Represents (D : Model) (c : Fin 3) (x : Nat) : Element D → Prop
  | .inl v => c = 0 ∧ x = v.val
  | .inr e => x = e.val.1 ∧
      ((c = 1 ∧ D.S e.val.1 e.val.2) ∨
       (c = 2 ∧ MatchingOnly D e.val.1 e.val.2))

theorem edge_kinds {D : Model} (h : Laws D) (e : Edge D) :
    D.S e.val.1 e.val.2 ∨ MatchingOnly D e.val.1 e.val.2 := by
  classical
  have hx := e.property.2.1
  have hy := e.property.2.2.1
  have hn : ¬ D.S e.val.2 e.val.1 := fun hs =>
    h.asymm _ hx _ hy e.property.1 (h.successor_before _ hy _ hx hs)
  by_cases hs : D.S e.val.1 e.val.2
  · exact Or.inl hs
  · refine Or.inr ⟨e.property.1, ?_, fun hh => hh.elim hs hn⟩
    rcases e.property.2.2.2.2 with hxy | hyx | hxy | hyx
    · exact False.elim (hs hxy)
    · exact False.elim (hn hyx)
    · exact hxy
    · exact h.matching_symmetric _ hy _ hx hyx

theorem edge_endpoint_unique {D : Model} (h : Laws D) (e f : Edge D)
    (he : e.val.1 = f.val.1 ∧ e.val.2 = f.val.2 ∨
      e.val.1 = f.val.2 ∧ e.val.2 = f.val.1) : e = f := by
  apply Subtype.ext
  rcases he with he | he
  · exact Prod.ext he.1 he.2
  · have hf : Before D e.val.2 e.val.1 := by simpa only [he.1, he.2] using f.property.1
    exact False.elim (h.asymm _ e.property.2.1 _ e.property.2.2.1 e.property.1 hf)

/-- Every physical graph edge has an actual incidence edge; conversely each
incidence edge has exactly the advertised endpoints and cannot be phantom. -/
theorem edge_coverage {D : Model} (h : Laws D) (x y : Nat) :
    Adjacent D x y ↔ ∃ e : Edge D,
      (e.val.1 = x ∧ e.val.2 = y) ∨ (e.val.1 = y ∧ e.val.2 = x) := by
  constructor
  · intro ha
    rcases h.total x ha.1 y ha.2.1 with he | hb | hb
    · exact False.elim (ha.2.2.1 he)
    · exact ⟨⟨(x, y), hb, ha⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨(y, x), hb, adjacent_symm ha⟩, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨e, he | he⟩
    · simpa only [he.1, he.2] using e.property.2
    · simpa only [he.1, he.2] using adjacent_symm e.property.2

/-- Distinct tags cannot duplicate an overlapping S/M edge: successor wins. -/
theorem successor_matching_disjoint {D : Model} {x y : Nat}
    (hs : D.S x y) : ¬ MatchingOnly D x y := fun hm => hm.2.2 (Or.inl hs)

theorem represents_valid {D : Model} {c : Fin 3} {x : Nat} {a : Element D}
    (hr : Represents D c x a) : ValidCode D c x := by
  cases a with
  | inl v =>
    rcases hr with ⟨rfl, rfl⟩
    exact (valid_vertex D _).mpr v.property
  | inr e =>
    rcases hr with ⟨rfl, ⟨rfl, hs⟩ | ⟨rfl, hm⟩⟩
    · exact (valid_successor D _).mpr ⟨e.property.2.1, _, e.property.2.2.1, hs⟩
    · exact (valid_matching D _).mpr ⟨e.property.2.1, _, e.property.2.2.1, hm⟩

theorem element_has_code {D : Model} (h : Laws D) (a : Element D) :
    ∃ c x, Represents D c x a := by
  cases a with
  | inl v => exact ⟨0, v.val, rfl, rfl⟩
  | inr e =>
    rcases edge_kinds h e with hs | hm
    · exact ⟨1, e.val.1, rfl, Or.inl ⟨rfl, hs⟩⟩
    · exact ⟨2, e.val.1, rfl, Or.inr ⟨rfl, hm⟩⟩

theorem code_unique {D : Model} {c d : Fin 3} {x y : Nat} {a : Element D}
    (hr : Represents D c x a) (hs : Represents D d y a) : c = d ∧ x = y := by
  cases a with
  | inl v => exact ⟨hr.1.trans hs.1.symm, hr.2.trans hs.2.symm⟩
  | inr e =>
    refine ⟨?_, hr.1.trans hs.1.symm⟩
    rcases hr.2 with ⟨hc, hcS⟩ | ⟨hc, hcM⟩ <;>
      rcases hs.2 with ⟨hd, hdS⟩ | ⟨hd, hdM⟩
    · exact hc.trans hd.symm
    · exact False.elim (successor_matching_disjoint hcS hdM)
    · exact False.elim (successor_matching_disjoint hdS hcM)
    · exact hc.trans hd.symm

theorem code_has_element {D : Model} (h : Laws D) {c : Fin 3} {x : Nat}
    (hv : ValidCode D c x) : ∃ a : Element D, Represents D c x a := by
  revert hv
  refine Fin.cases ?_ (fun c => Fin.cases ?_ (fun c => ?_) c) c
  · intro hv
    exact ⟨.inl ⟨x, (valid_vertex D x).mp hv⟩, rfl, rfl⟩
  · intro hv
    obtain ⟨hx, y, hy, hs⟩ := (valid_successor D x).mp hv
    have hb := h.successor_before x hx y hy hs
    exact ⟨.inr ⟨(x, y), hb, hx, hy, hb.1, Or.inl hs⟩,
      rfl, Or.inl ⟨rfl, hs⟩⟩
  · intro hv
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    obtain ⟨hx, y, hy, hm⟩ := (valid_matching D x).mp hv
    exact ⟨.inr ⟨(x, y), hm.1, hx, hy, hm.1.1, Or.inr (Or.inr (Or.inl hm.2.1))⟩,
      rfl, Or.inr ⟨rfl, hm⟩⟩

theorem represented_element_unique {D : Model} (h : Laws D) {c : Fin 3} {x : Nat}
    {a b : Element D} (ha : Represents D c x a) (hb : Represents D c x b) : a = b := by
  cases a with
  | inl v =>
    cases b with
    | inl w => exact congrArg Sum.inl (Subtype.ext (ha.2.symm.trans hb.2))
    | inr e =>
      have hc0 := ha.1
      rcases hb.2 with ⟨hc, _⟩ | ⟨hc, _⟩ <;> omega
  | inr e =>
    cases b with
    | inl v =>
      have hc0 := hb.1
      rcases ha.2 with ⟨hc, _⟩ | ⟨hc, _⟩ <;> omega
    | inr f =>
      apply congrArg Sum.inr
      apply Subtype.ext
      have hfirst := ha.1.symm.trans hb.1
      apply Prod.ext hfirst
      have hx := e.property.2.1
      have hy := e.property.2.2.1
      have hz := f.property.2.2.1
      rcases ha.2 with ⟨hce, he⟩ | ⟨hce, he⟩ <;>
        rcases hb.2 with ⟨hcf, hf⟩ | ⟨hcf, hf⟩
      · exact h.successor_functional _ hx _ hy _ hz he (hfirst.symm ▸ hf)
      · omega
      · omega
      · exact h.matching_functional _ hx _ hy _ hz he.2.1 (hfirst.symm ▸ hf.2.1)

/-- Existence in both directions and uniqueness in both directions: a genuine
bijection, not a quotient with duplicate or phantom edge representatives. -/
theorem exact_representation {D : Model} (h : Laws D) :
    (∀ a : Element D, ∃ q : Code D, Represents D q.val.1 q.val.2 a ∧
      ∀ p : Code D, Represents D p.val.1 p.val.2 a → p = q) ∧
    (∀ q : Code D, ∃ a : Element D, Represents D q.val.1 q.val.2 a ∧
      ∀ b : Element D, Represents D q.val.1 q.val.2 b → b = a) := by
  constructor
  · intro a
    obtain ⟨c, x, hr⟩ := element_has_code h a
    refine ⟨⟨(c, x), represents_valid hr⟩, hr, ?_⟩
    intro p hp
    apply Subtype.ext
    exact Prod.ext (code_unique hp hr).1 (code_unique hp hr).2
  · intro q
    obtain ⟨a, ha⟩ := code_has_element h q.property
    exact ⟨a, ha, fun b hb => represented_element_unique h hb ha⟩

/-- The exact physical incidence representation follows from the actual
accepted sparse sentence, with no residual ownership obligations. -/
theorem accepted_exact_representation {D : Model} {r s : Nat}
    (h : Satisfies D (fullAcceptedSentence r s)) :
    (∀ a : Element D, ∃ q : Code D, Represents D q.val.1 q.val.2 a ∧
      ∀ p : Code D, Represents D p.val.1 p.val.2 a → p = q) ∧
    (∀ q : Code D, ∃ a : Element D, Represents D q.val.1 q.val.2 a ∧
      ∀ b : Element D, Represents D q.val.1 q.val.2 b → b = a) :=
  exact_representation (laws_of_fullAcceptedSentence h)


noncomputable def encode {D : Model} (h : Laws D) (a : Element D) : Code D :=
  Classical.choose ((exact_representation h).1 a)
noncomputable def decode {D : Model} (h : Laws D) (q : Code D) : Element D :=
  Classical.choose ((exact_representation h).2 q)

theorem encode_represents {D : Model} (h : Laws D) (a : Element D) :
    Represents D (encode h a).val.1 (encode h a).val.2 a :=
  (Classical.choose_spec ((exact_representation h).1 a)).1

theorem decode_represents {D : Model} (h : Laws D) (q : Code D) :
    Represents D q.val.1 q.val.2 (decode h q) :=
  (Classical.choose_spec ((exact_representation h).2 q)).1

theorem decode_encode {D : Model} (h : Laws D) (a : Element D) :
    decode h (encode h a) = a :=
  represented_element_unique h (decode_represents h _) (encode_represents h _)

theorem encode_decode {D : Model} (h : Laws D) (q : Code D) :
    encode h (decode h q) = q := by
  apply Subtype.ext
  have hh := code_unique (encode_represents h (decode h q)) (decode_represents h q)
  exact Prod.ext hh.1 hh.2

#print axioms laws_of_fullAcceptedSentence
#print axioms edge_coverage
#print axioms exact_representation
#print axioms accepted_exact_representation
end IncidenceOwnership
end StackSorting.SparseEndpointMSO
