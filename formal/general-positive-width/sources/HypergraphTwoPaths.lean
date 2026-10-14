import HypergraphPaths
import FiniteTwoPathFlow

/-!
# Two hypergraph paths whose common edge IDs are precisely the cutedges

This is the actual existence assertion of Bojanczyk--Pilipczuk Lemma 5.5
(arXiv:1605.03045, Section 5.1; proof in Appendix E). Edge identifiers are never
quotiented by equality of their incidence sets. The proof uses an explicit
split-incidence network and a proved two-unit residual-flow construction.
-/
namespace FiniteFlow.Hypergraph

variable {V E : Type*}

/-- An edge ID unavoidable by every actual source-to-sink path. -/
def Cutedge (inc : V → E → Prop) (s t : V) (e : E) : Prop :=
  ∀ p : Path inc s t, e ∈ p.walk.edges

/-- Testing cutedges on simple paths is equivalent to testing every walk.
Arc-preserving loop erasure supplies the nontrivial direction. -/
theorem cutedge_iff_every_walk (inc : V → E → Prop) (s t : V) (e : E) :
    Cutedge inc s t e ↔ ∀ w : HWalk inc s t, e ∈ w.edges := by
  constructor
  · intro h w
    obtain ⟨p, hp⟩ := w.exists_path
    exact hp e (h p)
  · intro h p
    exact h p.walk

/-- Only unavoidable edge IDs receive two units; all other edge IDs receive one. -/
noncomputable def capacity (inc : V → E → Prop) (s t : V) : Node V E → Node V E → ℕ := by
  classical
  exact fun a b => match a, b with
    | .vertex x, .enter e => if inc x e then 2 else 0
    | .enter e, .leave f => if e = f then (if Cutedge inc s t e then 2 else 1) else 0
    | .leave e, .vertex x => if inc x e then 2 else 0
    | _, _ => 0

@[simp] theorem capacity_pos_iff (inc : V → E → Prop) (s t : V) (a b : Node V E) :
    0 < capacity inc s t a b ↔ Step inc a b := by
  classical
  constructor
  · intro h
    cases a with
    | vertex x =>
      cases b with
      | vertex y => simp [capacity] at h
      | enter e =>
        by_cases hx : inc x e
        · exact .enter hx
        · simp [capacity,hx] at h
      | leave e => simp [capacity] at h
    | enter e =>
      cases b with
      | vertex y => simp [capacity] at h
      | enter f => simp [capacity] at h
      | leave f =>
        by_cases hef : e = f
        · subst f; exact .cross e
        · simp [capacity,hef] at h
    | leave e =>
      cases b with
      | vertex x =>
        by_cases hx : inc x e
        · exact .leave hx
        · simp [capacity,hx] at h
      | enter f => simp [capacity] at h
      | leave f => simp [capacity] at h
  · intro h
    cases h with
    | enter hx => simp [capacity,hx]
    | cross e => by_cases hc : Cutedge inc s t e <;> simp [capacity,hc]
    | leave hx => simp [capacity,hx]

/-- Every capacity-one arc is exactly the split arc of an avoidable edge ID. -/
theorem capacity_one (inc : V → E → Prop) (s t : V) (a b : Node V E)
    (h : capacity inc s t a b = 1) :
    ∃ e, a = .enter e ∧ b = .leave e ∧ ¬ Cutedge inc s t e := by
  classical
  cases a <;> cases b <;> simp only [capacity] at h
  all_goals try omega
  · split at h <;> omega
  · split at h
    · subst_vars
      split at h
      · omega
      · exact ⟨_,rfl,rfl,by assumption⟩
    · omega
  · split at h <;> omega

/-- An avoiding hypergraph path lifts to a split path avoiding that ordered pair. -/
theorem avoiding_reachable (inc : V → E → Prop) (s t : V) (e : E)
    (h : ¬ Cutedge inc s t e) :
    Relation.ReflTransGen
      (fun a b => 0 < capacity inc s t a b ∧ (a,b) ≠ (.enter e,.leave e))
      (.vertex s) (.vertex t) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Path inc s t, e ∉ p.walk.edges := by
    simpa only [Cutedge, not_forall] using h
  let R : Node V E → Node V E → Prop := fun a b => p.walk.split.Uses a b
  have lift : ∀ {x y}, (w : HWalk inc x y) →
      ∀ a b, w.split.Uses a b →
        0 < capacity inc s t a b := by
    intro x y w a b huse
    exact (capacity_pos_iff inc s t a b).mpr (w.split.uses_relation huse)
  have map : ∀ a b, R a b →
      0 < capacity inc s t a b ∧ (a,b) ≠ (.enter e,.leave e) := by
    intro a b hab
    refine ⟨lift p.walk a b hab, ?_⟩
    intro he
    have ha : a = Node.enter e := congrArg Prod.fst he
    have hb : b = Node.leave e := congrArg Prod.snd he
    subst a; subst b
    exact hp ((p.walk.split_uses_cross_iff e).mp hab)
  exact (p.walk.split.restrict.mono map).to_reachable

/-- Actual two-path existence. Reachability is supplied by an actual hypergraph
walk. No cut ordering, Menger theorem, decomposition or path pair is assumed. -/
theorem exists_two_paths [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (inc : V → E → Prop) (s t : V)
    (connected : Nonempty (HWalk inc s t)) :
    ∃ p q : Path inc s t,
      ∀ e, (e ∈ p.walk.edges ∧ e ∈ q.walk.edges) ↔ Cutedge inc s t e := by
  classical
  obtain ⟨w⟩ := connected
  let c := capacity inc s t
  have pos_to_step : ∀ a b, 0 < c a b → Step inc a b :=
    fun a b h => (capacity_pos_iff inc s t a b).mp h
  have step_to_pos : ∀ a b, Step inc a b → 0 < c a b :=
    fun a b h => (capacity_pos_iff inc s t a b).mpr h
  have reach := (w.split.mono step_to_pos).to_reachable
  have avoid : ∀ a b, c a b = 1 → Relation.ReflTransGen
      (fun x y => 0 < c x y ∧ (x,y) ≠ (a,b)) (.vertex s) (.vertex t) := by
    intro a b hab
    obtain ⟨e, rfl, rfl, he⟩ := capacity_one inc s t a b hab
    exact avoiding_reachable inc s t e he
  obtain ⟨p,q,hp,hq,hcommon⟩ := FiniteFlow.exists_two_paths c (.vertex s) (.vertex t) reach avoid
  let p' := p.mono pos_to_step
  let q' := q.mono pos_to_step
  have hp' : p'.vertices.Nodup := by simpa [p'] using hp
  have hq' : q'.vertices.Nodup := by simpa [q'] using hq
  have hpSimple := DWalk.collapse_simple p' hp'
  have hqSimple := DWalk.collapse_simple q' hq'
  refine ⟨⟨p'.collapse,hpSimple.1,hpSimple.2⟩,
    ⟨q'.collapse,hqSimple.1,hqSimple.2⟩, ?_⟩
  intro e
  constructor
  · intro he
    have hpu : p.Uses (.enter e) (.leave e) :=
      (p.uses_mono pos_to_step _ _).mp ((DWalk.collapse_edge_iff p' e).mp he.1)
    have hqu : q.Uses (.enter e) (.leave e) :=
      (q.uses_mono pos_to_step _ _).mp ((DWalk.collapse_edge_iff q' e).mp he.2)
    have hc := hcommon _ _ hpu hqu
    by_contra hcut
    simp [c,capacity,hcut] at hc
  · intro he
    exact ⟨he _,he _⟩

/-- A network in the exact distinct-terminal, connected, nonempty-edge setting.
The edge type carries multiplicities, even for equal incidence subsets. -/
structure Network (V E : Type*) where
  incident : V → E → Prop
  source : V
  sink : V
  distinct : source ≠ sink
  edge_nonempty : ∀ e, ∃ v, incident v e
  connected : ∀ x y, Nonempty (HWalk incident x y)

/-- Bojanczyk--Pilipczuk Lemma 5.5 for a finite hypergraph network. -/
theorem network_two_paths [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (N : Network V E) :
    ∃ p q : Path N.incident N.source N.sink,
      ∀ e, (e ∈ p.walk.edges ∧ e ∈ q.walk.edges) ↔
        Cutedge N.incident N.source N.sink e :=
  exists_two_paths N.incident N.source N.sink (N.connected _ _)

end FiniteFlow.Hypergraph
