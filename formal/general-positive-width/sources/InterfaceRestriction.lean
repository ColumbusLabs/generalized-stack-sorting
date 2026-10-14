import PaddingReachability

namespace StackSorting.BiInterface.RepeatedColumn
variable {k : ℕ} {V : Type*}

/-- Retain a partial port exactly when its actual endpoint is retained. -/
noncomputable def restrictPort (S : Set V) (p : Option V) : Option S := by
  classical
  exact match p with
    | none => none
    | some v => if h : v ∈ S then some ⟨v,h⟩ else none

theorem restrictPort_eq_some (S : Set V) (p : Option V) (v : S) :
    restrictPort S p = some v ↔ p = some v.val := by
  classical
  cases p with
  | none => simp [restrictPort]
  | some w =>
    by_cases hw : w ∈ S
    · simp only [restrictPort, dite_eq_left hw, Option.some.injEq]
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    · simp only [restrictPort, dite_eq_right hw, Option.some.injEq, reduceCtorEq, false_iff]
      intro he
      exact hw (he.symm ▸ v.property)

/-- The actual induced bi-interface graph. A deleted endpoint loses its port;
no new edge or walk is added. -/
noncomputable def restrictGraph (G : Graph k V) (S : Set V) : Graph k S where
  Adj := fun v w => G.Adj v.val w.val
  symm := G.symm
  loopless := fun v => G.loopless v.val
  left := fun i => restrictPort S (G.left i)
  right := fun i => restrictPort S (G.right i)
  left_inj := by
    intro i j v hi hj
    exact G.left_inj i j v.val ((restrictPort_eq_some S _ v).mp hi)
      ((restrictPort_eq_some S _ v).mp hj)
  right_inj := by
    intro i j v hi hj
    exact G.right_inj i j v.val ((restrictPort_eq_some S _ v).mp hi)
      ((restrictPort_eq_some S _ v).mp hj)
  cross := by
    intro i j v hi hj
    exact G.cross i j v.val ((restrictPort_eq_some S _ v).mp hi)
      ((restrictPort_eq_some S _ v).mp hj)

theorem restrictGraph_port (G : Graph k V) (S : Set V) (p : Port k) :
    (restrictGraph G S).port p = restrictPort S (G.port p) := by
  obtain ⟨b,i⟩ := p
  cases b <;> rfl

theorem restrictGraph_port_some (G : Graph k V) (S : Set V) (p : Port k) (v : S) :
    (restrictGraph G S).port p = some v ↔ G.port p = some v.val := by
  rw [restrictGraph_port,restrictPort_eq_some]

theorem restrictGraph_boundary (G : Graph k V) (S : Set V) (v : S) :
    v ∈ (restrictGraph G S).boundary ↔ v.val ∈ G.boundary := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(restrictGraph_port_some G S p v).mp hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,(restrictGraph_port_some G S p v).mpr hp⟩

/-- Deleting only boundary vertices commutes exactly with the finite walks
that define torso edges. Internal vertices were already forbidden to be among
the deleted boundary; therefore this theorem constructs the lifted walk. -/
theorem through_restrict_iff (G : Graph k V) (S : Set V)
    (hkeep : G.boundaryᶜ ⊆ S) (v w : S) :
    Through (restrictGraph G S).Adj (restrictGraph G S).boundaryᶜ v w ↔
      Through G.Adj G.boundaryᶜ v.val w.val := by
  constructor
  · intro h
    exact h.map Subtype.val (by intros; assumption)
      (fun a ha hb => ha ((restrictGraph_boundary G S a).mpr hb))
  · intro h
    have lift (x y : V) (hp : Through G.Adj G.boundaryᶜ x y) :
        ∀ hx : x ∈ S, ∀ hy : y ∈ S,
          Through (restrictGraph G S).Adj (restrictGraph G S).boundaryᶜ ⟨x,hx⟩ ⟨y,hy⟩ := by
      induction hp with
      | refl a => intro hx hy; exact .refl (⟨a,hx⟩ : S)
      | edge hp => intro hx hy; exact .edge hp
      | @join a b c hab hb hbc ihab ihbc =>
        intro hx hy
        have hbs : b ∈ S := hkeep hb
        exact .join (ihab hx hbs)
          (fun hmem => hb ((restrictGraph_boundary G S ⟨b,hbs⟩).mp hmem)) (ihbc hbs hy)
    exact lift v.val w.val h v.property w.property

/-- A persistent vertex has the same port name on both sides. -/
def Persistent (G : Graph k V) : Set V :=
  {v | ∃ i, G.left i = some v ∧ G.right i = some v}

def PersistentAt (G : Graph k V) (i : Fin k) : Prop :=
  ∃ v, G.left i = some v ∧ G.right i = some v

noncomputable def removePersistent (G : Graph k V) : Graph k ↥((Persistent G)ᶜ) :=
  restrictGraph G (Persistent G)ᶜ

theorem persistent_boundary (G : Graph k V) : Persistent G ⊆ G.boundary := by
  rintro v ⟨i,hi,_⟩
  exact ⟨(false,i),hi⟩

theorem persistent_of_port (G : Graph k V) (p : Port k) {v : V}
    (hp : G.port p = some v) : v ∈ Persistent G ↔ PersistentAt G p.2 := by
  obtain ⟨b,i⟩ := p
  constructor
  · rintro ⟨j,hj,hj'⟩
    cases b
    · have he : i = j := G.left_inj i j v hp hj
      exact he.symm ▸ ⟨v,hj,hj'⟩
    · have he : i = j := G.right_inj i j v hp hj'
      exact he.symm ▸ ⟨v,hj,hj'⟩
  · rintro ⟨w,hw,hw'⟩
    cases b
    · have he : w = v := Option.some.inj (hw.symm.trans hp)
      exact ⟨i,he ▸ hw,he ▸ hw'⟩
    · have he : w = v := Option.some.inj (hw'.symm.trans hp)
      exact ⟨i,he ▸ hw,he ▸ hw'⟩

theorem removePersistent_disjoint (G : Graph k V) :
    ∀ i j v, (removePersistent G).left i = some v →
      (removePersistent G).right j = some v → False := by
  intro i j v hi hj
  have hi' := (restrictPort_eq_some (Persistent G)ᶜ (G.left i) v).mp hi
  have hj' := (restrictPort_eq_some (Persistent G)ᶜ (G.right j) v).mp hj
  have he : i = j := G.cross i j v.val hi' hj'
  subst j
  exact v.property ⟨i,hi',hj'⟩

#print axioms through_restrict_iff
#print axioms removePersistent_disjoint
end StackSorting.BiInterface.RepeatedColumn
