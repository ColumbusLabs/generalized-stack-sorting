import TorsoAbstraction
import Mathlib.Data.Fintype.OfMap

namespace StackSorting.BiInterface
variable {k : ℕ} {V : Type*} (G : Graph k V)

def boundaryPort (p : Port k) : Option G.boundary :=
  (G.port p).attach.map (fun v => ⟨v.val,⟨p,v.property⟩⟩)

@[simp] theorem boundaryPort_val (p : Port k) :
    (boundaryPort G p).map Subtype.val = G.port p := by
  simp only [boundaryPort, Option.map_map, Function.comp_def]
  exact Option.attach_map_subtype_val _

theorem boundaryPort_eq_some (p : Port k) (v : G.boundary) :
    boundaryPort G p = some v ↔ G.port p = some v.val := by
  constructor
  · intro h
    have hh := congrArg (Option.map Subtype.val) h
    simpa only [boundaryPort_val,Option.map_some] using hh
  · intro h
    have hh : (boundaryPort G p).map Subtype.val = some v.val := by rw [boundaryPort_val]; exact h
    obtain ⟨w,hw,he⟩ := Option.map_eq_some_iff.mp hh
    have he' : w = v := Subtype.ext he
    simpa [he'] using hw

noncomputable def boundaryName (v : G.boundary) : Port k := Classical.choose v.property

theorem boundaryName_spec (v : G.boundary) : G.port (boundaryName G v) = some v.val :=
  Classical.choose_spec v.property

theorem boundaryName_injective : Function.Injective (boundaryName G) := by
  intro v w h
  apply Subtype.ext
  apply Option.some.inj
  exact (boundaryName_spec G v).symm.trans ((congrArg G.port h).trans (boundaryName_spec G w))

/-- Only actual interface vertices are retained, so the torso is finite even
when the original graph's vertex type is not assumed finite. -/
noncomputable instance boundaryFintype : Fintype G.boundary :=
  Fintype.ofInjective (boundaryName G) (boundaryName_injective G)

theorem boundary_card_le : Fintype.card G.boundary ≤ 2 * k := by
  have h := Fintype.card_le_of_injective (boundaryName G) (boundaryName_injective G)
  simpa [Port, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using h

/-- The actual torso graph on the actual named vertices, retaining all interface
identities. Paths may use only unnamed vertices internally. -/
def torso : Graph k G.boundary where
  Adj := fun v w => v ≠ w ∧ Through G.Adj G.boundaryᶜ v.val w.val
  symm := by
    intro v w h
    exact ⟨h.1.symm,h.2.reverse (by intros; apply G.symm; assumption)⟩
  loopless := by intro v h; exact h.1 rfl
  left := fun i => boundaryPort G (false,i)
  right := fun i => boundaryPort G (true,i)
  left_inj := by
    intro i j v hi hj
    exact G.left_inj i j v.val
      ((boundaryPort_eq_some G (false,i) v).mp hi)
      ((boundaryPort_eq_some G (false,j) v).mp hj)
  right_inj := by
    intro i j v hi hj
    exact G.right_inj i j v.val
      ((boundaryPort_eq_some G (true,i) v).mp hi)
      ((boundaryPort_eq_some G (true,j) v).mp hj)
  cross := by
    intro i j v hi hj
    exact G.cross i j v.val
      ((boundaryPort_eq_some G (false,i) v).mp hi)
      ((boundaryPort_eq_some G (true,j) v).mp hj)

theorem torso_port (p : Port k) : (torso G).port p = boundaryPort G p := by
  obtain ⟨b,i⟩ := p
  cases b <;> rfl

theorem torso_boundary_all (v : G.boundary) : v ∈ (torso G).boundary := by
  obtain ⟨p,hp⟩ := v.property
  refine ⟨p,?_⟩
  rw [torso_port, boundaryPort_eq_some]
  exact hp

theorem torso_internal_empty : (torso G).boundaryᶜ = ∅ := by
  ext v
  simp [torso_boundary_all G v]

#print axioms torso_boundary_all
end StackSorting.BiInterface
