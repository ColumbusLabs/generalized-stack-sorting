import BiInterfaceGraph
import Mathlib.Data.Fintype.Pi

namespace StackSorting.BiInterface

abbrev Port (k : ℕ) := Bool × Fin k

def Graph.port {k : ℕ} {V : Type*} (G : Graph k V) : Port k → Option V
  | (false, i) => G.left i
  | (true, i) => G.right i

def Graph.boundary {k : ℕ} {V : Type*} (G : Graph k V) : Set V :=
  {v | ∃ p, G.port p = some v}

/-- A finite table retains presence, actual interface-vertex identities, and
interface-avoiding torso edges separately. Equal connectivity components alone
would not be a sound abstraction. -/
abbrev Code (k : ℕ) :=
  (Port k → Bool) × (Port k → Port k → Bool) × (Port k → Port k → Bool)

noncomputable def abstraction {k : ℕ} {V : Type*} (G : Graph k V) : Code k := by
  classical
  exact (fun p => (G.port p).isSome,
    (fun p q => decide (∃ v, G.port p = some v ∧ G.port q = some v)),
    (fun p q => decide (∃ v w, G.port p = some v ∧ G.port q = some w ∧
      v ≠ w ∧ Through G.Adj G.boundaryᶜ v w)))

theorem abstraction_presence {k : ℕ} {V : Type*} (G : Graph k V) (p : Port k) :
    (abstraction G).1 p = true ↔ ∃ v, G.port p = some v := by
  classical
  simp only [abstraction]
  cases G.port p <;> simp

theorem abstraction_identity {k : ℕ} {V : Type*} (G : Graph k V) (p q : Port k) :
    (abstraction G).2.1 p q = true ↔ ∃ v, G.port p = some v ∧ G.port q = some v := by
  classical
  simp [abstraction]

theorem abstraction_edge {k : ℕ} {V : Type*} (G : Graph k V) (p q : Port k) :
    (abstraction G).2.2 p q = true ↔
      ∃ v w, G.port p = some v ∧ G.port q = some w ∧
        v ≠ w ∧ Through G.Adj G.boundaryᶜ v w := by
  classical
  simp [abstraction]

/-- Finiteness is uniform in k and independent of the graph's vertex set. -/
theorem abstraction_finite (k : ℕ) : Finite (Code k) := inferInstance

end StackSorting.BiInterface
