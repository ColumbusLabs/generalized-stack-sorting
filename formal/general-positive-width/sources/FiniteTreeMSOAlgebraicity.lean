import FiniteTreeMSOPositionCorrectness
import FiniteTreeLanguageAlgebraicity

namespace StackSorting.TreeAutomaton
open StackSorting.GeneralAlgebraicity
open scoped RatFunc
noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Counts the literal distinct labelled tree objects satisfying a language. -/
def languageSeries (L : Set (BinaryTree α)) : PowerSeries ℚ := by
  classical
  exact PowerSeries.mk fun n => (((treesOfSize n).filter (fun t => t ∈ L)).card : ℚ)

theorem Recognizable.languageSeries_algebraic {L : Set (BinaryTree α)}
    (h : Recognizable L) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (languageSeries L)) := by
  classical
  obtain ⟨Q, hQ, A, F, hA⟩ := h
  let _ := hQ
  let accept : Finset Q := Finset.univ.filter (fun q => q ∈ F)
  have heq : languageSeries L = acceptedSeries A accept := by
    apply PowerSeries.ext
    intro n
    simp only [languageSeries, PowerSeries.coeff_mk, coeff_acceptedSeries]
    congr 1
    congr 1
    ext t
    simp [acceptedTrees, accept, ← hA]
  rw [heq]
  exact acceptedSeries_algebraic A accept

namespace Logic
/-- Closed formulas on unmarked labels use the unique empty variable environment. -/
def sentenceLanguage (p : Formula α 0) : Set (BinaryTree α) :=
  {t | p.PosHolds (t.map fun a => (a, Fin.elim0))}

theorem sentence_recognizable (p : Formula α 0) : Recognizable (sentenceLanguage p) :=
  p.positions_recognizable.preimage (fun a => (a, Fin.elim0))

/-- The finite-tree logical bridge is unconditional. Sparse-graph interpretation,
canonical tree encodings, and count-preserving graph/tree correspondence are
separate obligations and are not premises disguised as recognizability. -/
theorem sentence_countingSeries_algebraic (p : Formula α 0) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (languageSeries (sentenceLanguage p))) :=
  (sentence_recognizable p).languageSeries_algebraic

#print axioms sentence_countingSeries_algebraic
end Logic
end
end StackSorting.TreeAutomaton
