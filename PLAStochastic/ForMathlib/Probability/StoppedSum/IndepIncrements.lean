import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Integration

/-!
# Common setting for the elementary probability primitives

`IndepIncrements P F Y` says that the real increments `Y t` are adapted in the
shifted sense (`Y t` is `F (t+1)`-measurable) and that each `Y t` is independent
of the past `F t`.  This covers iid sequences with their natural filtration, signed
iid blocks, and the pair filtrations used by the endpoint hierarchy.  The partial
sum `partialSum Y n = ∑ t < n, Y t` includes the increments `Y 0, …, Y (n-1)`.

A stopping index is an `ℕ`-valued map `T` whose events `{t < T}` are
`F t`-measurable: whether increment `Y t` is used is decided by the past.
-/

namespace PGM

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Increments adapted to `F` in the shifted sense and independent of the past. -/
structure IndepIncrements (P : Measure Ω) (F : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable[F (t + 1)] (Y t)
  indep : ∀ t, Indep (MeasurableSpace.comap (Y t) inferInstance) (F t) P

/-- `partialSum Y n = Y 0 + ⋯ + Y (n - 1)`. -/
def partialSum (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, Y t ω

/-- The events `{t < T}` are decided by the past `F t`. -/
def IsStoppingIndex (F : Filtration ℕ mΩ) (T : Ω → ℕ) : Prop :=
  ∀ t, MeasurableSet[F t] {ω | t < T ω}

/-- The sum of the increments used before a stopping index. -/
def stoppedSum (Y : ℕ → Ω → ℝ) (T : Ω → ℕ) (ω : Ω) : ℝ :=
  partialSum Y (T ω) ω

namespace IndepIncrements

variable {P : Measure Ω} {F : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}

/-- A past-measurable factor and the next increment are independent. -/
theorem indepFun_past (h : IndepIncrements P F Y) (t : ℕ) {Z : Ω → ℝ}
    (hZ : Measurable[F t] Z) : IndepFun (Y t) Z P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (h.indep t) (hZ.comap_le)

/-- `E[Z * Y t] = E[Z] * E[Y t]` for a past-measurable `Z`. -/
theorem integral_mul_past (h : IndepIncrements P F Y) (t : ℕ) {Z : Ω → ℝ}
    (hZ : Measurable[F t] Z) (hYm : Measurable (Y t)) :
    ∫ ω, Z ω * Y t ω ∂P = (∫ ω, Z ω ∂P) * ∫ ω, Y t ω ∂P := by
  have hind := (h.indepFun_past t hZ).symm
  exact hind.integral_mul_eq_mul_integral
    ((hZ.mono (F.le t) le_rfl).aestronglyMeasurable) hYm.aestronglyMeasurable

end IndepIncrements

end PGM
