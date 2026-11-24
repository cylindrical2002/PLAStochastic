import PLAStochastic.Swing.Restart.Chain.StreamRebasing
import PLAStochastic.Swing.DenseSampling.Rejection.LongOutputCover

/-! The signed carried state read from the actual repeated recording clocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- At observation n the rejected sample is n+1 and the fitted endpoint is read
from the complete actual output through n. At n=0 the anchor is zero. -/
def nativeRestartObservedState {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  cumulativeSamples X (n+1) ω-
    nativeCarryAnchor (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E n

def nativeRestartRecordingState {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) (k : ℕ) : Ω → ℝ :=
  stoppedValue (nativeRestartObservedState X E)
    (nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k)

theorem nativeRestartObservedState_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) :
    nativeRestartObservedState X E 0 ω = X 0 ω := by
  simp [nativeRestartObservedState, nativeCarryAnchor, nativeStream, nativeSegmentAt,
    nativeSegmentEndpoint, cumulativeSamples_succ]

theorem nativeRecordingTime_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) :
    nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E 0 ω = 0 := by
  apply le_antisymm _ bot_le
  apply (nativeRecordingTime_le_iff _ _ _ 0 0 ω).mpr
  simp [nativeStream, scanNative]

/-- The initial signed state is the actual first Gaussian increment. -/
theorem nativeRestartRecordingState_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) :
    nativeRestartRecordingState X E 0 = X 0 := by
  funext ω
  simp only [nativeRestartRecordingState, stoppedValue, nativeRecordingTime_zero, WithTop.untopA]
  exact nativeRestartObservedState_zero X E ω

theorem nativeRestartRecordingState_eq_at {Ω : Type*} (X : ℕ → Ω → ℝ)
    (E : ℝ) (k n : ℕ) (ω : Ω)
    (hτ : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω = (n : WithTop ℕ)) :
    nativeRestartRecordingState X E k ω = nativeRestartObservedState X E n ω := by
  simp only [nativeRestartRecordingState, stoppedValue, hτ, WithTop.untopA]
  rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

theorem nativeRestartObservedState_adapted (hX : ∀ j, Measurable (X j)) (E : ℝ) (n : ℕ) :
    Measurable[incrementFiltration X hX n] (nativeRestartObservedState X E n) := by
  let m : MeasurableSpace Ω := incrementFiltration X hX n
  have hsample : ∀ j, j ≤ n+1 → Measurable[m] (cumulativeSamples X j) :=
    fun j hj => cumulativeSamples_measurable_at (mΩ := mΩ) hX hj
  let : MeasurableSpace Ω := m
  have hpath : Measurable
      (fun ω j => if j ≤ n then cumulativeSamples X j ω else 0) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ≤ n
    · simpa only [if_pos hj] using hsample j (show j ≤ n+1 by omega)
    · simp only [if_neg hj]
      exact measurable_const
  have ha : Measurable
      (fun ω => nativeCarryAnchor (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E n) := by
    have hh := (measurable_nativeCarryAnchor (fun j => (j : ℝ))
      (fun i j hij => by change (i : ℝ) < (j : ℝ); exact_mod_cast hij) E n).comp hpath
    convert hh using 1
    funext ω
    apply nativeCarryAnchor_prefix_congr
    intro j hj
    exact (if_pos hj).symm
  exact (hsample (n+1) le_rfl).sub ha

/-- The actual state is measurable at the original extended recording clock. -/
theorem nativeRestartRecordingState_measurable_stopped
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable[(nativeRecordingTime_isStoppingTime_increment X hX E k).measurableSpace]
      (nativeRestartRecordingState X E k) := by
  apply measurable_stoppedValue
    ((show StronglyAdapted (incrementFiltration X hX) (nativeRestartObservedState X E) from
      fun n => (nativeRestartObservedState_adapted hX E n).stronglyMeasurable).isStronglyProgressive_of_discrete)

theorem nativeRestartRecordingState_measurable
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (nativeRestartRecordingState X E k) :=
  (nativeRestartRecordingState_measurable_stopped hX E k).mono
    (nativeRecordingTime_isStoppingTime_increment X hX E k).measurableSpace_le le_rfl

theorem nativeRestartRecordingState_initial_law
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (E : ℝ) :
    μ.map (nativeRestartRecordingState X E 0) = gaussianReal 0 1 := by
  rw [nativeRestartRecordingState_zero, hG]

end SwingRepair
