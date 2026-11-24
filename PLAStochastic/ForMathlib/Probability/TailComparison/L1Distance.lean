import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

/-! # The `L¹` distance of two tail functions

`∫₀^∞ |P(U > t) - P(V > t)| dt ≤ E|U - V|` for nonnegative integrable `U, V`.
The proof squeezes both tails between the tails of the minimum and of the
maximum and applies the layer-cake formula twice.  This converts the already
proved `L¹` continuity of the ladder height into `L¹` continuity of the
equilibrium overshoot density.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The tail function of a nonnegative integrable variable is integrable on the
positive half-line. -/
theorem integrable_meas_gt [IsFiniteMeasure μ] {U : Ω → ℝ} (hU : Integrable U μ)
    (hU0 : 0 ≤ᵐ[μ] U) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < U ω}) (Ioi 0) volume := by
  have hmeas : Measurable (fun t : ℝ => μ.real {ω | t < U ω}) := by
    refine Measurable.ennreal_toReal ?_
    exact Antitone.measurable (fun s t hst => measure_mono (fun ω h => lt_of_le_of_lt hst h))
  refine ⟨hmeas.aestronglyMeasurable.restrict, ?_⟩
  have hfin : (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < U ω}) < ⊤ := by
    rw [← lintegral_eq_lintegral_meas_lt μ hU0 hU.aemeasurable]
    exact hU.lintegral_lt_top
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [Real.enorm_eq_ofReal (by positivity), Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- The tails of two nonnegative integrable variables differ in `L¹` by at most
their `L¹` distance. -/
theorem integral_abs_meas_gt_sub_le [IsFiniteMeasure μ] {U V : Ω → ℝ}
    (hU : Integrable U μ) (hV : Integrable V μ)
    (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω) :
    (∫ t in Ioi (0 : ℝ), |μ.real {ω | t < U ω} - μ.real {ω | t < V ω}|) ≤
      ∫ ω, |U ω - V ω| ∂μ := by
  set P : Ω → ℝ := fun ω => max (U ω) (V ω) with hPdef
  set Q : Ω → ℝ := fun ω => min (U ω) (V ω) with hQdef
  have hP : Integrable P μ := hU.sup hV
  have hQ : Integrable Q μ := hU.inf hV
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => le_trans (hU0 ω) (le_max_left _ _)
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω => le_min (hU0 ω) (hV0 ω)
  have hPint := integrable_meas_gt hP (ae_of_all _ hP0)
  have hQint := integrable_meas_gt hQ (ae_of_all _ hQ0)
  have hdiffint : IntegrableOn
      (fun t : ℝ => μ.real {ω | t < P ω} - μ.real {ω | t < Q ω}) (Ioi 0) volume :=
    hPint.sub hQint
  have habsint : IntegrableOn
      (fun t : ℝ => |μ.real {ω | t < U ω} - μ.real {ω | t < V ω}|) (Ioi 0) volume := by
    have hUint := integrable_meas_gt hU (ae_of_all _ hU0)
    have hVint := integrable_meas_gt hV (ae_of_all _ hV0)
    exact (hUint.sub hVint).abs
  have hpoint : ∀ t : ℝ,
      |μ.real {ω | t < U ω} - μ.real {ω | t < V ω}| ≤
        μ.real {ω | t < P ω} - μ.real {ω | t < Q ω} := by
    intro t
    have hQU : μ.real {ω | t < Q ω} ≤ μ.real {ω | t < U ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      have h : t < Q ω := hω
      show t < U ω
      exact lt_of_lt_of_le h (min_le_left _ _)
    have hQV : μ.real {ω | t < Q ω} ≤ μ.real {ω | t < V ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      have h : t < Q ω := hω
      show t < V ω
      exact lt_of_lt_of_le h (min_le_right _ _)
    have hUP : μ.real {ω | t < U ω} ≤ μ.real {ω | t < P ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      have h : t < U ω := hω
      show t < P ω
      exact lt_of_lt_of_le h (le_max_left _ _)
    have hVP : μ.real {ω | t < V ω} ≤ μ.real {ω | t < P ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      have h : t < V ω := hω
      show t < P ω
      exact lt_of_lt_of_le h (le_max_right _ _)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hmono := setIntegral_mono_on habsint hdiffint measurableSet_Ioi
    (fun t _ => hpoint t)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_sub hPint hQint,
    ← hP.integral_eq_integral_meas_lt (ae_of_all _ hP0),
    ← hQ.integral_eq_integral_meas_lt (ae_of_all _ hQ0), ← integral_sub hP hQ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show max (U ω) (V ω) - min (U ω) (V ω) = |U ω - V ω|
  rcases le_total (U ω) (V ω) with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]

end SwingRepair
