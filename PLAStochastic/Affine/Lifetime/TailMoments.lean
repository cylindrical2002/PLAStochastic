import PLAStochastic.Affine.Lifetime.UnitMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Real-order tail moments of the Brownian lifetimes

The layer-cake identity is converted to finite Bochner integrals using the proved
moment integrability. Strict tails of the real representative agree with those of
the original extended lifetime by almost-sure finiteness; no atomlessness is used.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The real tail-moment identity, together with integrability of its survival integrand. -/
theorem integrable_rpow_tail_identity [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hX₀ : 0 ≤ᵐ[μ] X) {p : ℝ} (hp : 0 < p)
    (hpow : Integrable (fun ω => X ω ^ p) μ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * μ.real {ω | t < X ω}) (Ioi 0) ∧
      (∫ ω, X ω ^ p ∂μ) =
        p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * μ.real {ω | t < X ω} := by
  let P : ℝ → ℝ≥0∞ := fun t => μ {ω | t < X ω} * ENNReal.ofReal (t ^ (p - 1))
  have hP : Measurable P :=
    (measurable_tail_measure μ X).mul ((by fun_prop :
      Measurable (fun t : ℝ => t ^ (p - 1))).ennreal_ofReal)
  have hPfin : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t < ∞ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top
  have hpow₀ : 0 ≤ᵐ[μ] (fun ω => X ω ^ p) :=
    hX₀.mono fun _ hx => Real.rpow_nonneg hx _
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ hX₀ hX hp
  have hleft : ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hpow.aestronglyMeasurable hpow₀).mpr hpow
  rw [hlayer] at hleft
  have hright : ∫⁻ t in Ioi (0 : ℝ), P t ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right hleft (by positivity)).ne
  have hint := integrable_toReal_of_lintegral_ne_top hP.aemeasurable hright
  have hrewrite : (fun t => (P t).toReal) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => t ^ (p - 1) * μ.real {ω | t < X ω}) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    simp only [P, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _),
      Measure.real]
    ring
  have hreal := congrArg ENNReal.toReal hlayer
  rw [← integral_eq_lintegral_of_nonneg_ae hpow₀ hpow.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le,
    ← integral_toReal hP.aemeasurable hPfin] at hreal
  rw [integral_congr_ae hrewrite] at hreal
  exact ⟨hint.congr hrewrite, hreal⟩

/-- Outside the finite-value exceptional set, all nonnegative strict tails agree at once. -/
theorem toReal_strict_tails_ae {X : Ω → ℝ≥0∞}
    (hfinite : ∀ᵐ ω ∂μ, X ω ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → (t < (X ω).toReal ↔ ENNReal.ofReal t < X ω) := by
  filter_upwards [hfinite] with ω hω
  intro t ht
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht hω).symm

/-- A real representative recovers the original extended random variable almost surely. -/
theorem ofReal_toReal_ae_eq_of_finite {X : Ω → ℝ≥0∞}
    (hfinite : ∀ᵐ ω ∂μ, X ω ≠ ∞) :
    (fun ω => ENNReal.ofReal (X ω).toReal) =ᵐ[μ] X :=
  hfinite.mono fun _ hω => ENNReal.ofReal_toReal hω

/-- Equality of strict-tail probabilities needs finiteness, but no restriction on atoms. -/
theorem measure_strict_tail_toReal_eq {X : Ω → ℝ≥0∞}
    (hfinite : ∀ᵐ ω ∂μ, X ω ≠ ∞) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < (X ω).toReal} = μ {ω | ENNReal.ofReal t < X ω} := by
  apply measure_congr
  filter_upwards [toReal_strict_tails_ae hfinite] with ω hω
  exact propext (hω t ht)

variable {B : ℝ≥0 → Ω → ℝ}

theorem anchoredUnitLifetime_strict_tails_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
      (t < anchoredUnitLifetime B ω ↔ ENNReal.ofReal t < anchoredProcessLifetime B 1 ω) :=
  toReal_strict_tails_ae (anchoredProcessLifetime_ae_ne_top hB)

theorem ofReal_anchoredUnitLifetime_ae_eq (hB : IsBrownianReal B μ) :
    (fun ω => ENNReal.ofReal (anchoredUnitLifetime B ω)) =ᵐ[μ] anchoredProcessLifetime B 1 :=
  ofReal_toReal_ae_eq_of_finite (anchoredProcessLifetime_ae_ne_top hB)

theorem anchoredUnitLifetime_strict_tail_probability (hB : IsBrownianReal B μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < anchoredUnitLifetime B ω} = μ {ω | ENNReal.ofReal t < anchoredProcessLifetime B 1 ω} :=
  measure_strict_tail_toReal_eq (anchoredProcessLifetime_ae_ne_top hB) ht

/-- The survival integrand in the paper's real-order moment formula is integrable. -/
theorem anchoredUnitLifetime_tail_weight_integrable (hB : IsBrownianReal B μ)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * μ.real {ω | t < anchoredUnitLifetime B ω}) (Ioi 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_rpow_tail_identity (aemeasurable_anchoredUnitLifetime hB)
    (Eventually.of_forall (anchoredUnitLifetime_nonnegative B)) hp
    (anchoredUnitLifetime_integrable_rpow hB hp.le)).1

/-- The paper's tail-moment identity holds for every real order `p > 0`. -/
theorem anchoredUnitLifetime_tail_moment (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, anchoredUnitLifetime B ω ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * μ.real {ω | t < anchoredUnitLifetime B ω} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_rpow_tail_identity (aemeasurable_anchoredUnitLifetime hB)
    (Eventually.of_forall (anchoredUnitLifetime_nonnegative B)) hp
    (anchoredUnitLifetime_integrable_rpow hB hp.le)).2

/-- The same formula uses strict tails of the original extended Brownian lifetime. -/
theorem anchoredProcessLifetime_tail_moment (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, anchoredUnitLifetime B ω ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) *
        μ.real {ω | ENNReal.ofReal t < anchoredProcessLifetime B 1 ω} := by
  rw [anchoredUnitLifetime_tail_moment hB hp]
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  rw [Measure.real, Measure.real, anchoredUnitLifetime_strict_tail_probability hB ht.le]

theorem optimalUnitLifetime_strict_tails_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
      (t < optimalUnitLifetime B ω ↔ ENNReal.ofReal t < optimalProcessLifetime B 1 ω) :=
  toReal_strict_tails_ae (optimalProcessLifetime_ae_ne_top hB)

theorem ofReal_optimalUnitLifetime_ae_eq (hB : IsBrownianReal B μ) :
    (fun ω => ENNReal.ofReal (optimalUnitLifetime B ω)) =ᵐ[μ] optimalProcessLifetime B 1 :=
  ofReal_toReal_ae_eq_of_finite (optimalProcessLifetime_ae_ne_top hB)

theorem optimalUnitLifetime_strict_tail_probability (hB : IsBrownianReal B μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < optimalUnitLifetime B ω} = μ {ω | ENNReal.ofReal t < optimalProcessLifetime B 1 ω} :=
  measure_strict_tail_toReal_eq (optimalProcessLifetime_ae_ne_top hB) ht

/-- The survival integrand in the paper's real-order moment formula is integrable. -/
theorem optimalUnitLifetime_tail_weight_integrable (hB : IsBrownianReal B μ)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * μ.real {ω | t < optimalUnitLifetime B ω}) (Ioi 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_rpow_tail_identity (aemeasurable_optimalUnitLifetime hB)
    (Eventually.of_forall (optimalUnitLifetime_nonnegative B)) hp
    (optimalUnitLifetime_integrable_rpow hB hp.le)).1

/-- The paper's tail-moment identity holds for every real order `p > 0`. -/
theorem optimalUnitLifetime_tail_moment (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, optimalUnitLifetime B ω ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * μ.real {ω | t < optimalUnitLifetime B ω} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_rpow_tail_identity (aemeasurable_optimalUnitLifetime hB)
    (Eventually.of_forall (optimalUnitLifetime_nonnegative B)) hp
    (optimalUnitLifetime_integrable_rpow hB hp.le)).2

/-- The same formula uses strict tails of the original extended Brownian lifetime. -/
theorem optimalProcessLifetime_tail_moment (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, optimalUnitLifetime B ω ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) *
        μ.real {ω | ENNReal.ofReal t < optimalProcessLifetime B 1 ω} := by
  rw [optimalUnitLifetime_tail_moment hB hp]
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  rw [Measure.real, Measure.real, optimalUnitLifetime_strict_tail_probability hB ht.le]

end BrownianAffine
