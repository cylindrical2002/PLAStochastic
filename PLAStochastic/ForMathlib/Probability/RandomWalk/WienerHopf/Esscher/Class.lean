import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Measure
import PLAStochastic.ForMathlib.Analysis.Fourier.WeightedRemainder

/-!
# Explicit envelope and moment constants for an Esscher step law

For `q ≥ 0` and `|β| ≤ θ / 2`, a centred step law with envelope
`D exp (-θ |y|)` tilts to a drifted law with envelope
`D exp (-(θ / 2) |y|)` and raw second moment at most `256 D / θ³`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM.WienerHopf

namespace IsStepLaw

variable {ρ : Measure ℝ} {f : ℝ → ℝ} {D θ v : ℝ}

theorem integrable_exp_of_abs_lt (h : IsStepLaw ρ f D θ v) (hD : 0 ≤ D)
    {t : ℝ} (ht : |t| < θ) : Integrable (fun y => Real.exp (t * y)) ρ := by
  have hf := h.measurable
  have hi : Integrable (fun y => f y * Real.exp (t * y)) := by
    refine ((PGM.integrable_exp_neg_abs (sub_pos.mpr ht)).const_mul D).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (h.nonneg y) (Real.exp_pos _).le)]
    calc f y * Real.exp (t * y) ≤
        D * Real.exp (-θ * |y|) * Real.exp (t * y) :=
      mul_le_mul_of_nonneg_right (h.le_exp y) (Real.exp_pos _).le
    _ = D * Real.exp (-θ * |y| + t * y) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ D * Real.exp (-(θ - |t|) * |y|) := by
      gcongr
      have hh : t * y ≤ |t| * |y| := by rw [← abs_mul]; exact le_abs_self _
      nlinarith
  rw [h.eq_withDensity, integrable_withDensity_iff_integrable_smul₀'
    h.measurable.ennreal_ofReal.aemeasurable (Filter.Eventually.of_forall
      fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (h.nonneg _), smul_eq_mul] using hi

theorem mem_interior_integrableExpSet (h : IsStepLaw ρ f D θ v) (hD : 0 ≤ D)
    {t : ℝ} (ht : |t| < θ) : t ∈ interior (integrableExpSet id ρ) := by
  exact interior_maximal (fun s hs => h.integrable_exp_of_abs_lt hD
    (abs_lt.mpr hs)) isOpen_Ioo (abs_lt.mp ht)

/-- Tilting changes the mean, while preserving explicit exponential and moment
budgets on the half-width of the original exponential strip. -/
theorem esscher (h : IsStepLaw ρ f D θ v) (hD : 0 ≤ D) (hθ : 0 < θ)
    {β q : ℝ} (hβ : |β| ≤ θ / 2) (hq : 0 ≤ q)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    IsDriftedStepLaw (esscherLaw ρ β) (fun y => Real.exp (β * y - q) * f y)
      D (θ / 2) (deriv (cgf id ρ) β) (256 * D / θ ^ 3) := by
  have := h.isProbabilityMeasure
  have hf := h.measurable
  have hβlt : |β| < θ := by linarith
  have hβi := h.integrable_exp_of_abs_lt hD hβlt
  have hsq : Integrable (fun y => Real.exp (β * y) * y ^ 2) ρ := by
    refine (h.integral_sq_mul_exp_le hθ hD).1.mono' (by fun_prop)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hh : β * y ≤ θ / 2 * |y| :=
      (le_abs_self (β * y)).trans (by rw [abs_mul]; gcongr)
    calc Real.exp (β * y) * y ^ 2 ≤ Real.exp (θ / 2 * |y|) * y ^ 2 := by gcongr
    _ = _ := mul_comm _ _
  have hsqtilt : Integrable (fun y => y ^ 2) (esscherLaw ρ β) :=
    (integrable_tilted_iff hβi _).mpr (by simpa only [smul_eq_mul] using hsq)
  have hsqdisc : Integrable (fun y => Real.exp (β * y - q) * y ^ 2) ρ := by
    simpa only [Real.exp_sub, div_mul_eq_mul_div] using hsq.div_const (Real.exp q)
  refine ⟨isProbabilityMeasure_esscherLaw hβi, esscherLaw_density h.eq_withDensity
    h.measurable hroot, by fun_prop,
    fun y => mul_nonneg (Real.exp_pos _).le (h.nonneg y), ?_, hsqtilt,
    esscherLaw_mean (h.mem_interior_integrableExpSet hD hβlt), ?_⟩
  · intro y
    calc Real.exp (β * y - q) * f y ≤
        Real.exp (β * y - q) * (D * Real.exp (-θ * |y|)) :=
      mul_le_mul_of_nonneg_left (h.le_exp y) (Real.exp_pos _).le
    _ = D * Real.exp (β * y - q - θ * |y|) := by
      rw [show Real.exp (β * y - q) * (D * Real.exp (-θ * |y|)) =
        D * (Real.exp (β * y - q) * Real.exp (-θ * |y|)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ D * Real.exp (-(θ / 2) * |y|) := by
      gcongr
      have hh : β * y ≤ θ / 2 * |y| :=
        (le_abs_self (β * y)).trans (by rw [abs_mul]; gcongr)
      nlinarith
  · rw [integral_esscherLaw hroot]
    simp only [smul_eq_mul]
    calc
      (∫ y, Real.exp (β * y - q) * y ^ 2 ∂ρ) ≤
          ∫ y, y ^ 2 * Real.exp (θ / 2 * |y|) ∂ρ := by
        refine integral_mono hsqdisc (h.integral_sq_mul_exp_le hθ hD).1 ?_
        intro y
        dsimp only
        have hh : β * y ≤ θ / 2 * |y| :=
          (le_abs_self (β * y)).trans (by rw [abs_mul]; gcongr)
        rw [mul_comm (y ^ 2)]
        gcongr
        linarith
      _ ≤ 256 * D / θ ^ 3 := (h.integral_sq_mul_exp_le hθ hD).2

end IsStepLaw

end PGM.WienerHopf
