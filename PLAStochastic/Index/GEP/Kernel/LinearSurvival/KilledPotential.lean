import PLAStochastic.Index.GEP.Kernel.LinearSurvival.RenewalBound
import PLAStochastic.Index.GEP.StrongApprox.Saddle.Parameters

/-!
# A killed-walk potential with a bounded exponential correction

The potential `d + C - exp(-lam d)`, killed on the negative half-line, absorbs
unbounded positive jumps using an exponential-moment tail. This avoids imposing
a bounded overshoot on either sign of the centered increment.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The raw concave potential, before killing. -/
def linearSurvivalPotentialRaw (C lam d : ℝ) : ℝ := d + C - Real.exp (-lam * d)

/-- The potential killed outside the nonnegative half-line. -/
def linearSurvivalPotential (C lam : ℝ) : ℝ → ℝ :=
  (Ici 0).indicator (linearSurvivalPotentialRaw C lam)

theorem measurable_linearSurvivalPotential (C lam : ℝ) :
    Measurable (linearSurvivalPotential C lam) := by
  unfold linearSurvivalPotential linearSurvivalPotentialRaw
  exact (by fun_prop : Measurable (fun d : ℝ => d + C - Real.exp (-lam * d))).indicator measurableSet_Ici

theorem linearSurvivalPotential_of_nonneg (C lam : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    linearSurvivalPotential C lam d = d + C - Real.exp (-lam * d) :=
  indicator_of_mem hd _

theorem linearSurvivalPotential_nonneg {C lam : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (d : ℝ) :
    0 ≤ linearSurvivalPotential C lam d := by
  by_cases hd : 0 ≤ d
  · rw [linearSurvivalPotential_of_nonneg C lam hd]
    have he := Real.exp_le_one_iff.2 (show -lam * d ≤ 0 by nlinarith)
    linarith
  · simp [linearSurvivalPotential, hd]

theorem linearSurvivalPotential_ge {C lam d : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (hd : 0 ≤ d) :
    d ≤ linearSurvivalPotential C lam d := by
  rw [linearSurvivalPotential_of_nonneg C lam hd]
  have he := Real.exp_le_one_iff.2 (show -lam * d ≤ 0 by nlinarith)
  linarith

theorem linearSurvivalPotential_le {C lam : ℝ} (hC : 0 ≤ C) (d : ℝ) :
    linearSurvivalPotential C lam d ≤ |d| + C := by
  by_cases hd : 0 ≤ d
  · rw [linearSurvivalPotential_of_nonneg C lam hd, abs_of_nonneg hd]
    linarith [Real.exp_pos (-lam * d)]
  · simp only [linearSurvivalPotential, indicator_of_notMem (show d ∉ Ici 0 from hd)]
    positivity

/-- The cost of killing is paid entirely by a fixed exponential tail. -/
theorem linearSurvivalPotential_kill_error {C lam R d : ℝ}
    (hlam : 0 ≤ lam) (hR : 0 ≤ R) (hC : R + Real.exp (lam * R) ≤ C) (hd : 0 ≤ d) (y : ℝ) :
    linearSurvivalPotential C lam (d - y) ≤ linearSurvivalPotentialRaw C lam (d - y) +
      Real.exp (-lam * d) * (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y := by
  have hC0 : 0 ≤ C := by linarith [Real.exp_pos (lam * R)]
  have htail : 0 ≤ (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y := by
    by_cases hy : R < y
    · rw [indicator_of_mem (show y ∈ Ioi R from hy)]
      exact mul_nonneg (by linarith) (Real.exp_pos _).le
    · rw [indicator_of_notMem (show y ∉ Ioi R from hy)]
  by_cases hy : y ≤ d
  · rw [linearSurvivalPotential_of_nonneg C lam (by linarith)]
    unfold linearSurvivalPotentialRaw
    exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le htail)
  · rw [show linearSurvivalPotential C lam (d - y) = 0 by
      exact indicator_of_notMem (show d - y ∉ Ici 0 by change ¬0 ≤ d - y; linarith) _]
    by_cases hyR : y ≤ R
    · have hexp : Real.exp (-lam * (d - y)) ≤ Real.exp (lam * R) :=
        Real.exp_le_exp.2 (by nlinarith)
      unfold linearSurvivalPotentialRaw
      nlinarith [mul_nonneg (Real.exp_pos (-lam * d)).le htail]
    · have hRy : R < y := lt_of_not_ge hyR
      rw [indicator_of_mem (show y ∈ Ioi R from hRy)]
      have hexp : 1 ≤ Real.exp (lam * (y - d)) :=
        Real.one_le_exp_iff.2 (by nlinarith)
      have hy0 : 0 ≤ y := hR.trans hRy.le
      have hye := mul_le_mul_of_nonneg_left hexp hy0
      have he : Real.exp (-lam * d) * Real.exp (lam * y) = Real.exp (lam * (y - d)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have he' : Real.exp (-lam * (d - y)) = Real.exp (lam * (y - d)) := by
        congr 1
        ring
      unfold linearSurvivalPotentialRaw
      rw [he']
      have he'' : Real.exp (-lam * d) * ((y + 1) * Real.exp (lam * y)) =
          (y + 1) * Real.exp (lam * (y - d)) := by rw [← he]; ring
      rw [he'']
      nlinarith

/-- The killed potential is integrable under any integrable increment. -/
theorem integrable_linearSurvivalPotential_shift (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (d : ℝ) :
    Integrable (fun y => linearSurvivalPotential C lam (d - y)) (μ : Measure ℝ) := by
  apply (((integrable_const d).sub hi).abs.add (integrable_const C)).mono'
    (((measurable_linearSurvivalPotential C lam).comp (by fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ fun y => by
    change ‖linearSurvivalPotential C lam (d - y)‖ ≤ |d - y| + C
    rw [Real.norm_eq_abs, abs_of_nonneg (linearSurvivalPotential_nonneg hC hlam _)]
    exact linearSurvivalPotential_le (by linarith) _

/-- **Killed potential inequality.** A centered or slightly negatively drifting
increment has a controlled first moment on surviving paths. The tail condition
is precisely the gap consumed by the killing correction. -/
theorem linearSurvivalPotential_step (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam R ρ : ℝ} (hC1 : 1 ≤ C) (hlam : 0 ≤ lam) (hR : 0 ≤ R)
    (hC : R + Real.exp (lam * R) ≤ C)
    (he : Integrable (fun y => Real.exp (lam * y)) (μ : Measure ℝ))
    (ht : Integrable ((Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y))) (μ : Measure ℝ))
    (hm : (∫ y : ℝ, y ∂(μ : Measure ℝ)) = -ρ)
    (hgap : 1 + (∫ y, (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y ∂(μ : Measure ℝ)) ≤
      ∫ y, Real.exp (lam * y) ∂(μ : Measure ℝ))
    {d : ℝ} (hd : 0 ≤ d) :
    (∫ y, linearSurvivalPotential C lam (d - y) ∂(μ : Measure ℝ)) ≤
      linearSurvivalPotential C lam d + ρ := by
  have hiRaw : Integrable (fun y => linearSurvivalPotentialRaw C lam (d - y)) (μ : Measure ℝ) := by
    have heq : (fun y => linearSurvivalPotentialRaw C lam (d - y)) =
        fun y => d - y + C - Real.exp (-lam * d) * Real.exp (lam * y) := by
      funext y
      unfold linearSurvivalPotentialRaw
      rw [show -lam * (d - y) = -lam * d + lam * y by ring, Real.exp_add]
    rw [heq]
    exact (((integrable_const d).sub hi).add (integrable_const C)).sub (he.const_mul _)
  have hb := integral_mono (integrable_linearSurvivalPotential_shift μ hi hC1 hlam d)
    (hiRaw.add (ht.const_mul (Real.exp (-lam * d))))
    (linearSurvivalPotential_kill_error hlam hR hC hd)
  simp only [Pi.add_apply] at hb
  rw [integral_add hiRaw (ht.const_mul _), integral_const_mul] at hb
  have hraw : (∫ y, linearSurvivalPotentialRaw C lam (d - y) ∂(μ : Measure ℝ)) =
      d + ρ + C - Real.exp (-lam * d) * (∫ y, Real.exp (lam * y) ∂(μ : Measure ℝ)) := by
    have heq : (fun y => linearSurvivalPotentialRaw C lam (d - y)) =
        fun y => d - y + C - Real.exp (-lam * d) * Real.exp (lam * y) := by
      funext y
      unfold linearSurvivalPotentialRaw
      rw [show -lam * (d - y) = -lam * d + lam * y by ring, Real.exp_add]
    have hlin : Integrable (fun y : ℝ => d - y) (μ : Measure ℝ) := (integrable_const d).sub hi
    have hlinC : Integrable (fun y : ℝ => d - y + C) (μ : Measure ℝ) := hlin.add (integrable_const C)
    rw [heq, integral_sub hlinC (he.const_mul _), integral_add hlin (integrable_const C),
      integral_sub (integrable_const d) hi, integral_const_mul, hm]
    simp
  rw [hraw] at hb
  rw [linearSurvivalPotential_of_nonneg C lam hd]
  have hg := mul_le_mul_of_nonneg_left hgap (Real.exp_pos (-lam * d)).le
  linarith

end

end PGM
