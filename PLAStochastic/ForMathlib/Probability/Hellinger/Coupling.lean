import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureMetric
import PLAStochastic.ForMathlib.Probability.Hellinger.Affinity
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Hellinger budgets from a common submeasure and a common coupling

A common submeasure contributes its full mass to affinity. Two measurable
outputs of the same probability space therefore differ by at most the square
root of twice the probability outside any event where they agree.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α]

theorem rnDeriv_le_rnDeriv_of_finite_le (R P mu : Measure α)
    [IsFiniteMeasure R] [IsFiniteMeasure P] [IsFiniteMeasure mu] (hRP : R ≤ P) :
    R.rnDeriv mu ≤ᵐ[mu] P.rnDeriv mu := by
  have h := Measure.rnDeriv_add (P - R) R mu
  rw [Measure.sub_add_cancel_of_le hRP] at h
  filter_upwards [h] with x hx
  change P.rnDeriv mu x = (P - R).rnDeriv mu x + R.rnDeriv mu x at hx
  rw [hx]
  exact le_add_left le_rfl

theorem measureHellinger_sq_le_common_submeasure (P Q R : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsFiniteMeasure R] (hRP : R ≤ P) (hRQ : R ≤ Q) :
    measureHellinger P Q ^ 2 ≤ 2 * (1 - R.real univ) := by
  let p := HellingerDensity.leftDensity P Q
  let q := HellingerDensity.rightDensity P Q
  have hRmu : R ≪ P + Q := Measure.absolutelyContinuous_of_le
    (hRP.trans (Measure.le_add_right le_rfl))
  have hRi : Integrable (fun x => (R.rnDeriv (P + Q) x).toReal) (P + Q) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := R) (ν := P + Q)
        (s := univ) (measure_ne_top R univ))
  have haff : R.real univ ≤ p.affinity q := by
    rw [← Measure.integral_toReal_rnDeriv hRmu]
    apply integral_mono_ae hRi (p.affinity_integrable q)
    filter_upwards [rnDeriv_le_rnDeriv_of_finite_le R P (P + Q) hRP,
      rnDeriv_le_rnDeriv_of_finite_le R Q (P + Q) hRQ,
      Measure.rnDeriv_lt_top P (P + Q), Measure.rnDeriv_lt_top Q (P + Q)]
      with x hp hq hpfin hqfin
    change (R.rnDeriv (P + Q) x).toReal ≤
      Real.sqrt ((P.rnDeriv (P + Q) x).toReal) *
        Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)
    have hp' := Real.sqrt_le_sqrt (ENNReal.toReal_mono hpfin.ne hp)
    have hq' := Real.sqrt_le_sqrt (ENNReal.toReal_mono hqfin.ne hq)
    calc
      _ = Real.sqrt ((R.rnDeriv (P + Q) x).toReal) *
          Real.sqrt ((R.rnDeriv (P + Q) x).toReal) :=
        (Real.mul_self_sqrt ENNReal.toReal_nonneg).symm
      _ ≤ _ := mul_le_mul hp' hq' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : measureHellinger P Q ^ 2 = 2 - 2 * p.affinity q := by
    change p.hellinger q ^ 2 = _
    exact p.hellinger_sq_eq_affinity q
  rw [hs]
  linarith only [haff]

theorem measureHellinger_coupled_outputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → α}
    (hF : Measurable F) (hG : Measurable G) {s : Set Ω}
    (hs : MeasurableSet s) (heq : ∀ w ∈ s, F w = G w) :
    let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure (P.map G) := Measure.isProbabilityMeasure_map hG.aemeasurable
    measureHellinger (P.map F) (P.map G) ≤ Real.sqrt (2 * P.real sᶜ) := by
  let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (P.map G) := Measure.isProbabilityMeasure_map hG.aemeasurable
  let R := (P.restrict s).map F
  have hR : R = (P.restrict s).map G :=
    Measure.map_congr ((ae_restrict_mem hs).mono fun w hw => heq w hw)
  have hRP : R ≤ P.map F := Measure.map_mono Measure.restrict_le_self hF
  have hRQ : R ≤ P.map G := hR ▸ Measure.map_mono Measure.restrict_le_self hG
  have hmass : R.real univ = P.real s := by
    simp only [R, measureReal_def, Measure.map_apply hF MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hsq := measureHellinger_sq_le_common_submeasure (P.map F) (P.map G) R hRP hRQ
  rw [hmass] at hsq
  have hcompl : 1 - P.real s = P.real sᶜ := by
    rw [measureReal_compl hs, probReal_univ]
  rw [hcompl] at hsq
  have hnon : 0 ≤ 2 * P.real sᶜ := mul_nonneg (by norm_num) measureReal_nonneg
  nlinarith [measureHellinger_nonneg (P.map F) (P.map G), Real.sqrt_nonneg (2 * P.real sᶜ),
    Real.sq_sqrt hnon]

end

end ProbabilityTheory
