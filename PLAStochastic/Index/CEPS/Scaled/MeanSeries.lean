import PLAStochastic.Index.CEPS.Scaled.ZeroEndpointTaylor
import PLAStochastic.Index.CEPS.Scaled.PairIntegralSeries
import PLAStochastic.Index.CEPS.Scaled.NormalZeroFrequencyTaylor

/-! # Finite scale series for the genuine normal slope at zero frequency

The coefficients are genuine endpoint and Bochner-integral coefficients. This
module does not assert that the integral coefficients have a finite jet representation.
-/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsScaledMeanSeries {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) : PowerSeries ℂ :=
  complexTaylorSeries (cepsScaledSurrogateZeroEndpoint dom ρW N) 0 +
    cepsScaledPairIntegralSeries dom ρW N 0

def CepsCanonDomain.zeroEndpointSeriesBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  complexTaylorBudgetConstant N dom.zeroEndpointScaleRadius (dom.zeroEndpointPolynomialBound N M) +
    8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀

def CepsCanonDomain.meanSeriesScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.zeroEndpointScaleRadius / 2) (dom.pairIntegralTaylorScaleBase N M)

def CepsCanonDomain.meanSeriesBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  dom.zeroEndpointSeriesBudgetConstant N M + dom.pairIntegralSeriesBudgetConstant N M δ

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem meanSeriesScaleBase_pos (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.meanSeriesScaleBase N M :=
  lt_min (half_pos (zeroEndpointScaleRadius_pos dom))
    (pairIntegralTaylorScaleBase_pos dom hW hθ hD N hM)

include hW hθ hD in
theorem cepsScaledZeroEndpoint_seriesApprox {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {b : ℝ} (hb : 0 ≤ b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.zeroEndpointScaleRadius / 2)) :
    SeriesApprox (cepsScaledZeroEndpoint dom ρW b)
      (complexTaylorSeries (cepsScaledSurrogateZeroEndpoint dom ρW N) 0) N b
      (dom.zeroEndpointSeriesBudgetConstant N M) := by
  have hR := zeroEndpointScaleRadius_pos dom
  have hB := cepsScaledSurrogateZeroEndpoint_budget dom hW hθ hD hf hη hM N (by omega)
  have hK : 0 ≤ dom.zeroEndpointPolynomialBound N M :=
    (norm_nonneg _).trans (hB 0 (mem_ball_self hR))
  have hS := seriesApprox_of_polynomial_disc
    (f := cepsScaledSurrogateZeroEndpoint dom ρW N) hR (le_refl (1 : ℝ)) hK 0 N
    (by simpa using (cepsScaledSurrogateZeroEndpoint_differentiable dom (ρW := ρW) N).differentiableOn)
    (by simpa using hB) hb (by simpa using hbs)
  simp only [one_pow, mul_one] at hS
  have hbR : b < dom.zeroEndpointScaleRadius / 2 := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_nonneg hb] using hbs
  have hbμ : |b| < dom.μ₀ / 4 := by
    rw [abs_of_nonneg hb]
    have hle : dom.zeroEndpointScaleRadius ≤ dom.μ₀ / 8 := min_le_right _ _
    have := dom.μ₀_pos
    linarith
  have hb1 : b ≤ 1 := by
    have hle : dom.zeroEndpointScaleRadius ≤ 1 := min_le_left _ _
    linarith
  have hC : 0 ≤ 8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀ := by
    have := dom.jetC_nonneg hD N
    have := dom.c₀_pos
    have := (cepsSobolev_nonneg m η fW).trans hM
    unfold CepsCanonDomain.canonDriftCoeffBound
    positivity
  apply hS.of_close hC
  have hA := cepsScaledSurrogateZeroEndpoint_approx dom hW hθ hD hf hη hM N hN hbμ
  rw [abs_of_nonneg hb] at hA
  exact hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb hb1 (by omega)) hC)

include hW hθ hD in
theorem cepsScaledTrueNormalSlope_seriesApprox {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    {b : ℝ} (hb : 0 < b) (hbs : b < dom.meanSeriesScaleBase N M) :
    SeriesApprox (-cepsScaledTrueNormalSlope dom ρW b δ)
      (cepsScaledMeanSeries dom ρW N) N b (dom.meanSeriesBudgetConstant N M δ) := by
  have hbE := hbs.trans_le (min_le_left _ _)
  have hbI := hbs.trans_le (min_le_right _ _)
  have hE := cepsScaledZeroEndpoint_seriesApprox dom hW hθ hD hf hη hM N (by omega) hb.le
    (by simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos hb] using hbE)
  have hI := cepsScaledTrueCutoffPair_integral_seriesApprox dom hW hθ hD
    hf hη hM N hN hδ hδactual hb (z := 0) rfl (by simpa using hbI)
  simp only [norm_zero, Real.sqrt_zero, add_zero, one_pow, mul_one] at hI
  rw [show -cepsScaledTrueNormalSlope dom ρW b δ = cepsScaledZeroEndpoint dom ρW b +
    ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ 0 lam by
      unfold cepsScaledTrueNormalSlope; ring]
  exact hE.add hI

end PGM
