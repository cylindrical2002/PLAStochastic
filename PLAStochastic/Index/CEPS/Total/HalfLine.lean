import PLAStochastic.Index.CEPS.Total.DrawupAlgebra
import PLAStochastic.Index.CEPS.Normal.ActualHalfLineIdentity
import PLAStochastic.Index.CEPS.Scaled.EndpointPhysical
import PLAStochastic.Index.CEPS.Scaled.RootCoercivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# WP10: the half-line integral on `[b, δ]` (P12) and its endpoints

For a nonzero imaginary mark `t` the marked half-line primitive
`P(μ) = 𝒦_t/(β₊ - t) = cepsNormalHalfPrimitive …` has derivative the half-line pair
`J^∞_t(μ)` at every `μ ∈ [b, δ] ⊂ (0, μ₀/4)` (WP5 `actual_halfPair_marked_original`: there the
two roots are separate since `r₊ ≠ 0` for `μ > 0`, and `d_t ≠ 0`). Hence
`∫_{[b,δ]} J^∞ = P(δ) - P(b)` whenever `J^∞` is integrable (`halfLine_integral_eq`), and
`d_t P(μ) = 𝒜_μ(t) e^{-(β₊-t) l}` (`d_mul_halfPrimitive`).
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The marked half-line primitive `P(μ) = 𝒦_t/(β₊ - t)` as a function of the real drift. -/
def cepsHalfPrimitiveMarked (D θ : ℝ) (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (t w : ℂ) (μ : ℝ) : ℂ :=
  cepsNormalHalfPrimitive (cepsCgf ρW) (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
    (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) μ (t * (1 + (μ : ℂ))) t w

include hW hθ hD in
/-- For positive drift the two roots are distinct. -/
theorem marked_nonmerge {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hμ0 : 0 < μ) {q : ℂ} (hre : 0 ≤ q.re) :
    q - cepsMorseMin D θ ρW μ ≠ 0 := by
  have h := cepsRootR_norm_ge_drift dom hW hθ hD hμ hre
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hpos : 0 < Real.sqrt (cepsVarLo D) / (3 * v) * |μ| := by
    have := Real.sqrt_pos.mpr (cepsVarLo_pos hD)
    have := abs_pos.mpr hμ0.ne'
    positivity
  intro h0
  have hr : cepsRootR D θ ρW μ q = 0 := by
    have hsq := cepsRootR_sq D θ ρW μ q
    rw [h0] at hsq
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  rw [hr, norm_zero] at h
  linarith

include hW hθ hD in
/-- (P12) on `[b, δ]`: the half-line pair is the derivative of the marked primitive. -/
theorem hasDerivAt_halfPrimitiveMarked {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η) {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ < dom.μ₀ / 4)
    {t : ℂ} (ht0 : t.re = 0) (ht : t ≠ 0) (htq : ‖t‖ * (1 + μ) < dom.q₀ / 4)
    (htu : t ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) (w : ℂ) :
    HasDerivAt (cepsHalfPrimitiveMarked D θ dom ρW t w)
      (cepsNormalHalfPair (cepsNormalData D θ ρW) (dom.canonL ρW) μ t w) μ := by
  have habs : |μ| < dom.μ₀ / 4 := by rwa [abs_of_pos hμ0]
  have hq : ‖t * (1 + (μ : ℂ))‖ < dom.q₀ / 4 := by
    rw [norm_mul, show (1 + (μ : ℂ)) = ((1 + μ : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact htq
  have hre : 0 ≤ (t * (1 + (μ : ℂ))).re := by
    have : (t * (1 + (μ : ℂ))).re = t.re * (1 + μ) := by simp [mul_re]
    rw [this, ht0, zero_mul]
  have hc0 := dom.c₀_pos
  have hμ₀ := dom.μ₀_pos
  have hne := marked_nonmerge dom hW hθ hD (μ := μ) (by rw [abs_of_pos hμ0]; linarith) hμ0 hre
  have hd0 : cepsD ρW μ (t * (1 + (μ : ℂ))) t ≠ 0 := by
    rw [cepsD_marked_eq]; exact cepsMarkedDiscount_ne_zero_on_unit hW hθ hD ht htu
  exact dom.actual_halfPair_marked_original hW hθ hD hf hm hη habs hq hre (by rw [ht0]; exact hc0)
    hne hd0

include hW hθ hD in
/-- **(P12) integrated over `[b, δ]`.** -/
theorem halfLine_integral_eq {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η) {b δ : ℝ} (hb : 0 < b) (hbδ : b ≤ δ)
    (hδ : δ < dom.μ₀ / 4) {t : ℂ} (ht0 : t.re = 0) (ht : t ≠ 0)
    (htq : ‖t‖ * (1 + δ) < dom.q₀ / 4) (htu : t ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ))
    (w : ℂ)
    (hint : IntegrableOn (fun μ : ℝ => cepsNormalHalfPair (cepsNormalData D θ ρW)
      (dom.canonL ρW) μ t w) (Icc b δ)) :
    ∫ μ in Icc b δ, cepsNormalHalfPair (cepsNormalData D θ ρW) (dom.canonL ρW) μ t w =
      cepsHalfPrimitiveMarked D θ dom ρW t w δ - cepsHalfPrimitiveMarked D θ dom ρW t w b := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbδ]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
  · rw [uIcc_of_le hbδ] at hx
    have ht1 : ‖t‖ * (1 + x) < dom.q₀ / 4 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith [hx.2]) (norm_nonneg t)) htq
    exact hasDerivAt_halfPrimitiveMarked dom hW hθ hD hf hm hη (by linarith [hx.1])
      (by linarith [hx.2]) ht0 ht ht1 htu w
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hbδ).mpr hint

include hW hθ hD in
/-- The endpoint values: `d_t P(μ) = 𝒜_μ(t) e^{-(β₊-t) w(1+μ)}`. -/
theorem d_mul_halfPrimitive {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {t : ℂ}
    (hq : ‖t * (1 + (μ : ℂ))‖ ≤ dom.q₀) (hd : cepsMarkedDiscount ρW t ≠ 0) (w : ℂ) :
    cepsMarkedDiscount ρW t * cepsHalfPrimitiveMarked D θ dom ρW t w μ =
      (cepsNormalData D θ ρW μ (t * (1 + (μ : ℂ)))).amplitude (dom.canonL ρW) μ
          (t * (1 + (μ : ℂ))) t *
        exp (-(cepsRootPlus D θ ρW μ (t * (1 + (μ : ℂ))) - t) * (w * (1 + (μ : ℂ)))) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hx := dom.mem_SPRegion hW hθ hD hμ' hq
  unfold cepsHalfPrimitiveMarked
  rw [dom.actual_halfPrimitive_eq_amplitude hW hθ hD hx, cepsD_marked_eq]
  field_simp

end PGM
