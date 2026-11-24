import PLAStochastic.Index.CEPS.Final.EndpointInputs

/-! # The drift integrand of the low-band coefficient `Ĝ_j`

`cepsKernelPairIntegrand G j q lam z = Σ_{a+n=j} D_a(q,z) · P̃_n(q,lam,z)` combines the marked
discount scale coefficients with the glued pair coefficients. It is jointly analytic in `(q, z)`
on the polydisc times the strip for every drift, with a product envelope.
-/

noncomputable section
open Complex Metric Set Filter Topology Finset
namespace PGM

/-- The glued drift integrand of `Ĝ_j`. -/
def cepsKernelPairIntegrand {d N : ℕ} (G : CepsGlueData d N) (j : ℕ) (q : Fin d → ℂ) (lam : ℝ)
    (z : ℂ) : ℂ :=
  ∑ x ∈ antidiagonal j, cepsKernelDiscountCoeffC d j x.1 q z *
    cepsGluedPairCoeff d N x.2 G.H G.lc G.zc q lam z

namespace CepsGlueData

variable {d N : ℕ} (G : CepsGlueData d N)

/-- Discount scale coefficients: analyticity and a polynomial bound. -/
theorem discount_coeff {j : ℕ} (hD : CepsDiscountBudget d j) :
    ∃ KD δD : ℝ, ∃ eD : ℕ, 0 < δD ∧ 0 ≤ KD ∧ ∀ q ∈ ball G.c₀ G.R, ∀ (z : ℂ) (a : ℕ),
      AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsKernelDiscountCoeffC d j a v.1 v.2) (q, z) ∧
      ‖cepsKernelDiscountCoeffC d j a q z‖ ≤ KD * (4 / δD) ^ a * (1 + ‖z‖) ^ (eD + a) := by
  obtain ⟨δb, K, e, hδb, hB⟩ := hD (‖G.c₀‖ + G.R) (by linarith [norm_nonneg G.c₀, G.hR])
  refine ⟨|K|, δb, e, hδb, abs_nonneg K, fun q hq z a => ?_⟩
  have hq' : ‖q‖ ≤ ‖G.c₀‖ + G.R := by
    linarith [norm_le_insert' q G.c₀, (mem_ball_iff_norm.mp hq).le]
  have h := cepsScaleCoeff_of_sqrt_family (F := fun q z b =>
      -cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d q) j 0 z b (b * z))
    (q := q) (z := z) hδb (fun b hb => hB q hq' z b hb) a
  refine ⟨h.1, h.2.trans ?_⟩
  have hs := one_add_sqrt_le ‖z‖ (norm_nonneg z)
  have h1 : 0 ≤ 1 + Real.sqrt ‖z‖ := by positivity
  have h2 : (2 * (1 + Real.sqrt ‖z‖) / δb) ^ a ≤ (4 / δb) ^ a * (1 + ‖z‖) ^ a := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδb]
    linarith
  calc K * (1 + ‖z‖) ^ e * (2 * (1 + Real.sqrt ‖z‖) / δb) ^ a
      ≤ |K| * (1 + ‖z‖) ^ e * ((4 / δb) ^ a * (1 + ‖z‖) ^ a) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)) h2
          (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The drift envelope of the glued integrand. -/
def integrandEnvelope (j : ℕ) (KD δD : ℝ) (lam : ℝ) : ℝ :=
  ∑ x ∈ antidiagonal j, KD * (4 / δD) ^ x.1 * G.gluedEnvelope x.2 lam

theorem integrandEnvelope_integrable (j : ℕ) (KD δD : ℝ) :
    MeasureTheory.Integrable (G.integrandEnvelope j KD δD) := by
  unfold integrandEnvelope
  exact MeasureTheory.integrable_finsetSum _ fun x _ => (G.gluedEnvelope_integrable x.2).const_mul _

theorem integrand_analyticAt {j : ℕ} (hj : j + 1 ≤ N) (hD : CepsDiscountBudget d j)
    {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) (lam : ℝ) {z : ℂ} (hz : -G.δ < z.re) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsKernelPairIntegrand G j v.1 lam v.2) (q, z) := by
  obtain ⟨KD, δD, eD, -, -, hDc⟩ := G.discount_coeff hD
  unfold cepsKernelPairIntegrand
  refine Finset.analyticAt_fun_sum _ fun x hx => (hDc q hq z x.1).1.mul ?_
  have hn : x.2 ≤ N := by have := (mem_antidiagonal.mp hx); omega
  exact G.glued_analyticAt hn hq lam hz

theorem integrand_norm_le {j : ℕ} (hD : CepsDiscountBudget d j) (hMH : 0 ≤ G.MH) :
    ∃ KD δD : ℝ, ∃ eD : ℕ, 0 < δD ∧ 0 ≤ KD ∧ ∀ q ∈ ball G.c₀ G.R, ∀ (lam : ℝ) (z : ℂ),
      -G.δ ≤ z.re →
      ‖cepsKernelPairIntegrand G j q lam z‖ ≤ G.integrandEnvelope j KD δD lam *
        ((1 + ‖z‖) ^ (eD + G.e + j) * Real.exp (-G.c * Real.sqrt ‖z‖)) := by
  obtain ⟨KD, δD, eD, hδD, hKD, hDc⟩ := G.discount_coeff hD
  refine ⟨KD, δD, eD, hδD, hKD, fun q hq lam z hz => ?_⟩
  unfold cepsKernelPairIntegrand integrandEnvelope
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hx' := mem_antidiagonal.mp hx
  have hDn := (hDc q hq z x.1).2
  have hGn := G.glued_norm_le (n := x.2) hq lam hz hMH
  have hE : 0 ≤ G.gluedEnvelope x.2 lam := G.gluedEnvelope_nonneg x.2 lam hMH
  rw [norm_mul]
  calc ‖cepsKernelDiscountCoeffC d j x.1 q z‖ * ‖cepsGluedPairCoeff d N x.2 G.H G.lc G.zc q lam z‖
      ≤ (KD * (4 / δD) ^ x.1 * (1 + ‖z‖) ^ (eD + x.1)) *
        (G.gluedEnvelope x.2 lam * ((1 + ‖z‖) ^ (G.e + x.2) *
          Real.exp (-G.c * Real.sqrt ‖z‖))) :=
        mul_le_mul hDn hGn (norm_nonneg _) (by positivity)
    _ = _ := by
        rw [show eD + G.e + j = (eD + x.1) + (G.e + x.2) by omega, pow_add]
        ring

end CepsGlueData

end PGM
