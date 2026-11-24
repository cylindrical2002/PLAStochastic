import PLAStochastic.Index.CEPS.Scaled.CanonWeightError
import PLAStochastic.Index.CEPS.Scaled.SurrogateSpatialBudget

/-! # Weighted spatial errors of the actual scaled exponential factor

The true drift remains real. On its physical scale curve, the difference
from the complex-scale surrogate has the same endpoint exponential weight
and the full real-drift vanishing order, including every spatial derivative.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueG {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (lam : ℝ) (z : ℂ) (b : ℝ) (ξ : ℂ) : ℂ :=
  exp (-ξ * (1 + (b : ℂ) * lam)) *
    cepsCanonTrueWeight dom ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) * ξ)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueG_spatial_differentiableOn (N : ℕ) (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableOn ℂ (cepsScaledTrueG dom ρW lam z b)
      (ball 0 (dom.entranceSpatialScaleRadius lam z)) := by
  have hbase : ∀ ξ ∈ ball (0 : ℂ) (dom.entranceSpatialScaleRadius lam z),
      (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖(b : ℂ) * ξ‖ < dom.c₀ / 2 :=
    fun _ hξ => entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb hξ
  have hC : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_right _ _).trans
      (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hb
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz
    (sign := 1) (by norm_num) hC
  have hμD : |b * lam| ≤ dom.μ₀ := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    rw [norm_real, Real.norm_eq_abs] at ht
    linarith [dom.μ₀_pos]
  have hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ :=
    hq.le.trans (half_le_self dom.q₀_pos.le)
  have hmap : MapsTo (fun ξ : ℂ => (b : ℂ) * ξ)
      (ball 0 (dom.entranceSpatialScaleRadius lam z)) (ball 0 (dom.c₀ / 2)) :=
    fun ξ hξ => mem_ball_zero_iff.mpr (hbase ξ hξ).2
  have hWgt := (cepsCanonTrueWeight_spatial_differentiableOn dom hW hθ hD hμD hqD).comp
    (differentiableOn_id.const_mul (b : ℂ)) hmap
  have hE : DifferentiableOn ℂ (fun ξ : ℂ => exp (-ξ * (1 + (b : ℂ) * lam)))
      (ball 0 (dom.entranceSpatialScaleRadius lam z)) := by fun_prop
  simpa only [cepsScaledTrueG, Function.comp_apply] using! hE.mul hWgt

include hW hθ hD in
theorem cepsScaledTrueG_spatial_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) (n : ℕ) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ dom.entranceSpatialScaleRadius lam z / 2) :
    ‖iteratedDeriv n (cepsScaledTrueG dom ρW lam z b) ξ -
      iteratedDeriv n (cepsScaledSurrogateG dom ρW N lam z b) ξ‖ ≤
      ((n.factorial : ℝ) * (Real.exp 2 * dom.canonWeightErrorBound N M) / (1 / 2 : ℝ) ^ n) *
        Real.exp (-(ξ * (1 + (b : ℂ) * lam)).re) * |b * lam| ^ (N + 1) := by
  let R := dom.entranceSpatialScaleRadius lam z
  let w : ℂ := 1 + (b : ℂ) * lam
  have hC0 : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hR : 2 ≤ R := by
    dsimp [R, CepsCanonDomain.entranceSpatialScaleRadius]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hsub : ball ξ (1 : ℝ) ⊆ ball (0 : ℂ) R := by
    intro ζ hζ
    have hn := norm_add_le (ζ - ξ) ξ
    rw [sub_add_cancel] at hn
    have hz1 : ‖ζ - ξ‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hζ
    exact mem_ball_zero_iff.mpr (by nlinarith)
  have hbase : ∀ ξ ∈ ball (0 : ℂ) R,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖(b : ℂ) * ξ‖ < dom.c₀ / 2 :=
    fun _ hξ => entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb hξ
  have hC := (hbase ξ (hsub (mem_ball_self (by norm_num : (0 : ℝ) < 1)))).1
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz
    (sign := 1) (by norm_num) hC
  have hμ' : |b * lam| ≤ dom.μ₀ / 8 := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    simpa only [norm_real, Real.norm_eq_abs] using ht.le
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  rw [norm_real, Real.norm_eq_abs] at ht
  have hA1 : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hμ1 : ‖(b : ℂ) * (lam : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖, abs_nonneg b]
  have hw : ‖w‖ ≤ 2 := by
    have hn := norm_add_le (1 : ℂ) ((b : ℂ) * (lam : ℂ))
    rw [norm_one] at hn
    exact hn.trans (by linarith)
  have hA := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD N M lam hz hb
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD (M := M) hf hη N (by omega) lam hz
  have hB : DifferentiableOn ℂ (cepsScaledSurrogateG dom ρW N lam z b) (ball 0 R) :=
    fun ζ hζ => (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ ⟨hb, hζ⟩).differentiableWithinAt
  have hK : 0 ≤ dom.canonWeightErrorBound N M := by
    have hM0 := (cepsSobolev_nonneg m η fW).trans hM
    have := CepsCanonDomain.v_pos hW hθ hD
    have := dom.jetC_nonneg hD N
    have := dom.c₀_pos
    unfold CepsCanonDomain.canonWeightErrorBound CepsCanonDomain.canonDriftCoeffBound
    positivity
  have hbudget : ∀ ζ ∈ ball ξ (1 : ℝ),
      ‖cepsScaledTrueG dom ρW lam z b ζ - cepsScaledSurrogateG dom ρW N lam z b ζ‖ ≤
        Real.exp (-(ξ * w).re) * (Real.exp 2 * dom.canonWeightErrorBound N M) * |b * lam| ^ (N + 1) := by
    intro ζ hζ
    have hsp := (hbase ζ (hsub hζ)).2
    have hWgt := cepsCanonTrueWeight_approx dom hW hθ hD hf hη hM N hN hμ' hq.le hsp.le
    rw [ofReal_mul] at hWgt
    have hExp : ‖exp (-(ζ - ξ) * w)‖ ≤ Real.exp 2 := by
      rw [norm_exp]
      apply Real.exp_le_exp.mpr
      have hr := re_le_norm (-(ζ - ξ) * w)
      rw [norm_mul, norm_neg] at hr
      have hz1 : ‖ζ - ξ‖ ≤ 1 := by simpa only [dist_eq_norm] using (mem_ball.mp hζ).le
      exact hr.trans (by nlinarith [norm_nonneg (ζ - ξ)])
    have he : -ζ * w = -ξ * w + -(ζ - ξ) * w := by ring
    unfold cepsScaledTrueG cepsScaledSurrogateG
    rw [← mul_sub]
    change ‖exp (-ζ * w) * _‖ ≤ _
    rw [he, exp_add, norm_mul, norm_mul]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hExp (norm_nonneg _)) hWgt
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans_eq
    rw [norm_exp, neg_mul, neg_re]
    ring
  have hh := norm_iteratedDeriv_le_of_ball n (by norm_num : (0 : ℝ) < 1)
    ((hA.sub hB).mono hsub) hbudget
  have hξ0 : ξ ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
  rw [iteratedDeriv_sub ((hA.analyticOnNhd isOpen_ball) ξ hξ0).contDiffAt
    ((hB.analyticOnNhd isOpen_ball) ξ hξ0).contDiffAt] at hh
  apply hh.trans_eq
  ring

end PGM
