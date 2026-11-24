import PLAStochastic.Index.CEPS.Scaled.CanonWeight
import PLAStochastic.Index.CEPS.Scaled.CanonSpatialTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.ExpDifference

/-! # True canonical weight error on the full spatial disc

The real-drift Taylor approximation is retained before taking spatial
derivatives. Cauchy estimates give every derivative error on the quarter
disc, with the same real-drift vanishing order.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}

def cepsCanonTrueWeight (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (μ : ℝ) (q ζ : ℂ) : ℂ :=
  cepsQ D θ ρW μ q ζ * exp (-2 * dom.canonL ρW μ q ζ)

def CepsCanonDomain.canonWeightErrorBound (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  2 * v * Real.exp (2 * (dom.normalLogBound + dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
    dom.canonDriftCoeffBound (N + 1) M

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonTrueWeight_spatial_differentiableOn {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    DifferentiableOn ℂ (cepsCanonTrueWeight dom ρW μ q) (ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hQ : DifferentiableOn ℂ (cepsQ D θ ρW μ q) (ball 0 (dom.c₀ / 2)) := by
    intro ζ hζ
    apply (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq ?_).differentiableWithinAt
    apply mem_ball_zero_iff.mpr
    have hn := mem_ball_zero_iff.mp hζ
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hL : DifferentiableOn ℂ (dom.canonL ρW μ q) (ball 0 (dom.c₀ / 2)) := by
    intro ζ hζ
    exact (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
      ((re_le_norm ζ).trans_lt ((mem_ball_zero_iff.mp hζ).trans
        (half_lt_self dom.c₀_pos)))).differentiableWithinAt
  exact hQ.mul ((hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsCanonTrueWeight_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀ / 8) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖cepsCanonTrueWeight dom ρW μ q ζ - cepsCanonSurrogateWeight dom ρW N μ q ζ‖ ≤
      dom.canonWeightErrorBound N M * |μ| ^ (N + 1) := by
  let A := dom.canonL ρW μ q ζ
  let B := cepsCanonDriftTaylor dom ρW N μ q ζ
  let K := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ / 8 := by rwa [norm_real, Real.norm_eq_abs]
  have hμD : ‖(μ : ℂ)‖ ≤ dom.μ₀ := hμ'.trans (by linarith [dom.μ₀_pos])
  have hqD : ‖q‖ ≤ dom.q₀ := hq.trans (half_le_self dom.q₀_pos.le)
  have hA : ‖A‖ ≤ dom.normalLogBound :=
    dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμD (ofReal_im μ) hqD hζ
  have hB : ‖B‖ ≤ K := cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N
    (by omega) hμ' hq hζ
  have hA0 : 0 ≤ dom.normalLogBound := (norm_nonneg A).trans hA
  have hB0 : 0 ≤ K := (norm_nonneg B).trans hB
  have hexp := norm_cexp_sub_cexp_le (M := 2 * (dom.normalLogBound + K))
    (a := -2 * A) (b := -2 * B)
    (by rw [norm_mul, norm_neg, norm_ofNat]; nlinarith)
    (by rw [norm_mul, norm_neg, norm_ofNat]; nlinarith)
  have he : ‖A - B‖ ≤ dom.canonDriftCoeffBound (N + 1) M * |μ| ^ (N + 1) :=
    cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN
      (hμ.trans_lt (by linarith [dom.μ₀_pos])) hq hζ
  rw [show -2 * A - -2 * B = -2 * (A - B) by ring, norm_mul, norm_neg, norm_ofNat] at hexp
  have hQ := cepsQ_norm_le_on_rootZone dom hW hθ hD hμD hqD
    (show ‖ζ‖ < dom.ρA by have := dom.c₀_le; have := dom.ρA_pos; linarith)
  change ‖cepsQ D θ ρW μ q ζ * exp (-2 * A) -
    cepsQ D θ ρW μ q ζ * exp (-2 * B)‖ ≤ _
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ v * (Real.exp (2 * (dom.normalLogBound + K)) *
        (2 * (dom.canonDriftCoeffBound (N + 1) M * |μ| ^ (N + 1)))) := by
      apply mul_le_mul hQ
        (hexp.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num))
          (Real.exp_pos _).le)) (norm_nonneg _) (CepsCanonDomain.v_pos hW hθ hD).le
    _ = _ := by unfold CepsCanonDomain.canonWeightErrorBound; ring

include hW hθ hD in
theorem cepsCanonTrueWeight_spatial_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀ / 8) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀ / 2) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) (n : ℕ) :
    ‖iteratedDeriv n (cepsCanonTrueWeight dom ρW μ q) ζ -
      iteratedDeriv n (cepsCanonSurrogateWeight dom ρW N μ q) ζ‖ ≤
      ((n.factorial : ℝ) * dom.canonWeightErrorBound N M / (dom.c₀ / 8) ^ n) *
        |μ| ^ (N + 1) := by
  have hμD : |μ| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hqD : ‖q‖ ≤ dom.q₀ := hq.le.trans (half_le_self dom.q₀_pos.le)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ / 8 := by rwa [norm_real, Real.norm_eq_abs]
  have hA := cepsCanonTrueWeight_spatial_differentiableOn dom hW hθ hD hμD hqD
  have hB := cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N (by omega) hμ' hq
  have hsub : ball ζ (dom.c₀ / 4) ⊆ ball (0 : ℂ) (dom.c₀ / 2) := by
    intro w hw
    have ht := dist_triangle w ζ 0
    simp only [dist_zero_right] at ht
    exact mem_ball_zero_iff.mpr (by linarith [mem_ball.mp hw])
  have hb : ∀ w ∈ ball ζ (dom.c₀ / 4),
      ‖cepsCanonTrueWeight dom ρW μ q w - cepsCanonSurrogateWeight dom ρW N μ q w‖ ≤
        dom.canonWeightErrorBound N M * |μ| ^ (N + 1) :=
    fun _ hw => cepsCanonTrueWeight_approx dom hW hθ hD hf hη hM N hN hμ hq.le
      (mem_ball_zero_iff.mp (hsub hw)).le
  have h := norm_iteratedDeriv_le_of_ball n (by have := dom.c₀_pos; positivity)
    ((hA.sub hB).mono hsub) hb
  have hz0 : ζ ∈ ball (0 : ℂ) (dom.c₀ / 2) :=
    mem_ball_zero_iff.mpr (by linarith [dom.c₀_pos])
  rw [iteratedDeriv_sub ((hA.analyticOnNhd isOpen_ball) ζ hz0).contDiffAt
    ((hB.analyticOnNhd isOpen_ball) ζ hz0).contDiffAt] at h
  apply h.trans_eq
  ring

end PGM
