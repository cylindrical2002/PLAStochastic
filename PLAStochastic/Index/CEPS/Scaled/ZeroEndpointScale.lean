import PLAStochastic.Index.CEPS.Scaled.CanonSpatialTaylor
import PLAStochastic.Index.CEPS.Normal.ZeroHalfTransport
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # The scaled finite endpoint at zero discount

The true endpoint is exactly the finite physical endpoint multiplied by
minus the square of the scale. Its polynomial surrogate has a two-order
vanishing true-factor error. This module concerns zero discount only.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}

def cepsScaledZeroEndpoint (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (b : ℝ) : ℂ :=
  1 - (cepsStepVar ρW : ℂ) / 2 +
    (b : ℂ) * (1 + 2 * deriv (dom.canonL ρW b 0) 0) - (b : ℂ) ^ 2 / 2

def cepsScaledSurrogateZeroEndpoint (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (N : ℕ) (b : ℂ) : ℂ :=
  1 - (cepsStepVar ρW : ℂ) / 2 +
    b * (1 + 2 * cepsCanonSpatialDriftTaylor dom ρW N b 0) - b ^ 2 / 2

variable (dom : CepsCanonDomain D θ v)

theorem cepsScaledZeroEndpoint_eq_physical {b : ℝ} (hb : b ≠ 0) :
    cepsScaledZeroEndpoint dom ρW b =
      -(b : ℂ) ^ 2 * dom.halfZeroEndpoint ρW b (b : ℂ)⁻¹ := by
  unfold cepsScaledZeroEndpoint CepsCanonDomain.halfZeroEndpoint
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb
  field_simp
  ring

theorem cepsScaledZeroEndpoint_zero :
    cepsScaledZeroEndpoint dom ρW 0 = 1 - (cepsStepVar ρW : ℂ) / 2 := by
  simp [cepsScaledZeroEndpoint]

theorem cepsScaledSurrogateZeroEndpoint_zero (N : ℕ) :
    cepsScaledSurrogateZeroEndpoint dom ρW N 0 = 1 - (cepsStepVar ρW : ℂ) / 2 := by
  simp [cepsScaledSurrogateZeroEndpoint]

theorem cepsScaledSurrogateZeroEndpoint_differentiable (N : ℕ) :
    Differentiable ℂ (cepsScaledSurrogateZeroEndpoint dom ρW N) := by
  unfold cepsScaledSurrogateZeroEndpoint
  exact ((differentiable_const _).add (differentiable_id.mul
    ((differentiable_const _).add
      ((cepsCanonSpatialDriftTaylor_differentiable dom N 0).const_mul 2)))).sub
        ((differentiable_id.pow 2).div_const 2)

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateZeroEndpoint_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {b : ℝ} (hb : |b| < dom.μ₀ / 4) :
    ‖cepsScaledZeroEndpoint dom ρW b - cepsScaledSurrogateZeroEndpoint dom ρW N b‖ ≤
      (8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |b| ^ (N + 2) := by
  have hq : ‖(0 : ℂ)‖ < dom.q₀ / 2 := by simpa using half_pos dom.q₀_pos
  have hr := cepsCanonSpatialDriftTaylor_approx dom hW hθ hD hf hη hM N hN hb hq
  have he : cepsScaledZeroEndpoint dom ρW b - cepsScaledSurrogateZeroEndpoint dom ρW N b =
      (2 : ℂ) * b * (deriv (dom.canonL ρW b 0) 0 -
        cepsCanonSpatialDriftTaylor dom ρW N b 0) := by
    unfold cepsScaledZeroEndpoint cepsScaledSurrogateZeroEndpoint
    ring
  rw [he, norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * |b|)).trans_eq
  rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
  ring

namespace CepsCanonDomain

def zeroEndpointScaleRadius (dom : CepsCanonDomain D θ v) : ℝ := min 1 (dom.μ₀ / 8)

def zeroEndpointPolynomialBound (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  1 + v / 2 + dom.zeroEndpointScaleRadius *
    (1 + 8 * dom.canonDriftTaylorBound N M dom.zeroEndpointScaleRadius / dom.c₀) +
      dom.zeroEndpointScaleRadius ^ 2 / 2

end CepsCanonDomain

theorem zeroEndpointScaleRadius_pos : 0 < dom.zeroEndpointScaleRadius := by
  unfold CepsCanonDomain.zeroEndpointScaleRadius
  exact lt_min (by norm_num) (by have := dom.μ₀_pos; positivity)

include hW hθ hD in
theorem cepsScaledSurrogateZeroEndpoint_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) :
    ∀ b ∈ ball (0 : ℂ) dom.zeroEndpointScaleRadius,
      ‖cepsScaledSurrogateZeroEndpoint dom ρW N b‖ ≤ dom.zeroEndpointPolynomialBound N M := by
  intro b hb
  have hr : ‖b‖ ≤ dom.zeroEndpointScaleRadius := (mem_ball_zero_iff.mp hb).le
  have hr0 : 0 ≤ dom.zeroEndpointScaleRadius := (zeroEndpointScaleRadius_pos dom).le
  have hq : ‖(0 : ℂ)‖ < dom.q₀ / 2 := by simpa using half_pos dom.q₀_pos
  have hρ := cepsCanonSpatialDriftTaylor_norm_le dom hW hθ hD hf hη hM N hN hr hq
  have hB : 0 ≤ 4 * dom.canonDriftTaylorBound N M dom.zeroEndpointScaleRadius / dom.c₀ :=
    (norm_nonneg _).trans hρ
  have hV : ‖(cepsStepVar ρW : ℂ)‖ ≤ v := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (cepsStepVar_pos hW hθ hD)]
    exact cepsStepVar_le hW
  unfold cepsScaledSurrogateZeroEndpoint
  calc
    _ ≤ ‖1 - (cepsStepVar ρW : ℂ) / 2‖ +
        ‖b * (1 + 2 * cepsCanonSpatialDriftTaylor dom ρW N b 0)‖ + ‖b ^ 2 / 2‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 + v / 2) + dom.zeroEndpointScaleRadius *
        (1 + 2 * (4 * dom.canonDriftTaylorBound N M dom.zeroEndpointScaleRadius / dom.c₀)) +
          dom.zeroEndpointScaleRadius ^ 2 / 2 := by
      have hc : ‖1 - (cepsStepVar ρW : ℂ) / 2‖ ≤ 1 + v / 2 := by
        apply (norm_sub_le _ _).trans
        rw [norm_one, norm_div, norm_ofNat]
        gcongr
      have hinner : ‖1 + 2 * cepsCanonSpatialDriftTaylor dom ρW N b 0‖ ≤
          1 + 2 * (4 * dom.canonDriftTaylorBound N M dom.zeroEndpointScaleRadius / dom.c₀) := by
        apply (norm_add_le _ _).trans
        rw [norm_one, norm_mul, norm_ofNat]
        gcongr
      rw [norm_mul, norm_div, norm_pow, norm_ofNat]
      gcongr
    _ = dom.zeroEndpointPolynomialBound N M := by
      unfold CepsCanonDomain.zeroEndpointPolynomialBound
      ring

include hW hθ hD in
theorem cepsScaledSurrogateZeroEndpoint_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (n : ℕ) {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.zeroEndpointScaleRadius / 2)) :
    ‖cepsScaledSurrogateZeroEndpoint dom ρW N b -
      complexTaylorSum (cepsScaledSurrogateZeroEndpoint dom ρW N) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.zeroEndpointPolynomialBound N M /
        (dom.zeroEndpointScaleRadius / 4) ^ n) * ‖b‖ ^ n := by
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (zeroEndpointScaleRadius_pos dom)
    (cepsScaledSurrogateZeroEndpoint_differentiable dom N).differentiableOn
    (cepsScaledSurrogateZeroEndpoint_budget dom hW hθ hD hf hη hM N hN) hb

end PGM
