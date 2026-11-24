import PLAStochastic.Index.CEPS.Scaled.CanonWeight
import PLAStochastic.Index.CEPS.Normal.SlopeStability

/-! # A uniform spatial disc for the scaled surrogate before choosing roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledBoundedSpatialG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (μ q w b ξ : ℂ) : ℂ :=
  exp (-ξ * w) * cepsCanonSurrogateWeight dom ρW N μ q (b * ξ)

def CepsCanonDomain.boundedSpatialWeightLower {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  cepsVarLo D / 4 * Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

def CepsCanonDomain.boundedSpatialGUpper {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp 2 * (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)))

def CepsCanonDomain.boundedSpatialRootRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (1 / 4) (dom.boundedSpatialWeightLower N M / (512 * dom.boundedSpatialGUpper N M))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem boundedSpatialWeightLower_pos (N : ℕ) (M : ℝ) : 0 < dom.boundedSpatialWeightLower N M :=
  mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)

include hW hθ hD in
theorem boundedSpatialGUpper_pos (N : ℕ) (M : ℝ) : 0 < dom.boundedSpatialGUpper N M :=
  mul_pos (Real.exp_pos _) (mul_pos (CepsCanonDomain.v_pos hW hθ hD) (Real.exp_pos _))

include hW hθ hD in
theorem boundedSpatialRootRadius_pos (N : ℕ) (M : ℝ) : 0 < dom.boundedSpatialRootRadius N M :=
  lt_min (by norm_num) (div_pos (boundedSpatialWeightLower_pos dom hD N M)
    (mul_pos (by norm_num) (boundedSpatialGUpper_pos dom hW hθ hD N M)))

include hW hθ hD in
theorem cepsScaledBoundedSpatialG_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q w b : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hw : ‖w‖ ≤ 2) (hb : ‖b‖ ≤ dom.c₀ / 4) :
    DifferentiableOn ℂ (cepsScaledBoundedSpatialG dom ρW N μ q w b) (ball 0 1) ∧
      ∀ ξ ∈ ball (0 : ℂ) 1,
        ‖cepsScaledBoundedSpatialG dom ρW N μ q w b ξ‖ ≤ dom.boundedSpatialGUpper N M := by
  have hmap : MapsTo (fun ξ : ℂ => b * ξ) (ball 0 1) (ball 0 (dom.c₀ / 2)) := by
    intro ξ hξ
    rw [mem_ball_zero_iff, norm_mul]
    have hn := mem_ball_zero_iff.mp hξ
    have hh : ‖b‖ * ‖ξ‖ ≤ dom.c₀ / 4 := by nlinarith [norm_nonneg b]
    linarith [dom.c₀_pos]
  have hWgt := (cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ hq).comp
    (differentiableOn_id.const_mul b) hmap
  have hExp : DifferentiableOn ℂ (fun ξ : ℂ => exp (-ξ * w)) (ball 0 1) := by fun_prop
  refine ⟨hExp.mul hWgt, fun ξ hξ => ?_⟩
  have hE : ‖exp (-ξ * w)‖ ≤ Real.exp 2 := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hh : ‖-ξ * w‖ ≤ 2 := by
      rw [norm_mul, norm_neg]
      have := mem_ball_zero_iff.mp hξ
      nlinarith [norm_nonneg w]
    exact (re_le_norm _).trans hh
  have hV := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
    (mem_ball_zero_iff.mp (hmap hξ)).le).2
  rw [cepsScaledBoundedSpatialG, norm_mul]
  exact mul_le_mul hE hV (norm_nonneg _) (Real.exp_pos _).le

include hW hθ hD in
theorem cepsScaledBoundedSpatialG_deriv_zero {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2) (w b : ℂ) :
    deriv (cepsScaledBoundedSpatialG dom ρW N μ q w b) 0 =
      -w * cepsCanonSurrogateWeight dom ρW N μ q 0 + b * deriv (cepsCanonSurrogateWeight dom ρW N μ q) 0 := by
  have hd := ((cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ hq)
    0 (mem_ball_self (half_pos dom.c₀_pos))).differentiableAt (ball_mem_nhds 0 (half_pos dom.c₀_pos)) |>.hasDerivAt
  have hcurve : HasDerivAt (fun ξ : ℂ => b * ξ) b 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_mul b
  have hG := (((hasDerivAt_id' (0 : ℂ)).neg.mul_const w).cexp).mul
    (hd.comp_of_eq (0 : ℂ) hcurve (by simp))
  have hh := hG.deriv
  simp only [Pi.neg_apply, neg_zero, zero_mul, exp_zero, one_mul,
    Function.comp_apply, mul_zero] at hh
  exact hh.trans (by ring)

end PGM
