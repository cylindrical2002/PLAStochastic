import PLAStochastic.Index.CEPS.Scaled.CanonDriftTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Spatial jets of the genuine real-drift canonical surrogate

Cauchy estimates transfer the true real-drift approximation to every spatial
derivative at zero. Only the finite drift polynomial is extended to complex
drift. Its spatial slope is an explicit finite polynomial in that drift.
-/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}

def cepsCanonSpatialDriftCoeff (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (j : ℕ) (q : ℂ) : ℂ :=
  deriv (cepsCanonDriftCoeff dom ρW j q) 0

def cepsCanonSpatialDriftTaylor (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (N : ℕ) (μ q : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * μ ^ j *
    cepsCanonSpatialDriftCoeff dom ρW j q

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonDriftCoeff_spatial_differentiableOn {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (j : ℕ) (hj : j + 1 ≤ m) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 2) :
    DifferentiableOn ℂ (cepsCanonDriftCoeff dom ρW j q)
      {ζ : ℂ | ζ.re < dom.c₀} := by
  have hc := cepsCanonDriftCoeff_differentiableOn dom hW hθ hD hf hη j hj
  have hcurve : DifferentiableOn ℂ (fun ζ : ℂ => (ζ, q)) {ζ : ℂ | ζ.re < dom.c₀} := by
    fun_prop
  simpa only [Function.comp_apply] using! hc.comp hcurve (fun _ hζ => ⟨hζ, hq⟩)

include hW hθ hD in
theorem cepsCanonDriftTaylor_spatial_deriv_eq {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (μ : ℂ) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 2) :
    deriv (cepsCanonDriftTaylor dom ρW N μ q) 0 =
      cepsCanonSpatialDriftTaylor dom ρW N μ q := by
  have hc : ∀ j ∈ range (N + 1), DifferentiableAt ℂ (cepsCanonDriftCoeff dom ρW j q) 0 := by
    intro j hj
    have hd := cepsCanonDriftCoeff_spatial_differentiableOn dom hW hθ hD hf hη j
      (by have := mem_range.mp hj; omega) hq
    exact (hd 0 (by simpa using dom.c₀_pos)).differentiableAt
      ((isOpen_lt continuous_re continuous_const).mem_nhds (by simpa using dom.c₀_pos))
  unfold cepsCanonDriftTaylor cepsCanonSpatialDriftTaylor
  rw [deriv_fun_sum (fun j hj => (hc j hj).const_mul _)]
  apply sum_congr rfl
  intro j hj
  exact deriv_const_mul _ (hc j hj)

theorem cepsCanonSpatialDriftTaylor_differentiable (N : ℕ) (q : ℂ) :
    Differentiable ℂ (fun μ => cepsCanonSpatialDriftTaylor dom ρW N μ q) := by
  unfold cepsCanonSpatialDriftTaylor
  fun_prop

include hW hθ hD in
theorem cepsCanonSpatialDriftCoeff_norm_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (j : ℕ) (hj : j + 1 ≤ m)
    {q : ℂ} (hq : ‖q‖ < dom.q₀ / 2) :
    ‖cepsCanonSpatialDriftCoeff dom ρW j q‖ ≤
      4 * dom.canonDriftCoeffBound j M / dom.c₀ := by
  have hr : 0 < dom.c₀ / 2 := half_pos dom.c₀_pos
  have hd := (cepsCanonDriftCoeff_spatial_differentiableOn dom hW hθ hD hf hη j hj hq).mono
    (show ball (0 : ℂ) (dom.c₀ / 2) ⊆ {ζ : ℂ | ζ.re < dom.c₀} from
      fun ζ hζ => (re_le_norm ζ).trans_lt ((mem_ball_zero_iff.mp hζ).trans
        (half_lt_self dom.c₀_pos)))
  have hb : ∀ ζ ∈ ball (0 : ℂ) (dom.c₀ / 2),
      ‖cepsCanonDriftCoeff dom ρW j q ζ‖ ≤ dom.canonDriftCoeffBound j M :=
    fun _ hζ => cepsCanonDriftCoeff_norm_le dom hW hθ hD hf hη hM j hj hq.le
      (mem_ball_zero_iff.mp hζ).le
  have h := norm_iteratedDeriv_le_of_ball 1 hr hd hb
  rw [iteratedDeriv_one] at h
  apply h.trans_eq
  simp
  ring

include hW hθ hD in
theorem cepsCanonSpatialDriftTaylor_norm_le {m : ℕ} {η M r : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q : ℂ} (hμ : ‖μ‖ ≤ r) (hq : ‖q‖ < dom.q₀ / 2) :
    ‖cepsCanonSpatialDriftTaylor dom ρW N μ q‖ ≤
      4 * dom.canonDriftTaylorBound N M r / dom.c₀ := by
  have hr : 0 ≤ r := (norm_nonneg μ).trans hμ
  unfold cepsCanonSpatialDriftTaylor CepsCanonDomain.canonDriftTaylorBound
  rw [mul_sum, sum_div]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  have hc := cepsCanonSpatialDriftCoeff_norm_le dom hW hθ hD hf hη hM j
    (by have := mem_range.mp hj; omega) hq
  calc
    _ ≤ (j.factorial : ℝ)⁻¹ * r ^ j * (4 * dom.canonDriftCoeffBound j M / dom.c₀) := by
      gcongr
    _ = _ := by ring

include hW hθ hD in
theorem cepsCanonDriftTaylor_spatial_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 2) (n : ℕ) :
    ‖iteratedDeriv n (dom.canonL ρW μ q) 0 -
      iteratedDeriv n (cepsCanonDriftTaylor dom ρW N μ q) 0‖ ≤
      ((n.factorial : ℝ) * dom.canonDriftCoeffBound (N + 1) M /
        (dom.c₀ / 4) ^ n) * |μ| ^ (N + 1) := by
  let U := ball (0 : ℂ) (dom.c₀ / 2)
  have hr : 0 < dom.c₀ / 2 := half_pos dom.c₀_pos
  have hμ' : |μ| ≤ dom.μ₀ := hμ.le.trans (by linarith [dom.μ₀_pos])
  have hq' : ‖q‖ ≤ dom.q₀ := hq.le.trans (by linarith [dom.q₀_pos])
  have hA : DifferentiableOn ℂ (dom.canonL ρW μ q) U := by
    intro ζ hζ
    exact (CepsC6.differentiableAt_canonL dom hW hθ hD hμ' hq'
      ((re_le_norm ζ).trans_lt ((mem_ball_zero_iff.mp hζ).trans
        (half_lt_self dom.c₀_pos)))).differentiableWithinAt
  have hcurve : DifferentiableOn ℂ (fun ζ : ℂ => ((μ : ℂ), (q, ζ))) U := by fun_prop
  have hB : DifferentiableOn ℂ (cepsCanonDriftTaylor dom ρW N μ q) U := by
    simpa only [Function.comp_apply] using!
      (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N (by omega)).comp hcurve
        (fun ζ hζ => ⟨(re_le_norm ζ).trans_lt ((mem_ball_zero_iff.mp hζ).trans
          (half_lt_self dom.c₀_pos)), hq⟩)
  have hb : ∀ ζ ∈ U, ‖dom.canonL ρW μ q ζ - cepsCanonDriftTaylor dom ρW N μ q ζ‖ ≤
      dom.canonDriftCoeffBound (N + 1) M * |μ| ^ (N + 1) :=
    fun _ hζ => cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN hμ hq.le
      (mem_ball_zero_iff.mp hζ).le
  have h := norm_iteratedDeriv_le_of_ball n hr (hA.sub hB) hb
  have h0 : (0 : ℂ) ∈ U := mem_ball_self hr
  have hCA : ContDiffAt ℂ n (dom.canonL ρW μ q) 0 :=
    ((hA.contDiffOn isOpen_ball) 0 h0).contDiffAt (isOpen_ball.mem_nhds h0)
  have hCB : ContDiffAt ℂ n (cepsCanonDriftTaylor dom ρW N μ q) 0 :=
    ((hB.contDiffOn isOpen_ball) 0 h0).contDiffAt (isOpen_ball.mem_nhds h0)
  rw [iteratedDeriv_sub hCA hCB] at h
  apply h.trans_eq
  ring

include hW hθ hD in
theorem cepsCanonSpatialDriftTaylor_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 2) :
    ‖deriv (dom.canonL ρW μ q) 0 - cepsCanonSpatialDriftTaylor dom ρW N μ q‖ ≤
      (4 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |μ| ^ (N + 1) := by
  have h := cepsCanonDriftTaylor_spatial_approx dom hW hθ hD hf hη hM N hN hμ hq 1
  rw [iteratedDeriv_one, iteratedDeriv_one,
    cepsCanonDriftTaylor_spatial_deriv_eq dom hW hθ hD hf hη N (by omega) (μ : ℂ) hq] at h
  apply h.trans_eq
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
  ring

end PGM
