import PLAStochastic.Index.CEPS.Scaled.CanonDriftTaylor
import PLAStochastic.Index.CEPS.Normal.ActualPiBounds

/-! # Spatial budgets for the genuine canonical Taylor surrogate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsCanonSurrogateWeight {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (μ q ζ : ℂ) : ℂ :=
  cepsQ D θ ρW μ q ζ * exp (-2 * cepsCanonDriftTaylor dom ρW N μ q ζ)

def CepsCanonDomain.canonSurrogatePiBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  64 * v / (dom.c₀ * cepsVarLo D) *
    Real.exp (4 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonSurrogateWeight_differentiableOn {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {μ q : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2) :
    DifferentiableOn ℂ (cepsCanonSurrogateWeight dom ρW N μ q)
      (ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖μ‖ ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hq' : ‖q‖ ≤ dom.q₀ := hq.le.trans (half_le_self dom.q₀_pos.le)
  have hQ : DifferentiableOn ℂ (cepsQ D θ ρW μ q) (ball 0 (dom.c₀ / 2)) := by
    intro ζ hζ
    apply (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq' ?_).differentiableWithinAt
    apply mem_ball_zero_iff.mpr
    have hn := mem_ball_zero_iff.mp hζ
    have := dom.c₀_le; have := dom.ρA_pos
    linarith
  have hcurve : DifferentiableOn ℂ (fun ζ : ℂ => (μ, (q, ζ)))
      (ball 0 (dom.c₀ / 2)) := by fun_prop
  have hL : DifferentiableOn ℂ (cepsCanonDriftTaylor dom ρW N μ q)
      (ball 0 (dom.c₀ / 2)) := by
    simpa only [Function.comp_apply] using!
      (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve
        (fun ζ hζ => ⟨by
          have := mem_ball_zero_iff.mp hζ
          linarith [re_le_norm ζ, dom.c₀_pos], hq⟩)
  exact hQ.mul ((hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsCanonSurrogateWeight_bounds {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ ≤ dom.q₀ / 2)
    (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    cepsVarLo D / 4 * Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) ≤
        ‖cepsCanonSurrogateWeight dom ρW N μ q ζ‖ ∧
      ‖cepsCanonSurrogateWeight dom ρW N μ q ζ‖ ≤
        v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
  have hμ' : ‖μ‖ ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hq' : ‖q‖ ≤ dom.q₀ := hq.trans (half_le_self dom.q₀_pos.le)
  have hζA : ‖ζ‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq' hζA
  have hQhi := cepsQ_norm_le_on_rootZone dom hW hθ hD hμ' hq' hζA
  have hL := cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N hN hμ hq hζ
  have hlre := (abs_re_le_norm (cepsCanonDriftTaylor dom ρW N μ q ζ)).trans hL
  have hlo : Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) ≤
      ‖exp (-2 * cepsCanonDriftTaylor dom ρW N μ q ζ)‖ := by
    rw [norm_exp]; apply Real.exp_le_exp.mpr
    simp [mul_re]
    linarith [(le_abs_self (cepsCanonDriftTaylor dom ρW N μ q ζ).re).trans hlre]
  have hhi : ‖exp (-2 * cepsCanonDriftTaylor dom ρW N μ q ζ)‖ ≤
      Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
    rw [norm_exp]; apply Real.exp_le_exp.mpr
    simp [mul_re]
    linarith [(neg_le_abs (cepsCanonDriftTaylor dom ρW N μ q ζ).re).trans hlre]
  rw [cepsCanonSurrogateWeight, norm_mul]
  exact ⟨mul_le_mul hQlo hlo (Real.exp_pos _).le (norm_nonneg _),
    mul_le_mul hQhi hhi (norm_nonneg _) (CepsCanonDomain.v_pos hW hθ hD).le⟩

include hW hθ hD in
theorem cepsCanonSurrogateWeight_deriv_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    ‖deriv (cepsCanonSurrogateWeight dom ρW N μ q) ζ‖ ≤
      16 * (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) / dom.c₀ := by
  have hsub : ball ζ (dom.c₀ / 8) ⊆ ball (0 : ℂ) (dom.c₀ / 2) := by
    intro w hw
    have ht := dist_triangle w ζ 0
    simp only [dist_zero_right] at ht
    have hw' := mem_ball.mp hw
    apply mem_ball_zero_iff.mpr
    linarith [dom.c₀_pos]
  have hd := (cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ hq).mono hsub
  have hb : ∀ w ∈ ball ζ (dom.c₀ / 8), ‖cepsCanonSurrogateWeight dom ρW N μ q w‖ ≤
      v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) :=
    fun w hw => (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
      (mem_ball_zero_iff.mp (hsub hw)).le).2
  have he := norm_iteratedDeriv_le_of_ball 1 (by linarith [dom.c₀_pos]) hd hb
  rw [iteratedDeriv_one] at he
  apply he.trans_eq
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
  ring

include hD in
theorem canonSurrogatePiBound_mul_weightLower (N : ℕ) (M : ℝ) :
    dom.canonSurrogatePiBound N M *
      (cepsVarLo D / 4 * Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) =
        16 * (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) / dom.c₀ := by
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hexp : Real.exp (4 * B) * Real.exp (-2 * B) = Real.exp (2 * B) := by
    rw [← Real.exp_add]; congr 1; ring
  have hvl := (cepsVarLo_pos hD).ne'
  have hc := dom.c₀_pos.ne'
  unfold CepsCanonDomain.canonSurrogatePiBound
  change 64 * v / (dom.c₀ * cepsVarLo D) * Real.exp (4 * B) *
    (cepsVarLo D / 4 * Real.exp (-2 * B)) = _
  calc
    _ = (16 * v / dom.c₀) * (Real.exp (4 * B) * Real.exp (-2 * B)) := by field_simp; ring
    _ = _ := by rw [hexp]; ring

include hW hθ hD in
theorem cepsCanonSurrogateWeight_deriv_relative_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    ‖deriv (cepsCanonSurrogateWeight dom ρW N μ q) ζ‖ ≤
      dom.canonSurrogatePiBound N M * ‖cepsCanonSurrogateWeight dom ρW N μ q ζ‖ := by
  have hP : 0 ≤ dom.canonSurrogatePiBound N M := by
    have := dom.c₀_pos; have := cepsVarLo_pos hD; have := CepsCanonDomain.v_pos hW hθ hD
    unfold CepsCanonDomain.canonSurrogatePiBound
    positivity
  have hlo := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
    (show ‖ζ‖ ≤ dom.c₀ / 2 by linarith [dom.c₀_pos])).1
  calc
    _ ≤ _ := cepsCanonSurrogateWeight_deriv_bound dom hW hθ hD hf hη hM N hN hμ hq hζ
    _ = _ := (canonSurrogatePiBound_mul_weightLower dom hD N M).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo hP

end PGM
