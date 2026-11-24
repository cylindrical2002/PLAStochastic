import PLAStochastic.Index.CEPS.Canonical.MixedBounds

/-! # Joint continuity of the actual first drift jet

Pointwise line holomorphy and the Sobolev majorant give continuity in the
real drift, complex discount and complex spatial argument together.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem continuousAt_cepsCanonLJet_zero_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    ContinuousAt (fun x : ℝ × (ℂ × ℂ) =>
      cepsCanonLJet D θ ρW dom.c₀ 0 x.1 x.2.1 x.2.2) (μ, (q, ζ)) := by
  let x₀ : ℝ × (ℂ × ℂ) := (μ, (q, ζ))
  let δ := (dom.c₀ - ζ.re) / 2
  let C := dom.jetC 0 * (cepsSobolev m η fW + 1)
  let F : (ℝ × (ℂ × ℂ)) → ℝ → ℂ := fun x y =>
    cepsLogFJet D θ ρW 0 x.1 x.2.1 (dom.c₀ + y * I) / (dom.c₀ + y * I - x.2.2)
  let bound : ℝ → ℝ := fun y => 2 * C *
    ‖(((dom.c₀ : ℂ) + y * I) * ((dom.c₀ : ℂ) + y * I - ζ))⁻¹‖
  have hc := dom.c₀_pos
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hC : 0 ≤ C := by
    exact mul_nonneg (dom.jetC_nonneg hD 0) (by linarith [cepsSobolev_nonneg m η fW])
  have hevent : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀,
      |x.1| < dom.μ₀ / 4 ∧ ‖x.2.1‖ < dom.q₀ / 2 ∧ ‖x.2.2 - ζ‖ < δ := by
    have h1 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, |x.1| < dom.μ₀ / 4 :=
      (isOpen_lt (continuous_fst.abs) continuous_const).mem_nhds
        (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | |x.1| < dom.μ₀ / 4} from hμ)
    have h2 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, ‖x.2.1‖ < dom.q₀ / 2 :=
      (isOpen_lt (continuous_fst.comp continuous_snd).norm continuous_const).mem_nhds
        (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | ‖x.2.1‖ < dom.q₀ / 2} from hq)
    have h3 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, ‖x.2.2 - ζ‖ < δ :=
      (isOpen_lt (((continuous_snd.comp continuous_snd).sub continuous_const).norm)
        continuous_const).mem_nhds
          (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | ‖x.2.2 - ζ‖ < δ} by simpa [x₀] using hδ)
    exact h1.and (h2.and h3)
  have hspace : ∀ x : ℝ × (ℂ × ℂ), ‖x.2.2 - ζ‖ < δ → x.2.2.re < dom.c₀ := by
    intro x hx
    have hr := re_le_norm (x.2.2 - ζ)
    rw [sub_re] at hr
    dsimp [δ] at hx
    linarith
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) volume := by
    filter_upwards [hevent] with x hx
    exact dom.aestronglyMeasurable_jet_div hW hθ hD le_rfl (by linarith)
      hx.2.1.le 0 hx.1 (hspace x hx.2.2)
  have hbound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ y : ℝ, ‖F x y‖ ≤ bound y := by
    filter_upwards [hevent] with x hx
    refine Eventually.of_forall fun y => ?_
    let s : ℂ := dom.c₀ + y * I
    have hsre : s.re = dom.c₀ := by simp [s]
    have hs0 : 0 < ‖s‖ := by linarith [re_le_norm s]
    have hbase : 2 * δ ≤ ‖s - ζ‖ := by
      have hr := re_le_norm (s - ζ)
      rw [sub_re, hsre] at hr
      dsimp [δ]; linarith
    have htri : ‖s - ζ‖ ≤ ‖s - x.2.2‖ + ‖x.2.2 - ζ‖ := by
      calc
        _ = ‖(s - x.2.2) + (x.2.2 - ζ)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hden : ‖s - ζ‖ / 2 ≤ ‖s - x.2.2‖ := by linarith [hx.2.2]
    have hbase0 : 0 < ‖s - ζ‖ := by linarith
    have hinv : ‖s - x.2.2‖⁻¹ ≤ 2 * ‖s - ζ‖⁻¹ := by
      calc
        _ ≤ (‖s - ζ‖ / 2)⁻¹ := inv_anti₀ (by positivity) hden
        _ = _ := by field_simp
    have hk : ‖(s * (s - x.2.2))⁻¹‖ ≤ 2 * ‖(s * (s - ζ))⁻¹‖ := by
      simp only [norm_inv, norm_mul, mul_inv_rev]
      calc
        _ ≤ (2 * ‖s - ζ‖⁻¹) * ‖s‖⁻¹ := mul_le_mul_of_nonneg_right hinv (by positivity)
        _ = _ := by ring
    have hj := dom.norm_jet_div_le hW hθ hD hf hη (n := 0) (by simpa using hm)
      le_rfl (by linarith) hx.1.le hx.2.1.le (hspace x hx.2.2) y
    change ‖F x y‖ ≤ C * ‖(s * (s - x.2.2))⁻¹‖ at hj
    exact hj.trans (by
      change C * ‖(s * (s - x.2.2))⁻¹‖ ≤ 2 * C * ‖(s * (s - ζ))⁻¹‖
      calc
        _ ≤ C * (2 * ‖(s * (s - ζ))⁻¹‖) := mul_le_mul_of_nonneg_left hk hC
        _ = _ := by ring)
  have hint : Integrable bound := (integrable_inv_mul_line hc hζ).norm.const_mul (2 * C)
  have hpoint : ∀ᵐ y : ℝ, ContinuousAt (fun x => F x y) x₀ := by
    refine Eventually.of_forall fun y => ?_
    let s : ℂ := dom.c₀ + y * I
    have hsre : s.re = dom.c₀ := by simp [s]
    have hs0 : 0 < ‖s‖ := by linarith [re_le_norm s]
    have h2 : dom.c₀ ≤ |s.re| := by rw [hsre, abs_of_pos hc]
    have h3 : |s.re| ≤ 2 * dom.c₀ := by rw [hsre, abs_of_pos hc]; linarith
    have heps := dom.epsL_pos
    have hmem1 : ((μ : ℂ), q) ∈
        ball (μ : ℂ) (dom.epsL / ‖s‖) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) :=
      ⟨mem_ball_self (by positivity), mem_ball_zero_iff.mpr hq⟩
    have hmem2 : ((μ : ℂ), q) ∈
        ball (0 : ℂ) (dom.μ₀ / 2) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) :=
      ⟨mem_ball_zero_iff.mpr (by rw [norm_real, Real.norm_eq_abs]; linarith [dom.μ₀_pos]),
        mem_ball_zero_iff.mpr hq⟩
    have hG1 := ((dom.differentiableOn_G1_joint hW hθ hD hμ.le h2 h3) _ hmem1).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hmem1)
    have hG2 := ((dom.differentiableOn_G2_joint hW hθ hD h2) _ hmem2).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hmem2)
    have hp : ContinuousAt (fun x : ℝ × (ℂ × ℂ) => ((x.1 : ℂ), x.2.1)) x₀ := by fun_prop
    have hJc : ContinuousAt (fun p : ℂ × ℂ =>
        cepsG1 ρW p.1 p.2 s + cepsG2 D θ ρW p.1 p.2 s) ((μ : ℂ), q) :=
      (hG1.add hG2).continuousAt
    have hJ : ContinuousAt (fun x : ℝ × (ℂ × ℂ) => cepsLogFJet D θ ρW 0 x.1 x.2.1 s) x₀ := by
      simpa only [cepsLogFJet, iteratedDeriv_zero, Function.comp_def] using
        hJc.comp (f := fun x : ℝ × (ℂ × ℂ) => ((x.1 : ℂ), x.2.1)) hp
    have hne : s - ζ ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      rw [sub_re, hsre, zero_re] at hr
      linarith
    exact hJ.div (by fun_prop) hne
  have hi := continuousAt_of_dominated hmeas hbound hint hpoint
  exact hi.const_mul ((2 * Real.pi : ℂ)⁻¹)

end PGM.CepsCanonDomain
