import PLAStochastic.Index.CEPS.Canonical.MixedBounds
import PLAStochastic.ForMathlib.Analysis.Complex.LineCauchyParameter

/-! # Commuting real drift and complex spatial derivatives of the actual factor -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem deriv_canonL_line_formula {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < dom.c₀) :
    deriv (dom.canonL ρW μ q) ζ =
      (2 * Real.pi : ℂ)⁻¹ * deriv
        (lineCauchy (fun y : ℝ => log (cepsF D θ ρW 1 μ q (dom.c₀ + y * I))) dom.c₀) ζ -
        deriv (fun z : ℂ => log (1 - z)) ζ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hI := dom.integrable_cepsCanonL_integrand hW hθ hD
    (γ := 1) (by norm_num) le_rfl le_rfl (by linarith [dom.c₀_pos]) hμ' (by simp) hq hζ
  have hline := hasDerivAt_lineCauchy hζ.ne hI hζ.ne
  have hslit : 1 - ζ ∈ slitPlane := by
    left
    simp only [sub_re, one_re]
    have := dom.c₀_le
    have := dom.ρA_one
    linarith
  have hlog := ((hasDerivAt_id ζ).const_sub 1).clog hslit
  simp only [ofReal_one, id_eq] at hline hlog
  exact ((hline.const_mul _).sub hlog).deriv.trans (by rw [hline.deriv, hlog.deriv])

include hW hθ hD in
theorem hasDerivAt_deriv_canonL_mu {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    HasDerivAt (fun t : ℝ => deriv (dom.canonL ρW t q) ζ)
      (deriv (fun z => cepsCanonLJet D θ ρW dom.c₀ 0 μ q z) ζ) μ := by
  let δ := (dom.μ₀ / 4 - |μ|) / 2
  let φ := fun (t : ℝ) (y : ℝ) => log (cepsF D θ ρW 1 t q (dom.c₀ + y * I))
  let φ' := fun (t : ℝ) (y : ℝ) => cepsLogFJet D θ ρW 0 t q (dom.c₀ + y * I)
  let bound := fun y : ℝ => dom.jetC 0 * (cepsSobolev m η fW + 1) *
    ‖(((dom.c₀ : ℂ) + y * I) * ((dom.c₀ : ℂ) + y * I - ζ))⁻¹‖
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hball : ∀ t ∈ ball μ δ, |t| < dom.μ₀ / 4 := by
    intro t ht
    rw [mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t μ
    dsimp [δ] at ht
    linarith
  have hc2 : dom.c₀ ≤ 2 * dom.c₀ := by linarith [dom.c₀_pos]
  have hq' : ‖q‖ ≤ dom.q₀ := by linarith [dom.q₀_pos]
  have hI : ∀ t ∈ ball μ δ, Integrable (fun y => φ t y / (dom.c₀ + y * I - ζ)) := by
    intro t ht
    have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by
      rw [norm_real, Real.norm_eq_abs]
      linarith [hball t ht, dom.μ₀_pos]
    exact dom.integrable_cepsCanonL_integrand hW hθ hD (γ := 1) (by norm_num) le_rfl
      le_rfl hc2 ht' (by simp) hq' hζ
  have hDφ : ∀ t ∈ ball μ δ, ∀ y, HasDerivAt (fun t => φ t y) (φ' t y) t := by
    intro t ht y
    have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by
      rw [norm_real, Real.norm_eq_abs]
      linarith [hball t ht, dom.μ₀_pos]
    obtain ⟨hx, hd, hQ, hγs, hslit⟩ := dom.line_point_facts hW hθ hD
      (γ := 1) (by norm_num) le_rfl le_rfl hc2 ht' (by simp) hq' y
    simpa only [φ, φ', cepsLogFJet_zero, ofReal_one] using!
      (hasDerivAt_logF_mu hW hθ hD hx hd hQ hγs hslit).comp_ofReal
  have hmain := hasDerivAt_deriv_lineCauchy_parameter hδ hζ hI hDφ
    (dom.aestronglyMeasurable_jet_div hW hθ hD le_rfl hc2 hq 0 hμ hζ)
    ((integrable_inv_mul_line dom.c₀_pos hζ).norm.const_mul
      (dom.jetC 0 * (cepsSobolev m η fW + 1)))
    (fun y t ht => dom.norm_jet_div_le hW hθ hD hf hη (n := 0) (by simpa using hm)
      le_rfl hc2 (hball t ht).le hq hζ y)
  have he : (fun t : ℝ => deriv (dom.canonL ρW t q) ζ) =ᶠ[𝓝 μ]
      (fun t : ℝ => (2 * Real.pi : ℂ)⁻¹ * deriv (lineCauchy (φ t) dom.c₀) ζ -
        deriv (fun z : ℂ => log (1 - z)) ζ) := by
    filter_upwards [ball_mem_nhds μ hδ] with t ht
    exact dom.deriv_canonL_line_formula hW hθ hD
      (by linarith [hball t ht, dom.μ₀_pos]) hq' hζ
  have hjet := hasDerivAt_lineCauchy hζ.ne
    (dom.integrable_jet_div hW hθ hD hf hη (n := 0) (by simpa using hm)
      le_rfl hc2 hμ hq hζ) hζ.ne
  have hjet' := (hjet.const_mul ((2 * Real.pi : ℂ)⁻¹)).deriv
  exact ((hmain.const_mul _).sub_const _).congr_deriv hjet'.symm |>.congr_of_eventuallyEq he

end PGM.CepsCanonDomain
