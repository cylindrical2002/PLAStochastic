import PLAStochastic.Index.CEPS.Canonical.MuSpatialDifferential
import PLAStochastic.Index.CEPS.Canonical.JointDifferential

/-! # The first spatial coefficient of canonical transport -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The actual coefficient `ρ = ∂ζ L(0)` obeys `∂μ ρ = -∂q ℓ`. -/
theorem hasDerivAt_canonSpatialSlope_mu {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 4) :
    HasDerivAt (fun t : ℝ => deriv (dom.canonL ρW t q) 0)
      (-deriv (fun q' => dom.canonL ρW μ q' 0) q) μ := by
  let U := {x : ℂ × ℂ | ‖x.1‖ < dom.q₀ ∧ x.2.re < dom.c₀}
  let J := fun z : ℂ => cepsCanonLJet D θ ρW dom.c₀ 0 μ q z
  let Lq := fun z : ℂ => deriv (fun q' => dom.canonL ρW μ q' z) q
  have hμ1 : |μ| ≤ dom.μ₀ := by linarith [dom.μ₀_pos]
  have hq1 : ‖q‖ < dom.q₀ := by linarith [dom.q₀_pos]
  have hq2 : ‖q‖ < dom.q₀ / 2 := by linarith [dom.q₀_pos]
  have h0 : (0 : ℂ).re < dom.c₀ := by simpa using dom.c₀_pos
  have hc2 : dom.c₀ ≤ 2 * dom.c₀ := by linarith [dom.c₀_pos]
  have hU : IsOpen U :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_re.comp continuous_snd) continuous_const)
  have hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2) U := by
    intro x hx
    exact (dom.differentiableAt_canonL_qz hW hθ hD hμ1 hx.1 hx.2).differentiableWithinAt
  have hLq : DifferentiableAt ℂ Lq 0 :=
    differentiableAt_slice_snd hU (differentiableOn_deriv_fst hU hG) ⟨hq1, h0⟩
  let V := {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀ / 2}
  have hV : IsOpen V :=
    (isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  have hJ : DifferentiableAt ℂ J 0 :=
    differentiableAt_slice_fst hV
      (dom.differentiableOn_cepsCanonLJet hW hθ hD hf hη (n := 0) (by simpa using hm)
        le_rfl hc2 hμ) ⟨h0, hq2⟩
  have he : (fun z : ℂ => J z + z * Lq z) =ᶠ[𝓝 0] (fun _ => J 0) := by
    have hspace : ∀ᶠ z : ℂ in 𝓝 0, z.re < dom.c₀ :=
      (isOpen_lt continuous_re continuous_const).mem_nhds h0
    filter_upwards [hspace] with z hz
    have ht : |μ| < dom.μ₀ / 2 := by linarith [dom.μ₀_pos]
    have ht1 := dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf hm hη
      (γ := 1) (by norm_num) le_rfl le_rfl hc2 ht hq2.le hz
    have ht0 := dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf hm hη
      (γ := 1) (by norm_num) le_rfl le_rfl hc2 ht hq2.le h0
    have htr := dom.cepsCanonL_transport_of_sobolev hW hθ hD hf hm hη
      (γ := 1) (by norm_num) le_rfl le_rfl hc2 ht hq hz
    rw [ht1.deriv, ht0.deriv] at htr
    exact htr
  have hd := hJ.hasDerivAt.add ((hasDerivAt_id (0 : ℂ)).mul hLq.hasDerivAt)
  change HasDerivAt (fun z : ℂ => J z + z * Lq z)
    (deriv J 0 + (1 * Lq 0 + id 0 * deriv Lq 0)) 0 at hd
  have hh := he.deriv_eq
  rw [hd.deriv, deriv_const] at hh
  simp only [id_eq, one_mul, zero_mul, add_zero] at hh
  have hcommute := dom.hasDerivAt_deriv_canonL_mu hW hθ hD hf hm hη hμ hq2.le h0
  exact hcommute.congr_deriv (by change deriv J 0 = -Lq 0; linear_combination hh)

end PGM.CepsCanonDomain
