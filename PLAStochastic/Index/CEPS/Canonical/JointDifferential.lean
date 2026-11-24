import PLAStochastic.Index.CEPS.Canonical.JointMuJet
import PLAStochastic.ForMathlib.Analysis.Calculus.OnePartial

/-! # Joint real differentiability of the actual canonical factor

The continuous actual drift jet supplies the first partial. Joint complex
holomorphy of the discount/spatial slice supplies the second partial.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem differentiableAt_canonL_qz {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀) (hζ : ζ.re < dom.c₀) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2) (q, ζ) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hmem : (ζ, q) ∈ {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀} := ⟨hζ, hq⟩
  have hU : IsOpen {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀} :=
    (isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  have hs := ((dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)) _ hmem).differentiableAt
      (hU.mem_nhds hmem)
  exact DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => dom.canonL ρW μ x.2 x.1)
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (q, ζ) hs
    (differentiableAt_snd.prodMk differentiableAt_fst)

include hW hθ hD in
theorem hasFDerivAt_canonL_real_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => dom.canonL ρW x.1 x.2.1 x.2.2)
      ((cepsCanonLJet D θ ρW dom.c₀ 0 μ q ζ • Complex.ofRealCLM).coprod
        ((fderiv ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2) (q, ζ)).restrictScalars ℝ))
      (μ, (q, ζ)) := by
  let x₀ : ℝ × (ℂ × ℂ) := (μ, (q, ζ))
  let F := fun (x : ℝ) (p : ℂ × ℂ) => dom.canonL ρW x p.1 p.2
  let A := fun (x : ℝ) (p : ℂ × ℂ) => cepsCanonLJet D θ ρW dom.c₀ 0 x p.1 p.2
  let F₁ := fun (x : ℝ) (p : ℂ × ℂ) => A x p • Complex.ofRealCLM
  have hpartial : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀,
      HasFDerivAt (fun y : ℝ => F y x.2) (F₁ x.1 x.2) x.1 := by
    have h1 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, |x.1| < dom.μ₀ / 4 :=
      (isOpen_lt (continuous_fst.abs) continuous_const).mem_nhds
        (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | |x.1| < dom.μ₀ / 4} from hμ)
    have h2 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, ‖x.2.1‖ < dom.q₀ / 2 :=
      (isOpen_lt (continuous_fst.comp continuous_snd).norm continuous_const).mem_nhds
        (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | ‖x.2.1‖ < dom.q₀ / 2} from hq)
    have h3 : ∀ᶠ x : ℝ × (ℂ × ℂ) in 𝓝 x₀, x.2.2.re < dom.c₀ :=
      (isOpen_lt (continuous_re.comp (continuous_snd.comp continuous_snd)) continuous_const).mem_nhds
        (show x₀ ∈ {x : ℝ × (ℂ × ℂ) | x.2.2.re < dom.c₀} from hζ)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    have hd := dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf hm hη
      (γ := 1) (by norm_num) le_rfl (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos])
      (show |x.1| < dom.μ₀ / 2 by linarith [dom.μ₀_pos]) hx2.le hx3
    convert! hd.hasFDerivAt using 1
    ext
    simp [F₁, A, smul_eq_mul, mul_comm]
  have hcontinuous : ContinuousAt (fun x : ℝ × (ℂ × ℂ) => F₁ x.1 x.2) x₀ :=
    (dom.continuousAt_cepsCanonLJet_zero_joint hW hθ hD hf hm hη hμ hq hζ).smul continuousAt_const
  have hslice := dom.differentiableAt_canonL_qz hW hθ hD
    (show |μ| ≤ dom.μ₀ by linarith [dom.μ₀_pos])
    (show ‖q‖ < dom.q₀ by linarith [dom.q₀_pos]) hζ
  exact hasFDerivAt_uncurry_of_continuous_fst hpartial hcontinuous
    (hslice.hasFDerivAt.restrictScalars ℝ)

include hW hθ hD in
theorem differentiableAt_canonL_real_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    DifferentiableAt ℝ (fun x : ℝ × (ℂ × ℂ) => dom.canonL ρW x.1 x.2.1 x.2.2)
      (μ, (q, ζ)) :=
  (dom.hasFDerivAt_canonL_real_joint hW hθ hD hf hm hη hμ hq hζ).differentiableAt

end PGM.CepsCanonDomain
