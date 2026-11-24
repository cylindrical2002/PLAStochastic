import PLAStochastic.Index.CEPS.Canonical.RootSym

/-!
# CEPS WP3: pointwise regularity of `F` in `(μ, q, ζ)`

For a domain `dom`, a class step law and `‖μ‖ ≤ μ₀`:

* `CepsCanonDomain.sub_min_lt`: `‖q‖ ≤ q₀` puts `q` in the region `‖q - m(μ)‖ < r₁²` where
  `S, P` are holomorphic in `q` and jointly continuous;
* `CepsCanonDomain.differentiableAt_cepsF_q`: `q ↦ F(ζ; μ, q)` is holomorphic on `‖q‖ < q₀`
  (for `‖ζ‖ ≥ c₀/2`, where `D₀(ζ) ≠ 0`);
* `CepsCanonDomain.differentiableAt_cepsF_z`: `ζ ↦ F(ζ; μ, q)` is holomorphic on
  `|Re ζ| < θ/2`, `‖ζ‖ ≥ c₀/2`;
* `CepsCanonDomain.continuousAt_cepsF_mu`: `μ ↦ F(ζ; μ, q)` is continuous (complex `μ`,
  `‖μ‖ ≤ μ₀`), jointly with `ζ` on `|Re ζ| < θ/2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- `M₀` is holomorphic on the strip `|Re ζ| < θ/2`. -/
theorem differentiableAt_stepTransform_strip (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {ζ : ℂ} (hre : |ζ.re| < θ / 2) : DifferentiableAt ℂ (stepTransform ρW) ζ := by
  have h1 := (hW.integral_exp_le hθ hD.le (t := θ / 2) (by rw [abs_of_pos (by positivity)])).1
  have h2 := (hW.integral_exp_le hθ hD.le (t := -(θ / 2))
    (by rw [abs_neg, abs_of_pos (by positivity)])).1
  have := hW.isProbabilityMeasure
  have hstrip := differentiableOn_stepTransform (ρ := ρW) (a := θ / 2) h1 (by simpa using h2)
  have hmem : ζ ∈ {z : ℂ | z.re ∈ Ioo (-(θ / 2)) (θ / 2)} := abs_lt.mp hre
  have hopen : IsOpen {z : ℂ | z.re ∈ Ioo (-(θ / 2)) (θ / 2)} :=
    isOpen_Ioo.preimage continuous_re
  exact (hstrip ζ hmem).differentiableAt (hopen.mem_nhds hmem)

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

theorem two_c₀_lt : 2 * dom.c₀ < θ / 2 := by
  have h1 := dom.c₀_le
  have h2 := dom.ρA_R
  have h3 := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have h4 := cepsCgfRadius_le (D := D) (θ := θ)
  have h5 := dom.ρA_pos
  linarith

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem sub_min_lt {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2 := by
  have h := dom.norm_cepsRootR_le hW hθ hD hμ hq
  rw [← norm_cepsRootR_sq D θ ρW μ q]
  have hr := dom.rmax_pos
  have h1 := dom.rmax_r1
  have h0 := norm_nonneg (cepsRootR D θ ρW μ q)
  have : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ := by linarith
  exact pow_lt_pow_left₀ this h0 (by norm_num)

/-- The open region of `(μ, q)` where `S, P` are controlled. -/
theorem isOpen_SP_region :
    IsOpen {x : ℂ × ℂ | ‖x.1‖ < cepsChartMu D θ ∧
      ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} := by
  have hm := continuousOn_cepsMorseMin hW hθ hD
  have hg : ContinuousOn (fun x : ℂ × ℂ => x.2 - cepsMorseMin D θ ρW x.1)
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ univ) :=
    continuousOn_snd.sub (hm.comp continuousOn_fst (fun x hx => hx.1))
  have := hg.isOpen_inter_preimage (isOpen_ball.prod isOpen_univ) (isOpen_ball (x := (0 : ℂ))
    (ε := cepsChartRho D θ ^ 2))
  convert this using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_ball, dist_zero_right, mem_univ,
    and_true, mem_preimage]

theorem differentiableAt_cepsQuad_q {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) (ζ : ℂ) :
    DifferentiableAt ℂ (fun q => cepsQuad D θ ρW μ q ζ) q := by
  have hμc := dom.μ_lt_chart hμ
  obtain ⟨hS, hP⟩ := differentiableOn_cepsRootSum_q hW hθ hD hμc
  have hopen : IsOpen {q : ℂ | ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have hmem := dom.sub_min_lt hW hθ hD hμ hq
  have hS' := (hS q hmem).differentiableAt (hopen.mem_nhds hmem)
  have hP' := (hP q hmem).differentiableAt (hopen.mem_nhds hmem)
  have e : (fun q => cepsQuad D θ ρW μ q ζ) =
      fun q => ζ ^ 2 - cepsRootSum D θ ρW μ q * ζ + cepsRootProd D θ ρW μ q := by
    funext q; exact cepsQuad_eq_SP D θ ρW μ q ζ
  rw [e]
  exact ((differentiableAt_const _).sub (hS'.mul_const ζ)).add hP'

/-- `q ↦ F(ζ; μ, q)` is holomorphic where `‖q‖ < q₀`. -/
theorem differentiableAt_cepsF_q {γ μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : dom.c₀ / 2 ≤ ‖ζ‖) : DifferentiableAt ℂ (fun q => cepsF D θ ρW γ μ q ζ) q := by
  have hne := dom.cepsQuad_ne_zero hW hθ hD hμ hq hζ
  have hd : DifferentiableAt ℂ (fun q => cepsD ρW μ q ζ) q := by
    unfold cepsD
    exact (differentiableAt_const _).sub (((differentiableAt_id.neg.cexp).mul_const _).mul_const _)
  unfold cepsF
  exact (hd.mul_const _).div (dom.differentiableAt_cepsQuad_q hW hθ hD hμ hq ζ) hne

/-- `ζ ↦ F(ζ; μ, q)` is holomorphic on the strip `|Re ζ| < θ/2` off `‖ζ‖ < c₀/2`. -/
theorem differentiableAt_cepsF_z {γ μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : dom.c₀ / 2 ≤ ‖ζ‖) (hre : |ζ.re| < θ / 2) :
    DifferentiableAt ℂ (cepsF D θ ρW γ μ q) ζ := by
  have hne := dom.cepsQuad_ne_zero hW hθ hD hμ hq hζ
  have hM := differentiableAt_stepTransform_strip hW hθ hD hre
  have hd : DifferentiableAt ℂ (cepsD ρW μ q) ζ := by
    unfold cepsD
    exact (differentiableAt_const _).sub
      (((differentiableAt_const _).mul (differentiableAt_id.const_mul μ).cexp).mul hM)
  have hQ : DifferentiableAt ℂ (cepsQuad D θ ρW μ q) ζ := by
    unfold cepsQuad
    exact (differentiableAt_id.sub_const _).mul (differentiableAt_id.sub_const _)
  have e : cepsF D θ ρW γ μ q = fun z => cepsD ρW μ q z * (z ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q z := by
    funext z; rfl
  rw [e]
  exact (hd.mul ((differentiableAt_id.pow 2).sub_const _)).div hQ hne

/-- Joint continuity of `(μ, ζ) ↦ F(ζ; μ, q)` for `‖μ‖ ≤ μ₀`, `|Re ζ| < θ/2`, `‖ζ‖ ≥ c₀/2`. -/
theorem continuousAt_cepsF_mu {γ μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : dom.c₀ / 2 ≤ ‖ζ‖) (hre : |ζ.re| < θ / 2) :
    ContinuousAt (fun x : ℂ × ℂ => cepsF D θ ρW γ x.1 q x.2) (μ, ζ) := by
  have hne := dom.cepsQuad_ne_zero hW hθ hD hμ hq hζ
  have hμc := dom.μ_lt_chart hμ
  obtain ⟨hS, hP⟩ := continuousOn_cepsRootSum hW hθ hD
  have hU := isOpen_SP_region hW hθ hD
  have hmem : (μ, q) ∈ {x : ℂ × ℂ | ‖x.1‖ < cepsChartMu D θ ∧
      ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} :=
    ⟨hμc, dom.sub_min_lt hW hθ hD hμ hq⟩
  have hS' := (hS _ hmem).continuousAt (hU.mem_nhds hmem)
  have hP' := (hP _ hmem).continuousAt (hU.mem_nhds hmem)
  have hpair : ContinuousAt (fun x : ℂ × ℂ => ((x.1, q) : ℂ × ℂ)) (μ, ζ) :=
    continuousAt_fst.prodMk continuousAt_const
  have hS2 : ContinuousAt (fun x : ℂ × ℂ => cepsRootSum D θ ρW x.1 q) (μ, ζ) :=
    ContinuousAt.comp (g := fun x : ℂ × ℂ => cepsRootSum D θ ρW x.1 x.2)
      (f := fun x : ℂ × ℂ => ((x.1, q) : ℂ × ℂ)) hS' hpair
  have hP2 : ContinuousAt (fun x : ℂ × ℂ => cepsRootProd D θ ρW x.1 q) (μ, ζ) :=
    ContinuousAt.comp (g := fun x : ℂ × ℂ => cepsRootProd D θ ρW x.1 x.2)
      (f := fun x : ℂ × ℂ => ((x.1, q) : ℂ × ℂ)) hP' hpair
  have hM : ContinuousAt (stepTransform ρW) ζ :=
    (differentiableAt_stepTransform_strip hW hθ hD hre).continuousAt
  have hM2 : ContinuousAt (fun x : ℂ × ℂ => stepTransform ρW x.2) (μ, ζ) :=
    ContinuousAt.comp (g := stepTransform ρW) hM continuousAt_snd
  have hd : ContinuousAt (fun x : ℂ × ℂ => cepsD ρW x.1 q x.2) (μ, ζ) := by
    unfold cepsD
    exact continuousAt_const.sub ((continuousAt_const.mul
      ((continuousAt_fst.mul continuousAt_snd).cexp)).mul hM2)
  have hQ : ContinuousAt (fun x : ℂ × ℂ => cepsQuad D θ ρW x.1 q x.2) (μ, ζ) := by
    have e : (fun x : ℂ × ℂ => cepsQuad D θ ρW x.1 q x.2) = fun x : ℂ × ℂ =>
        x.2 ^ 2 - cepsRootSum D θ ρW x.1 q * x.2 + cepsRootProd D θ ρW x.1 q := by
      funext x; exact cepsQuad_eq_SP D θ ρW x.1 q x.2
    rw [e]
    exact ((continuousAt_snd.pow 2).sub (hS2.mul continuousAt_snd)).add hP2
  have e : (fun x : ℂ × ℂ => cepsF D θ ρW γ x.1 q x.2) = fun x : ℂ × ℂ =>
      cepsD ρW x.1 q x.2 * (x.2 ^ 2 - γ ^ 2) / cepsQuad D θ ρW x.1 q x.2 := by
    funext x; rfl
  rw [e]
  exact (hd.mul ((continuousAt_snd.pow 2).sub continuousAt_const)).div hQ hne

end

end CepsCanonDomain

end PGM
