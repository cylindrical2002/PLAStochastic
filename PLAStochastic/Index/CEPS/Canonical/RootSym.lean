import PLAStochastic.Index.CEPS.Canonical.FactorDefs
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt

/-!
# CEPS WP3: the symmetric functions of the two roots

`S = β₊ + β₋` (`cepsRootSum`) and `P = β₊ β₋` (`cepsRootProd`) are even functions of
`r₊ = √(q - m(μ))` in the Morse chart, so they do not see the branch of the square root:

* `differentiableOn_cepsRootSum_q`, `differentiableOn_cepsRootProd_q`: holomorphic in `q` on
  `‖q - m(μ)‖ < r₁²` for fixed complex `‖μ‖ < μ_c`;
* `continuousOn_cepsRootSum`, `continuousOn_cepsRootProd`: jointly continuous in `(μ, q)`;
* `cepsQuad_eq_SP`: `D₀(ζ) = ζ² - S ζ + P`.

Consequences for `F = d (ζ² - γ²)/D₀`: `differentiableAt_cepsF_q` (holomorphic in `q` where
`D₀ ≠ 0`) and `continuousAt_cepsF` (continuous in `(μ, q, ζ)` where `D₀ ≠ 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `S = β₊ + β₋`. -/
def cepsRootSum (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  cepsRootPlus D θ ρW μ q + cepsRootMinus D θ ρW μ q

/-- `P = β₊ β₋`. -/
def cepsRootProd (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  cepsRootPlus D θ ρW μ q * cepsRootMinus D θ ρW μ q

theorem cepsQuad_eq_SP (D θ : ℝ) (ρW : Measure ℝ) (μ q ζ : ℂ) :
    cepsQuad D θ ρW μ q ζ = ζ ^ 2 - cepsRootSum D θ ρW μ q * ζ + cepsRootProd D θ ρW μ q := by
  rw [cepsQuad, cepsRootSum, cepsRootProd]; ring

/-- `Ψ_S(μ, ρ) = Θ(ρ, μ) + Θ(-ρ, μ)`. -/
def cepsPsiS (D θ : ℝ) (ρW : Measure ℝ) (μ ρ : ℂ) : ℂ :=
  cepsMorseRoot D θ ρW μ ρ + cepsMorseRoot D θ ρW μ (-ρ)

/-- `Ψ_P(μ, ρ) = Θ(ρ, μ) Θ(-ρ, μ)`. -/
def cepsPsiP (D θ : ℝ) (ρW : Measure ℝ) (μ ρ : ℂ) : ℂ :=
  cepsMorseRoot D θ ρW μ ρ * cepsMorseRoot D θ ρW μ (-ρ)

theorem cepsPsiS_neg (D θ : ℝ) (ρW : Measure ℝ) (μ ρ : ℂ) :
    cepsPsiS D θ ρW μ (-ρ) = cepsPsiS D θ ρW μ ρ := by
  rw [cepsPsiS, cepsPsiS, neg_neg, add_comm]

theorem cepsPsiP_neg (D θ : ℝ) (ρW : Measure ℝ) (μ ρ : ℂ) :
    cepsPsiP D θ ρW μ (-ρ) = cepsPsiP D θ ρW μ ρ := by
  rw [cepsPsiP, cepsPsiP, neg_neg, mul_comm]

theorem cepsRootSum_eq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) :
    cepsRootSum D θ ρW μ q =
      cepsPsiS D θ ρW μ (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) := rfl

theorem cepsRootProd_eq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) :
    cepsRootProd D θ ρW μ q =
      cepsPsiP D θ ρW μ (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) := rfl

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- The open chart region `‖μ‖ < μ_c`, `‖ρ‖ < r₁`. -/
theorem differentiableOn_cepsPsi :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsPsiS D θ ρW x.1 x.2)
        (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsPsiP D θ ρW x.1 x.2)
        (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) := by
  have hΘ := differentiableOn_cepsMorseRoot hW hθ hD
  have hneg : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 (-x.2))
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) := by
    intro x hx
    have hx' : (x.1, -x.2) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
      ⟨hx.1, by rw [mem_ball, dist_zero_right, norm_neg]; simpa using hx.2⟩
    have h1 := (hΘ _ hx').differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx')
    have h2 : DifferentiableAt ℂ (fun x : ℂ × ℂ => ((x.1, -x.2) : ℂ × ℂ)) x :=
      differentiableAt_fst.prodMk differentiableAt_snd.neg
    exact (DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2)
      (f := fun x : ℂ × ℂ => ((x.1, -x.2) : ℂ × ℂ)) x h1 h2).differentiableWithinAt
  exact ⟨hΘ.add hneg, hΘ.mul hneg⟩

omit hW in
theorem cepsChartRho_sq_pos : 0 < cepsChartRho D θ ^ 2 := by
  have := cepsChartRho_pos hD hθ; positivity

/-- `S` is holomorphic in `q` on `‖q - m(μ)‖ < r₁²`. -/
theorem differentiableOn_cepsRootSum_q {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    DifferentiableOn ℂ (cepsRootSum D θ ρW μ)
      {q | ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2} ∧
      DifferentiableOn ℂ (cepsRootProd D θ ρW μ)
      {q | ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2} := by
  have hr := cepsChartRho_pos hD hθ
  obtain ⟨hS, hP⟩ := differentiableOn_cepsPsi hW hθ hD
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have slice : ∀ {Ψ : ℂ → ℂ → ℂ}, DifferentiableOn ℂ (fun x : ℂ × ℂ => Ψ x.1 x.2)
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) →
      DifferentiableOn ℂ (Ψ μ) (ball 0 (cepsChartRho D θ)) := by
    intro Ψ h ρ hρ
    have h1 := (h (μ, ρ) ⟨hμ', hρ⟩).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμ', hρ⟩)
    exact (DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => Ψ x.1 x.2)
      (f := fun ρ : ℂ => ((μ, ρ) : ℂ × ℂ)) ρ h1
      ((differentiableAt_const μ).prodMk differentiableAt_id)).differentiableWithinAt
  have hS1 := differentiableOn_comp_sqrt_of_even hr (slice hS) (cepsPsiS_neg D θ ρW μ)
  have hP1 := differentiableOn_comp_sqrt_of_even hr (slice hP) (cepsPsiP_neg D θ ρW μ)
  have hmaps : MapsTo (fun q => q - cepsMorseMin D θ ρW μ)
      {q | ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2} (ball 0 (cepsChartRho D θ ^ 2)) := by
    intro q hq; rw [mem_ball, dist_zero_right]; exact hq
  have hlin : DifferentiableOn ℂ (fun q => q - cepsMorseMin D θ ρW μ)
      {q | ‖q - cepsMorseMin D θ ρW μ‖ < cepsChartRho D θ ^ 2} :=
    (differentiable_id.sub_const _).differentiableOn
  exact ⟨hS1.comp hlin hmaps, hP1.comp hlin hmaps⟩

/-- `m` is continuous on `‖μ‖ < μ_c`. -/
theorem continuousOn_cepsMorseMin :
    ContinuousOn (cepsMorseMin D θ ρW) (ball 0 (cepsChartMu D θ)) := by
  intro μ hμ
  have hμ' : ‖μ‖ < cepsChartMu D θ := by rwa [mem_ball, dist_zero_right] at hμ
  have hc := (differentiableOn_cepsMorseCenter hW hθ hD μ hμ).differentiableAt
    (isOpen_ball.mem_nhds hμ)
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ'
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hmem : cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    rw [mem_ball, dist_zero_right]; linarith
  have hψ := (differentiableOn_cepsCgf hW hθ hD _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
  have h : DifferentiableAt ℂ (cepsMorseMin D θ ρW) μ := by
    have e : cepsMorseMin D θ ρW = fun μ => cepsCgf ρW (cepsMorseCenter D θ ρW μ) +
        μ * cepsMorseCenter D θ ρW μ := by
      funext μ; rw [cepsMorseMin, cepsCgfShift]
    rw [e]
    exact (hψ.comp μ hc).add (differentiableAt_id.mul hc)
  exact h.continuousAt.continuousWithinAt

/-- `S`, `P` are jointly continuous in `(μ, q)` on `‖μ‖ < μ_c`, `‖q - m(μ)‖ < r₁²`. -/
theorem continuousOn_cepsRootSum :
    ContinuousOn (fun x : ℂ × ℂ => cepsRootSum D θ ρW x.1 x.2)
        {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} ∧
      ContinuousOn (fun x : ℂ × ℂ => cepsRootProd D θ ρW x.1 x.2)
        {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} := by
  have hr := cepsChartRho_pos hD hθ
  obtain ⟨hS, hP⟩ := differentiableOn_cepsPsi hW hθ hD
  have hS1 := continuousOn_comp_sqrt_of_even (Ψ := cepsPsiS D θ ρW) hr hS.continuousOn
    (cepsPsiS_neg D θ ρW)
  have hP1 := continuousOn_comp_sqrt_of_even (Ψ := cepsPsiP D θ ρW) hr hP.continuousOn
    (cepsPsiP_neg D θ ρW)
  have hm := continuousOn_cepsMorseMin hW hθ hD
  set U := {x : ℂ × ℂ | ‖x.1‖ < cepsChartMu D θ ∧
    ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2}
  have hmap : ContinuousOn (fun x : ℂ × ℂ => ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ)) U := by
    refine continuousOn_fst.prodMk (continuousOn_snd.sub ?_)
    exact hm.comp continuousOn_fst (fun x hx => by rw [mem_ball, dist_zero_right]; exact hx.1)
  have hmaps : MapsTo (fun x : ℂ × ℂ => ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ)) U
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2)) := by
    intro x hx
    exact ⟨by rw [mem_ball, dist_zero_right]; exact hx.1,
      by rw [mem_ball, dist_zero_right]; exact hx.2⟩
  exact ⟨hS1.comp hmap hmaps, hP1.comp hmap hmaps⟩

end

end PGM
