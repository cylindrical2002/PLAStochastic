import PLAStochastic.Index.CEPS.Canonical.FactorPointwise
import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-!
# CEPS WP3: joint holomorphy of the symmetric root functions

By Osgood's lemma the even-square-root composition `G(μ, w) = Ψ(μ, √w)` of the jointly
holomorphic chart functions `Ψ_S, Ψ_P` is jointly holomorphic in `(μ, w)`
(`differentiableOn_cepsG`); composing with `(μ, q) ↦ (μ, q - m(μ))` gives joint holomorphy of
`S = β₊ + β₋` and `P = β₊ β₋` in complex `(μ, q)` on
`V = {‖μ‖ < μ_c, ‖q - m(μ)‖ < r₁²}` (`differentiableOn_cepsRootSum_joint`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `m` is holomorphic on `‖μ‖ < μ_c`. -/
theorem differentiableOn_cepsMorseMin :
    DifferentiableOn ℂ (cepsMorseMin D θ ρW) (ball 0 (cepsChartMu D θ)) := by
  intro μ hμ
  have hμ' : ‖μ‖ < cepsChartMu D θ := by rwa [mem_ball, dist_zero_right] at hμ
  have hc := (differentiableOn_cepsMorseCenter hW hθ hD μ hμ).differentiableAt
    (isOpen_ball.mem_nhds hμ)
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ'
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hmem : cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    rw [mem_ball, dist_zero_right]; linarith
  have hψ := (differentiableOn_cepsCgf hW hθ hD _ hmem).differentiableAt
    (isOpen_ball.mem_nhds hmem)
  have e : cepsMorseMin D θ ρW = fun μ => cepsCgf ρW (cepsMorseCenter D θ ρW μ) +
      μ * cepsMorseCenter D θ ρW μ := by
    funext μ; rw [cepsMorseMin, cepsCgfShift]
  rw [e]
  exact ((hψ.comp μ hc).add (differentiableAt_id.mul hc)).differentiableWithinAt

/-- Joint holomorphy of `G(μ, w) = Ψ(μ, √w)` for `Ψ = Ψ_S, Ψ_P`. -/
theorem differentiableOn_cepsG :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsPsiS D θ ρW x.1 (Complex.sqrt x.2))
        (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2)) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsPsiP D θ ρW x.1 (Complex.sqrt x.2))
        (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2)) := by
  have hr := cepsChartRho_pos hD hθ
  obtain ⟨hS, hP⟩ := differentiableOn_cepsPsi hW hθ hD
  have hsq : ∀ w ∈ ball (0 : ℂ) (cepsChartRho D θ ^ 2),
      Complex.sqrt w ∈ ball (0 : ℂ) (cepsChartRho D θ) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw ⊢
    exact norm_sqrt_lt hr hw
  have gen : ∀ {Ψ : ℂ → ℂ → ℂ}, DifferentiableOn ℂ (fun x : ℂ × ℂ => Ψ x.1 x.2)
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) →
      (∀ μ ρ, Ψ μ (-ρ) = Ψ μ ρ) →
      DifferentiableOn ℂ (fun x : ℂ × ℂ => Ψ x.1 (Complex.sqrt x.2))
        (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2)) := by
    intro Ψ hΨ heven
    refine osgood (isOpen_ball.prod isOpen_ball)
      (continuousOn_comp_sqrt_of_even hr hΨ.continuousOn heven) ?_ ?_
    · intro x hx
      have hmem : (x.1, Complex.sqrt x.2) ∈
          ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) := ⟨hx.1, hsq _ hx.2⟩
      have h1 := (hΨ _ hmem).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
      exact DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => Ψ x.1 x.2)
        (f := fun z : ℂ => ((z, Complex.sqrt x.2) : ℂ × ℂ)) x.1 h1
        (differentiableAt_id.prodMk (differentiableAt_const _))
    · intro x hx
      have hslice : DifferentiableOn ℂ (Ψ x.1) (ball 0 (cepsChartRho D θ)) := by
        intro ρ hρ
        have hmem : (x.1, ρ) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
          ⟨hx.1, hρ⟩
        have h1 := (hΨ _ hmem).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
        exact (DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => Ψ x.1 x.2)
          (f := fun ρ : ℂ => ((x.1, ρ) : ℂ × ℂ)) ρ h1
          ((differentiableAt_const _).prodMk differentiableAt_id)).differentiableWithinAt
      exact (differentiableOn_comp_sqrt_of_even hr hslice (heven x.1) x.2 hx.2).differentiableAt
        (isOpen_ball.mem_nhds hx.2)
  exact ⟨gen hS (cepsPsiS_neg D θ ρW), gen hP (cepsPsiP_neg D θ ρW)⟩

/-- **Joint holomorphy of `S` and `P`** in complex `(μ, q)` on
`V = {‖μ‖ < μ_c, ‖q - m(μ)‖ < r₁²}`. -/
theorem differentiableOn_cepsRootSum_joint :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsRootSum D θ ρW x.1 x.2)
        {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsRootProd D θ ρW x.1 x.2)
        {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} := by
  obtain ⟨hGS, hGP⟩ := differentiableOn_cepsG hW hθ hD
  have hm := differentiableOn_cepsMorseMin hW hθ hD
  have hmap : ∀ x ∈ {x : ℂ × ℂ | ‖x.1‖ < cepsChartMu D θ ∧
      ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2},
      DifferentiableAt ℂ (fun x : ℂ × ℂ => ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ)) x ∧
        ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ) ∈
          ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2) := by
    intro x hx
    have hx1 : x.1 ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rw [mem_ball, dist_zero_right]; exact hx.1
    have hmd := (hm _ hx1).differentiableAt (isOpen_ball.mem_nhds hx1)
    refine ⟨differentiableAt_fst.prodMk (differentiableAt_snd.sub
      (DifferentiableAt.fun_comp' (g := cepsMorseMin D θ ρW) (f := fun x : ℂ × ℂ => x.1) x hmd
        differentiableAt_fst)), hx1, ?_⟩
    rw [mem_ball, dist_zero_right]; exact hx.2
  have gen : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableOn ℂ g
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ ^ 2)) →
      DifferentiableOn ℂ (fun x : ℂ × ℂ => g ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ))
        {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2} := by
    intro g hg x hx
    obtain ⟨hd, hmem⟩ := hmap x hx
    have h1 := (hg _ hmem).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
    exact (DifferentiableAt.fun_comp' (g := g)
      (f := fun x : ℂ × ℂ => ((x.1, x.2 - cepsMorseMin D θ ρW x.1) : ℂ × ℂ)) x h1 hd).differentiableWithinAt
  exact ⟨gen hGS, gen hGP⟩

end

end PGM
