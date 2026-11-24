import PLAStochastic.Index.CEPS.Scaled.TrueDriftChart
import PLAStochastic.Index.CEPS.Scaled.SurrogateDriftMarkContinuity
import PLAStochastic.Index.CEPS.Scaled.SurrogateDriftSlopes
import PLAStochastic.Index.CEPS.Scaled.TruePositiveBridge

/-! # Surrogate bridge and entrance real-drift continuity on the fixed true disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open scoped Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateFactors_continuousAt_drift {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ContinuousAt (fun a : ℝ => cepsScaledSurrogateBridge dom ρW N a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledSurrogateEntrance dom ρW N a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledSurrogateHalfBridge dom ρW N a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledSurrogateMarkPrefactor dom ρW N a z b) lam := by
  obtain ⟨ε, hε, hS, ht, hp, ha, hbounds⟩ := cepsScaledTrue_drift_chart dom hW hθ hD M lam hz hb hbs
  let U := ball lam ε
  let S := dom.entranceSpatialScaleRadius lam z
  have hcoords : ∀ a ∈ U, |b * a| < dom.μ₀ / 4 ∧
      ‖cepsComplexScaledDiscount a z b‖ < dom.q₀ / 2 ∧ 0 ≤ (cepsComplexScaledDiscount a z b).re := by
    intro a ha
    obtain ⟨_, h1, h2, h3, _, _⟩ := hbounds a ha
    exact ⟨h1, h2, h3⟩
  have hpmap : MapsTo (fun a => cepsScaledSignedRoot D θ ρW a z 1 b) U (ball 0 S) :=
    fun a ha => (hbounds a ha).2.2.2.2.1
  have hamap : MapsTo (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b) U (ball 0 S) :=
    fun a ha => (hbounds a ha).2.2.2.2.2
  obtain ⟨hDenum, hNume, hGplus, hGminus⟩ := cepsScaledSurrogateSlopes_continuousOn_drift
    dom hW hθ hD hf hη N hN isOpen_ball b z hS hcoords hp ha hpmap hamap ht
  have hx : U ∈ 𝓝 lam := ball_mem_nhds _ hε
  have hDnon := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  have hB : ContinuousAt (fun a : ℝ => cepsScaledSurrogateBridge dom ρW N a z b) lam :=
    ((hGplus.continuousAt hx).neg.mul (hGminus.continuousAt hx)).div (hDenum.continuousAt hx) hDnon
  have hHalf : ContinuousAt (fun a : ℝ => cepsScaledSurrogateHalfBridge dom ρW N a z b) lam :=
    ((hp.continuousAt hx).sub (ha.continuousAt hx)).mul (hGplus.continuousAt hx)
  have hmark : ‖(b : ℂ) ^ 2 * z‖ < dom.c₀ / 2 := by
    have hn := (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp ht).le (norm_nonneg (b : ℂ))).trans_lt hS
    simpa only [pow_two, mul_assoc, norm_mul] using hn
  have hPref := cepsScaledSurrogateMarkPrefactor_continuousOn_drift dom hW hθ hD hf hη N hN isOpen_ball
    b z hmark hcoords
  have hH : ContinuousAt (fun a : ℝ => -cepsScaledSurrogateMarkPrefactor dom ρW N a z b *
      dslope (dslope (cepsScaledSurrogateG dom ρW N a z b)
        (cepsScaledSignedRoot D θ ρW a z (-1) b))
          (cepsScaledSignedRoot D θ ρW a z 1 b) ((b : ℂ) * z) /
            cepsScaledSurrogateDenominator dom ρW N a z b) lam :=
    ((hPref.continuousAt hx).neg.mul (hNume.continuousAt hx)).div (hDenum.continuousAt hx) hDnon
  have hHeq : (fun a : ℝ => cepsScaledSurrogateEntrance dom ρW N a z b) =ᶠ[𝓝 lam]
      (fun a : ℝ => -cepsScaledSurrogateMarkPrefactor dom ρW N a z b *
        dslope (dslope (cepsScaledSurrogateG dom ρW N a z b)
          (cepsScaledSignedRoot D θ ρW a z (-1) b))
            (cepsScaledSignedRoot D θ ρW a z 1 b) ((b : ℂ) * z) /
              cepsScaledSurrogateDenominator dom ρW N a z b) := by
    apply Filter.Eventually.of_forall
    intro a
    simp only [cepsScaledSurrogateEntrance, cepsScaledSurrogateMarkPrefactor, div_eq_mul_inv, mul_inv_rev]
    ring
  exact ⟨hB, hH.congr_of_eventuallyEq hHeq, hHalf, hPref.continuousAt hx⟩

end PGM
