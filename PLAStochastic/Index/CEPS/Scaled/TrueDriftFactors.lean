import PLAStochastic.Index.CEPS.Scaled.TrueDriftChart
import PLAStochastic.Index.CEPS.Scaled.TrueDriftMarkContinuity
import PLAStochastic.Index.CEPS.Scaled.TruePositiveBridge

/-! # Actual bridge and entrance real-drift continuity on the fixed true disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open scoped Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueFactors_continuousAt_drift {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ContinuousAt (fun a : ℝ => cepsScaledTrueBridge dom ρW a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledTrueEntrance dom ρW a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledTrueHalfBridge dom ρW a z b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledTrueMarkPrefactor dom ρW a z b) lam := by
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
  obtain ⟨hDenum, hNume, hGplus, hGminus⟩ := cepsScaledTrueSlopes_continuousOn_drift
    dom hW hθ hD hf hm hη isOpen_ball b z hS hcoords hp ha hpmap hamap ht
  have hDnon : ∀ a ∈ U, cepsScaledTrueDenominator dom ρW a z b ≠ 0 := fun a ha =>
    cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm a hz (hbounds a ha).1
  have hB : ContinuousOn (fun a : ℝ => cepsScaledTrueBridge dom ρW a z b) U :=
    (hGplus.neg.mul hGminus).div hDenum hDnon
  have hHalf : ContinuousOn (fun a : ℝ => cepsScaledTrueHalfBridge dom ρW a z b) U :=
    (hp.sub ha).mul hGplus
  have hmark : ‖(b : ℂ) ^ 2 * z‖ < dom.c₀ / 2 := by
    have hn := (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp ht).le (norm_nonneg (b : ℂ))).trans_lt hS
    simpa only [pow_two, mul_assoc, norm_mul] using hn
  have hPref := cepsScaledTrueMarkPrefactor_continuousOn_drift dom hW hθ hD hf hm hη isOpen_ball
    b z hmark hcoords
  have hH : ContinuousOn (fun a : ℝ => cepsScaledTrueEntrance dom ρW a z b) U :=
    (hPref.neg.mul hNume).div hDenum hDnon
  have hx : U ∈ 𝓝 lam := ball_mem_nhds _ hε
  exact ⟨hB.continuousAt hx, hH.continuousAt hx, hHalf.continuousAt hx, hPref.continuousAt hx⟩

end PGM
