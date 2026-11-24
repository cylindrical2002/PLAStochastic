import PLAStochastic.Index.CEPS.Scaled.RootBounds
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Complex.Schwarz

/-! # Removing the scale zero from the signed Morse chart

The divided-slope definition supplies the genuine value at zero scale.
For fixed complex drift and signed-root coordinates, it is holomorphic
in a class-controlled scale disk. Cauchy estimates give every scale jet.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

/-- Signed scaled chart, with the removable value at `b=0` retained. -/
def cepsScaledMorseChart (D θ : ℝ) (ρW : Measure ℝ) (lam r b : ℂ) : ℂ :=
  dslope (fun a => cepsMorseRoot D θ ρW (a * lam) (a * r)) 0 b

namespace CepsCanonDomain

def scaledMorseRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (lam r : ℂ) : ℝ :=
  min dom.μ₀ dom.rmax / (1 + ‖lam‖ + ‖r‖)

def scaledMorseBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) (lam r : ℂ) : ℝ :=
  2 / cepsVarLo D * ‖lam‖ + cepsChartK D * ‖r‖

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseCenter_at_zero : cepsMorseCenter D θ ρW 0 = 0 := by
  rw [cepsMorseCenter, neg_zero, (cepsCenter_hyp hW hθ hD).paramInv_zero (mem_univ _)]

include hW hθ hD in
theorem cepsScaledMorseChart_eq_div (lam r : ℂ) {b : ℂ} (hb : b ≠ 0) :
    cepsScaledMorseChart D θ ρW lam r b = cepsMorseRoot D θ ρW (b * lam) (b * r) / b := by
  unfold cepsScaledMorseChart
  rw [dslope_of_ne _ hb, slope_def_field, zero_mul, zero_mul,
    cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
    cepsMorseCenter_at_zero hW hθ hD, sub_zero, sub_zero]

include hW hθ hD in
theorem cepsScaledMorseChart_budget (lam r : ℂ) :
    DifferentiableOn ℂ (cepsScaledMorseChart D θ ρW lam r)
      (ball 0 (dom.scaledMorseRadius lam r)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.scaledMorseRadius lam r),
      ‖cepsScaledMorseChart D θ ρW lam r b‖ ≤ dom.scaledMorseBound lam r := by
  let R := dom.scaledMorseRadius lam r
  let C := dom.scaledMorseBound lam r
  let F := fun b : ℂ => cepsMorseRoot D θ ρW (b * lam) (b * r)
  have hden : 0 < 1 + ‖lam‖ + ‖r‖ := by positivity
  have hR : 0 < R := div_pos (lt_min dom.μ₀_pos dom.rmax_pos) hden
  have hC : 0 ≤ C := by
    have := cepsVarLo_pos hD; have := cepsChartK_pos hD
    unfold C CepsCanonDomain.scaledMorseBound; positivity
  have hcoords : ∀ b ∈ ball (0 : ℂ) R, ‖b * lam‖ < dom.μ₀ ∧ ‖b * r‖ < dom.rmax := by
    intro b hb
    have hn := mem_ball_zero_iff.mp hb
    have hm : ‖b‖ * (1 + ‖lam‖ + ‖r‖) < min dom.μ₀ dom.rmax :=
      (lt_div_iff₀ hden).mp hn
    rw [norm_mul, norm_mul]
    constructor
    · calc
        _ ≤ ‖b‖ * (1 + ‖lam‖ + ‖r‖) := mul_le_mul_of_nonneg_left
          (by linarith [norm_nonneg r]) (norm_nonneg b)
        _ < _ := hm.trans_le (min_le_left _ _)
    · calc
        _ ≤ ‖b‖ * (1 + ‖lam‖ + ‖r‖) := mul_le_mul_of_nonneg_left
          (by linarith [norm_nonneg lam]) (norm_nonneg b)
        _ < _ := hm.trans_le (min_le_right _ _)
  have hF : DifferentiableOn ℂ F (ball 0 R) := by
    refine (differentiableOn_cepsMorseRoot hW hθ hD).comp
      (f := fun b : ℂ => (b * lam, b * r))
      ((differentiableOn_id.mul_const lam).prodMk (differentiableOn_id.mul_const r)) ?_
    intro b hb
    obtain ⟨hm, hr⟩ := hcoords b hb
    exact ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart hm.le), mem_ball_zero_iff.mpr
      (by have := dom.rmax_r1; have := dom.rmax_pos; linarith)⟩
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [zero_mul, zero_mul, cepsMorseRoot_zero hW hθ hD
      (by simpa using cepsChartMu_pos hD hθ), cepsMorseCenter_at_zero hW hθ hD]
  have hnorm : ∀ b ∈ ball (0 : ℂ) R, ‖F b‖ ≤ C * ‖b‖ := by
    intro b hb
    obtain ⟨hm, hr⟩ := hcoords b hb
    have hc := cepsMorseCenter_norm_le_drift dom hW hθ hD hm.le
    have ht := norm_cepsMorseRoot_sub_center_le hW hθ hD (dom.μ_lt_chart hm.le)
      (show ‖b * r‖ < cepsChartRho D θ by have := dom.rmax_r1; have := dom.rmax_pos; linarith)
    calc
      _ = ‖cepsMorseCenter D θ ρW (b * lam) + (F b - cepsMorseCenter D θ ρW (b * lam))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ 2 / cepsVarLo D * ‖b * lam‖ + cepsChartK D * ‖b * r‖ := add_le_add hc ht
      _ = _ := by unfold C CepsCanonDomain.scaledMorseBound; rw [norm_mul, norm_mul]; ring
  have hmap : MapsTo F (ball 0 R) (closedBall (F 0) (R * C)) := by
    intro b hb
    rw [mem_closedBall, hF0, dist_zero_right]
    exact (hnorm b hb).trans (by nlinarith [mem_ball_zero_iff.mp hb])
  refine ⟨(differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr hF, ?_⟩
  intro b hb
  have hd := norm_dslope_le_div_of_mapsTo_ball hF hmap hb
  change ‖dslope F 0 b‖ ≤ C
  simpa only [mul_div_cancel_left₀ C hR.ne'] using hd

include hW hθ hD in
/-- Every scale jet has a polynomial budget in the fixed signed coordinates. -/
theorem cepsScaledMorseChart_scale_jet_le (lam r : ℂ) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledMorseChart D θ ρW lam r) 0‖ ≤
      (n.factorial : ℝ) * dom.scaledMorseBound lam r /
        (dom.scaledMorseRadius lam r / 2) ^ n := by
  have hR : 0 < dom.scaledMorseRadius lam r := div_pos (lt_min dom.μ₀_pos dom.rmax_pos)
    (by positivity)
  obtain ⟨hd, hb⟩ := cepsScaledMorseChart_budget dom hW hθ hD lam r
  exact norm_iteratedDeriv_le_of_ball n hR hd hb

end PGM
