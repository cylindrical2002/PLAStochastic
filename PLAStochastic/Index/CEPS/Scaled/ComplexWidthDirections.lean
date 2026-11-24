import PLAStochastic.Index.CEPS.Scaled.ComplexRootNorm
import PLAStochastic.Index.CEPS.Scaled.SurrogateOrigin

/-! # Individual root sectors retaining the actual complex scaled width -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.complexDirectionScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.centerUnitSectorRadius (1 / (8 * Real.sqrt v * dom.complexIndividualRootBound))

def CepsCanonDomain.complexDirectionScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.surrogateRegularScaleRadius N M lam z) (dom.complexDirectionScaleBase / (1 + |lam|))

private theorem re_mul_one_add_lower {a u : ℂ} {R H c : ℝ}
    (hR : 0 ≤ R) (hH : 0 < H) (_hc : 0 ≤ c) (hre : 2 * c * R ≤ a.re)
    (hn : ‖a‖ ≤ H * R) (hu : ‖u‖ ≤ c / H) : c * R ≤ (a * (1 + u)).re := by
  have hnorm : ‖a * u‖ ≤ c * R := by
    rw [norm_mul]
    calc
      _ ≤ (H * R) * (c / H) := mul_le_mul hn hu (norm_nonneg _) (mul_nonneg hH.le hR)
      _ = _ := by field_simp
  have hneg := (neg_le_abs (a * u).re).trans ((abs_re_le_norm _).trans hnorm)
  rw [mul_add, mul_one, add_re]
  linarith

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem complexDirectionScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.complexDirectionScaleRadius N M lam z := by
  have hH := complexIndividualRootBound_pos dom hW hθ hD
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hbase : 0 < dom.complexDirectionScaleBase :=
    lt_min (centerUnitSectorRadius_pos dom hW hθ hD) (by positivity)
  exact lt_min (surrogateRegularScaleRadius_pos dom hW hθ hD N M lam z) (div_pos hbase (by positivity))

theorem complexDirectionScaleCurve_bounds (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2) ∧
      b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius ∧
      ‖b * (lam : ℂ)‖ ≤ (1 / (8 * Real.sqrt v)) / dom.complexIndividualRootBound := by
  have hsub : dom.complexDirectionScaleRadius N M lam z ≤ dom.canonScaleRadius lam z / 2 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht : ‖b‖ * (1 + |lam|) < dom.complexDirectionScaleBase :=
    (lt_div_iff₀ (by positivity : 0 < 1 + |lam|)).mp
      ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  have hnorm : ‖b * (lam : ℂ)‖ < dom.complexDirectionScaleBase := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg b]
  refine ⟨ball_subset_ball hsub hb, mem_ball_zero_iff.mpr (hnorm.trans_le (min_le_left _ _)), ?_⟩
  apply (hnorm.le.trans (min_le_right _ _)).trans_eq
  ring

include hW hθ hD in
theorem cepsScaledRoot_complex_width_directions (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    (lam ≤ 0 → ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * Real.sqrt v) ≤
      (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) ∧
    (0 ≤ lam → ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * Real.sqrt v) ≤
      (-cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  obtain ⟨hhalf, hμ, hsmall⟩ := complexDirectionScaleCurve_bounds dom N M lam hb
  have hH := complexIndividualRootBound_pos dom hW hθ hD
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hdirs := cepsScaledRoot_complex_directions dom hW hθ hD lam hz hhalf hμ
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  have he : 2 * (1 / (8 * Real.sqrt v)) * R = R / (4 * Real.sqrt v) := by ring
  constructor
  · intro hlam
    have hn := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hhalf hμ
    have h := re_mul_one_add_lower (norm_nonneg _) hH (by positivity)
      (by rw [he]; exact hdirs.1 hlam) hn hsmall
    simpa only [div_mul_eq_mul_div, one_mul] using h
  · intro hlam
    have hn := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hhalf hμ
    have h := re_mul_one_add_lower (a := -cepsScaledSignedRoot D θ ρW lam z (-1) b)
      (norm_nonneg _) hH (by positivity) (by rw [he]; exact hdirs.2 hlam) (by simpa using hn) hsmall
    simpa only [div_mul_eq_mul_div, one_mul] using h

include hW hθ hD in
theorem cepsScaledRootPlus_complex_exp_decay (N : ℕ) (M lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    ‖exp (-cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam))‖ ≤
      Real.exp (-dom.scaledCoordinateLower lam z / (8 * Real.sqrt v)) := by
  have hdir := (cepsScaledRoot_complex_width_directions dom hW hθ hD N M lam hz hb).1 hlam
  have hbS : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) :=
    ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb)
  have hcoord := cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbS
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hlo := (div_le_div_of_nonneg_right hcoord (by positivity : 0 ≤ 8 * Real.sqrt v)).trans hdir
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have he : -cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam) =
      -(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)) := by ring
  rw [he, neg_re]
  simpa only [neg_div] using neg_le_neg hlo

end PGM
