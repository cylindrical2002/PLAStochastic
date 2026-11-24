import PLAStochastic.Index.CEPS.Scaled.TrueEntranceFrequency
import PLAStochastic.Index.CEPS.Scaled.HalfFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.TrueMarkFrequency
import PLAStochastic.Index.CEPS.Scaled.TrueHalfEntrance

/-! # A quantitative pole-free zero-frequency neighborhood of the actual half entrance -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueHalfZeroFrequencyBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.trueEntranceFrequencyRadius
    (min (dom.positiveFrequencyRadius / 2)
      (min (dom.positiveMarkerGapLower * dom.positiveFrequencyRadius / (4 * dom.c₀))
        (dom.positiveMarkerGapLower / 4)))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueHalfZeroFrequencyBase_pos : 0 < dom.trueHalfZeroFrequencyBase := by
  have := trueEntranceFrequencyRadius_pos dom hD
  have := positiveFrequencyRadius_pos dom hW hθ hD
  have := positiveMarkerGapLower_pos dom hW hθ hD
  have := dom.c₀_pos
  unfold CepsCanonDomain.trueHalfZeroFrequencyBase
  positivity

include hW hθ hD in
theorem cepsScaledTrueHalf_zero_frequency_root_bound (M lam : ℝ) (_hlam : 1 ≤ lam)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0))
    {ζ : ℂ} (hζ : ζ ∈ ball 0 dom.positiveFrequencyRadius) :
    ‖cepsScaledSignedRoot D θ ρW lam ζ (-1) b‖ ≤ dom.c₀ / (4 * b) := by
  have hμ := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs).1
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq := (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam (by simp) hb hbs
    (ball_subset_ball (positiveFrequencyRadius_le dom) hζ)).1.le
  have he := cepsScaledSignedRoot_minus_actual hW hθ hD hb (z := ζ) (dom.μ_lt_chart hμn)
  rw [he, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hq' : cepsScaledDiscount b lam ζ = cepsComplexScaledDiscount lam ζ b := by
    simp only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  rw [hq']
  exact (div_le_div_of_nonneg_right (dom.norm_rootMinus_le hW hθ hD hμn hq) hb.le).trans_eq
    (by ring)

include hW hθ hD in
theorem cepsScaledTrueHalf_zero_frequency_marker_gap (M lam : ℝ) (hlam : 1 ≤ lam)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0))
    {ζ : ℂ} (hζ : ζ ∈ ball 0 (dom.trueHalfZeroFrequencyBase * b)) :
    dom.positiveMarkerGapLower / 2 ≤
      ‖(b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b‖ := by
  let r := dom.positiveFrequencyRadius
  let g := dom.positiveMarkerGapLower
  have hr : 0 < r := positiveFrequencyRadius_pos dom hW hθ hD
  have hg : 0 < g := positiveMarkerGapLower_pos dom hW hθ hD
  have hc : 0 < dom.c₀ := dom.c₀_pos
  have hn : ‖ζ‖ < dom.trueHalfZeroFrequencyBase * b := mem_ball_zero_iff.mp hζ
  have hbaseR : dom.trueHalfZeroFrequencyBase ≤ r / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbaseG : dom.trueHalfZeroFrequencyBase ≤ g * r / (4 * dom.c₀) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbaseT : dom.trueHalfZeroFrequencyBase ≤ g / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb0 : 0 ≤ dom.trueHalfZeroFrequencyBase := (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le
  have hζr : ζ ∈ ball 0 (r / 2) := mem_ball_zero_iff.mpr
    (hn.trans_le ((mul_le_of_le_one_right hb0 hb1).trans hbaseR))
  have hd := (cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD
    M lam hlam (by simp) hb hbs).2
  have hvar := norm_sub_le_of_ball_half hr hd
    (fun ζ hζ => cepsScaledTrueHalf_zero_frequency_root_bound dom hW hθ hD M lam hlam hb hbs hζ)
    hζr (mem_ball_self (half_pos hr))
  simp only [sub_zero] at hvar
  have hvarB : ‖cepsScaledSignedRoot D θ ρW lam ζ (-1) b -
      cepsScaledSignedRoot D θ ρW lam 0 (-1) b‖ ≤ g / 4 := by
    apply hvar.trans
    have he : 4 * (dom.c₀ / (4 * b)) / r = dom.c₀ / (b * r) := by ring
    rw [he]
    have hn' := hn.le.trans (mul_le_mul_of_nonneg_right hbaseG hb.le)
    exact (mul_le_mul_of_nonneg_left hn' (by positivity : 0 ≤ dom.c₀ / (b * r))).trans_eq
      (by field_simp [hc.ne'])
  have ht : ‖(b : ℂ) * ζ‖ ≤ g / 4 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb]
    exact (mul_le_of_le_one_left (norm_nonneg ζ) hb1).trans
      (hn.le.trans ((mul_le_of_le_one_right hb0 hb1).trans hbaseT))
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam 0)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam 0) hbs)
  have hbP : (b : ℂ) ∈ ball (0 : ℂ)
      (dom.pairPolynomialScaleBase 0 M / (1 + |lam| + Real.sqrt ‖(0 : ℂ)‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hbD
  have hgap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD 0 M lam hlam (by simp) hbP
  simp only [mul_zero, zero_sub, norm_neg] at hgap
  have htri : ‖cepsScaledSignedRoot D θ ρW lam 0 (-1) b‖ ≤
      ‖(b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b‖ +
        ‖(b : ℂ) * ζ‖ +
          ‖cepsScaledSignedRoot D θ ρW lam ζ (-1) b -
            cepsScaledSignedRoot D θ ρW lam 0 (-1) b‖ := by
    have he : cepsScaledSignedRoot D θ ρW lam 0 (-1) b =
        -((b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b) +
          (b : ℂ) * ζ - (cepsScaledSignedRoot D θ ρW lam ζ (-1) b -
            cepsScaledSignedRoot D θ ρW lam 0 (-1) b) := by ring
    calc
      _ = _ := congrArg norm he
      _ ≤ _ := by
        have hsub := norm_sub_le
          (-((b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b) + (b : ℂ) * ζ)
          (cepsScaledSignedRoot D θ ρW lam ζ (-1) b -
            cepsScaledSignedRoot D θ ρW lam 0 (-1) b)
        have hadd := norm_add_le
          (-((b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b)) ((b : ℂ) * ζ)
        rw [norm_neg] at hadd
        linarith
  change g ≤ ‖cepsScaledSignedRoot D θ ρW lam 0 (-1) b‖ at hgap
  linarith

include hW hθ hD in
theorem trueHalfZeroFrequency_disc_subset_entrance {b : ℝ} (hb1 : b ≤ 1) :
    ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b) ⊆ ball 0 dom.trueEntranceFrequencyRadius :=
  ball_subset_ball ((mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1).trans
    (min_le_left _ _))

include hW hθ hD in
theorem trueHalfZeroFrequency_disc_subset_positive {b : ℝ} (hb1 : b ≤ 1) :
    ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b) ⊆ ball 0 dom.positiveFrequencyRadius :=
  ball_subset_ball ((mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1).trans
    (((min_le_right _ _).trans (min_le_left _ _)).trans
      (half_le_self (positiveFrequencyRadius_pos dom hW hθ hD).le)))

include hW hθ hD in
theorem cepsScaledTrueHalfEntrance_zero_frequency_budget (M lam : ℝ) (hlam : 1 ≤ lam)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueHalfEntrance dom ρW lam ζ b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) ∧
    ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      ‖cepsScaledTrueHalfEntrance dom ρW lam ζ b‖ ≤ 2 * dom.trueHalfEntranceConstant := by
  obtain ⟨hP, hPb⟩ := cepsScaledTrueMarkPrefactor_zero_frequency_budget dom hW hθ hD M lam hb hb1 hbs
  have hE := trueHalfZeroFrequency_disc_subset_entrance dom hW hθ hD hb1
  have hR := trueHalfZeroFrequency_disc_subset_positive dom hW hθ hD hb1
  have hgap : ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      dom.positiveMarkerGapLower / 2 ≤
        ‖(b : ℂ) * ζ - cepsScaledSignedRoot D θ ρW lam ζ (-1) b‖ := fun ζ hζ =>
    cepsScaledTrueHalf_zero_frequency_marker_gap dom hW hθ hD M lam hlam hb hb1 hbs hζ
  have hg : 0 < dom.positiveMarkerGapLower / 2 := half_pos (positiveMarkerGapLower_pos dom hW hθ hD)
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => (b : ℂ) * ζ -
      cepsScaledSignedRoot D θ ρW lam ζ (-1) b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) :=
    (differentiableOn_id.const_mul (b : ℂ)).sub
      (((cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD
        M lam hlam (by simp) hb hbs).2).mono hR)
  refine ⟨(hP.mono hE).div hd (fun ζ hζ => norm_pos_iff.mp (hg.trans_le (hgap ζ hζ))), ?_⟩
  intro ζ hζ
  unfold cepsScaledTrueHalfEntrance
  rw [norm_div]
  have := cepsVarLo_pos hD
  exact (div_le_div₀ (by positivity : 0 ≤ Real.exp dom.normalLogBound * (4 / cepsVarLo D))
    (hPb ζ (hE hζ)) hg (hgap ζ hζ)).trans_eq (by
      unfold CepsCanonDomain.trueHalfEntranceConstant
      ring)

end PGM
