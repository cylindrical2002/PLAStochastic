import PLAStochastic.Index.CEPS.Scaled.SurrogateOrigin

/-! # A common spatial disc for the moving scaled entrance divided differences -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.entranceSpatialScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ :=
  2 * (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z)

def CepsCanonDomain.entranceScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.surrogateRegularScaleRadius N M lam z) (dom.canonScaleRadius lam z / 8)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem entranceScale_constants (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.entranceScaleRadius N M lam z ∧ 0 < dom.entranceSpatialScaleRadius lam z := by
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    positivity
  exact ⟨lt_min (surrogateRegularScaleRadius_pos dom hW hθ hD N M lam z)
    (div_pos (canonScaleRadius_pos dom hW hθ hD lam z) (by norm_num)), by
      unfold CepsCanonDomain.entranceSpatialScaleRadius
      positivity⟩

include hD in
theorem entranceScaleCurve_product_bound (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z) < dom.canonScaleBase / 8 := by
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    positivity
  have ht := (mem_ball_zero_iff.mp hb).trans_le
    ((min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 8)))
  have he : (dom.canonScaleBase /
      (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z)) / 8 =
        dom.canonScaleBase / (8 * (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z)) := by
    rw [div_div]
    congr 1
    ring
  rw [he] at ht
  have h := (lt_div_iff₀ (by positivity : 0 < 8 * (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z))).mp ht
  nlinarith

include hW hθ hD in
theorem entranceScaleCurve_spatial_bounds (N : ℕ) (M lam : ℝ) {z b ξ : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z))
    (hξ : ξ ∈ ball (0 : ℂ) (dom.entranceSpatialScaleRadius lam z)) :
    b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖b * ξ‖ < dom.c₀ / 2 := by
  have hrad : dom.entranceScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_right _ _).trans (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))
  refine ⟨ball_subset_ball hrad hb, ?_⟩
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  have hξn := (mem_ball_zero_iff.mp hξ).le
  have hn := mul_le_mul_of_nonneg_left hξn (norm_nonneg b)
  have hbase : dom.canonScaleBase ≤ dom.c₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [norm_mul]
  unfold CepsCanonDomain.entranceSpatialScaleRadius at hn
  nlinarith [dom.c₀_pos]

include hW hθ hD in
theorem entranceScaleCurve_roots_mem (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign b : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    cepsScaledSignedRoot D θ ρW lam z sign b ∈ ball (0 : ℂ) (dom.entranceSpatialScaleRadius lam z) := by
  have hbC : b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z) :=
    ball_subset_ball (min_le_left _ _) (ball_subset_ball
      ((min_le_right _ _).trans (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hb)
  have hn := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).2 b hbC
  apply mem_ball_zero_iff.mpr
  unfold CepsCanonDomain.entranceSpatialScaleRadius
  nlinarith [norm_nonneg (cepsScaledSignedRoot D θ ρW lam z sign b), abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

include hD in
theorem entranceScaleCurve_mark_mem (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    b * z ∈ ball (0 : ℂ) (dom.entranceSpatialScaleRadius lam z) := by
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    positivity
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ 1 := by
    nlinarith [norm_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hn := mul_le_mul_of_nonneg_right hbs (Real.sqrt_nonneg ‖z‖)
  rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg z), one_mul] at hn
  apply mem_ball_zero_iff.mpr
  rw [norm_mul]
  unfold CepsCanonDomain.entranceSpatialScaleRadius
  nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

end PGM
