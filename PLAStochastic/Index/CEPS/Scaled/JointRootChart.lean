import PLAStochastic.Index.CEPS.Scaled.SignedRootNeighborhood
import PLAStochastic.Index.CEPS.Scaled.EntranceScaleCurve

/-! # Actual joint root neighborhoods with all spatial chart bounds -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaled_joint_root_chart (N : ℕ) (M lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N M lam z))) :
    ∃ ε > 0,
      (∀ sign : ℂ, ‖sign‖ ≤ 1 → DifferentiableOn ℂ
        (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1)
        (ball b ε ×ˢ ball z ε)) ∧
      ∀ x ∈ ball b ε ×ˢ ball z ε,
        ‖x.1 * (lam : ℂ)‖ < dom.μ₀ ∧
        ‖x.1 * cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < dom.rmax ∧
        ‖cepsComplexScaledDiscount lam x.2 x.1‖ < dom.q₀ / 2 ∧
        ‖x.1‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 ∧
        cepsScaledSignedRoot D θ ρW lam x.2 1 x.1 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
        cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
        x.1 * x.2 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) := by
  have hbJ := ball_subset_ball (min_le_left _ _) hb
  have hbE := ball_subset_ball (min_le_right _ _) hb
  obtain ⟨δ, hδ, hroots⟩ := cepsScaledSignedRoot_holomorphic_near_joint dom hW hθ hD lam hz hne hbJ
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_right _ _).trans
      (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
  let R := 1 + dom.scaledRootCoordinateBound lam z
  have hR : 0 < R := by dsimp [R, CepsCanonDomain.scaledRootCoordinateBound]; positivity
  have hbRad := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbJ)
  have hbMin : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam) :=
    ball_subset_ball ((radicandScaleRadius_budget dom hW hθ hD lam).2.trans
      (half_le_self (dom.minimumScaleRadius_pos lam).le)) hbRad
  have hcoord := cepsScaledRootCoordinate_differentiableAt_joint dom hW hθ hD lam hbMin
    (cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hbRad)
  have hr : ‖b * cepsScaledRootCoordinate D θ ρW lam z b‖ < dom.rmax := by
    have hc := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad
    have hbR := mem_ball_zero_iff.mp (ball_subset_ball (min_le_right _ _) hbJ)
    have hprod := (lt_div_iff₀ (by positivity : 0 < 1 + ‖(lam : ℂ)‖ + R)).mp hbR
    have hcR : ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ 1 + ‖(lam : ℂ)‖ + R := by
      dsimp [R]
      linarith [norm_nonneg (lam : ℂ)]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hcR (norm_nonneg b)).trans_lt
      (hprod.trans_le (min_le_right _ _))
  have hbS : ‖b‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 := by
    have ht := entranceScaleCurve_product_bound dom hD N M lam hbE
    have hbase : dom.canonScaleBase ≤ dom.c₀ / 4 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    unfold CepsCanonDomain.entranceSpatialScaleRadius
    nlinarith [dom.c₀_pos]
  have hP := entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbE
  have hM := entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbE
  have hT := entranceScaleCurve_mark_mem dom hD N M lam hbE
  have hpcont := (cepsScaledSignedRoot_differentiableAt_joint dom hW hθ hD lam hz hne
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbJ).continuousAt
  have hmcont := (cepsScaledSignedRoot_differentiableAt_joint dom hW hθ hD lam hz hne
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbJ).continuousAt
  have h1 : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z), ‖x.1 * (lam : ℂ)‖ < dom.μ₀ :=
    ((continuous_fst.mul continuous_const).norm).tendsto (b, z)
      (isOpen_Iio.mem_nhds (by linarith [dom.μ₀_pos] : ‖b * (lam : ℂ)‖ < dom.μ₀))
  have h2 := (continuousAt_fst.mul hcoord.continuousAt).norm.eventually (isOpen_Iio.mem_nhds hr)
  have hcq : Continuous (fun x : ℂ × ℂ => cepsComplexScaledDiscount lam x.2 x.1) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have h3 := hcq.norm.tendsto (b, z) (isOpen_Iio.mem_nhds hq)
  have h4 : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z), ‖x.1‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 :=
    (continuous_fst.norm.mul continuous_const).tendsto (b, z) (isOpen_Iio.mem_nhds hbS)
  have h5 := hpcont.eventually (isOpen_ball.mem_nhds hP)
  have h6 := hmcont.eventually (isOpen_ball.mem_nhds hM)
  have h7 := (continuous_fst.mul continuous_snd).tendsto (b, z) (isOpen_ball.mem_nhds hT)
  have hev : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z),
      ‖x.1 * (lam : ℂ)‖ < dom.μ₀ ∧
      ‖x.1 * cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < dom.rmax ∧
      ‖cepsComplexScaledDiscount lam x.2 x.1‖ < dom.q₀ / 2 ∧
      ‖x.1‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 ∧
      cepsScaledSignedRoot D θ ρW lam x.2 1 x.1 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
      cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
      x.1 * x.2 ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) := by
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with x hx1 hx2 hx3 hx4 hx5 hx6 hx7
    exact ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  obtain ⟨γ, hγ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := min δ γ
  have hε : 0 < ε := lt_min hδ hγ
  have hsub : ball b ε ×ˢ ball z ε ⊆ ball b δ ×ˢ ball z δ := fun x hx =>
    ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  refine ⟨ε, hε, fun sign hs => (hroots sign hs).mono hsub, fun x hx => ?_⟩
  have hxb : x ∈ ball (b, z) γ := by
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
  exact hball (mem_ball.mp hxb)

end PGM
