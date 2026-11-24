import PLAStochastic.Index.CEPS.Scaled.SignedRootJoint

/-! # Open joint neighborhoods for both actual signed roots

The frequency neighborhood includes points to the left of the imaginary
axis. The branch conditions are paid by continuity at the chosen center.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_differentiableAt_of_branch_conditions
    (lam : ℝ) {R : ℝ} (hR : 0 < R) {b z sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hbMin : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam))
    (hbChart : b ∈ ball (0 : ℂ) (dom.scaledMorseJointRadius lam R))
    (hr : ‖cepsScaledRootCoordinate D θ ρW lam z b‖ < R)
    (hbranch : cepsScaledMorseRadicand D θ ρW lam z b ∈ slitPlane)
    (hbranchZero : cepsScaledMorseRadicand D θ ρW lam z 0 ∈ slitPlane) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1)
      (b, z) := by
  have hcoord := cepsScaledRootCoordinate_differentiableAt_joint dom hW hθ hD lam hbMin hbranch
  have hsignR : sign * cepsScaledRootCoordinate D θ ρW lam z b ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_mul]
    exact (mul_le_mul_of_nonneg_right hsign (norm_nonneg _)).trans_lt (by simpa using hr)
  have hchart := ((cepsScaledMorseChart_differentiableOn_joint dom hW hθ hD
    (lam : ℂ) hR) (b, sign * cepsScaledRootCoordinate D θ ρW lam z b)
      ⟨hbChart, hsignR⟩).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hbChart, hsignR⟩)
  have hd := hchart.comp (b, z) (differentiableAt_fst.prodMk (hcoord.const_mul sign))
  have hcont : Continuous (fun x : ℂ × ℂ => cepsScaledMorseRadicand D θ ρW lam x.2 0) := by
    unfold cepsScaledMorseRadicand
    fun_prop
  have hZ := hcont.tendsto (b, z) (isOpen_slitPlane.mem_nhds hbranchZero)
  have he : (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1) =ᶠ[𝓝 (b, z)]
      (fun x => cepsScaledMorseChart D θ ρW lam
        (sign * cepsScaledRootCoordinate D θ ρW lam x.2 x.1) x.1) := by
    filter_upwards [hZ] with x hx
    have hm := (cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) x.2).1
    have hc : DifferentiableAt ℂ (cepsScaledRootCoordinate D θ ρW lam x.2) 0 :=
      (differentiableAt_sqrt hx).comp 0
        ((hm 0 (mem_ball_self (dom.minimumScaleRadius_pos lam))).differentiableAt
          (ball_mem_nhds _ (dom.minimumScaleRadius_pos lam)))
    exact cepsScaledSignedRoot_eq_fixed_chart_of_differentiable hW hθ hD lam x.2 sign hc x.1
  exact hd.congr_of_eventuallyEq he

include hW hθ hD in
theorem cepsScaledSignedRoot_holomorphic_near_joint
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.jointRootScaleRadius lam z)) :
    ∃ ε > 0, ∀ sign : ℂ, ‖sign‖ ≤ 1 →
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1)
        (ball b ε ×ˢ ball z ε) := by
  let R := 1 + dom.scaledRootCoordinateBound lam z
  have hR : 0 < R := by dsimp [R, CepsCanonDomain.scaledRootCoordinateBound]; positivity
  have hbA := ball_subset_ball (min_le_left _ _) hb
  have hbRad := ball_subset_ball (min_le_left _ _) hbA
  have hbMin : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam) :=
    ball_subset_ball ((radicandScaleRadius_budget dom hW hθ hD lam).2.trans
      (half_le_self (dom.minimumScaleRadius_pos lam).le)) hbRad
  have hbChart : b ∈ ball (0 : ℂ) (dom.scaledMorseJointRadius lam R) :=
    ball_subset_ball (min_le_right _ _) hb
  have hbranch := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hbRad
  have hbranchZero := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne
    (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)
  have hr : ‖cepsScaledRootCoordinate D θ ρW lam z b‖ < R := by
    have hn := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad
    dsimp [R]
    linarith
  have hcoord := cepsScaledRootCoordinate_differentiableAt_joint dom hW hθ hD lam hbMin hbranch
  have hrad := ((cepsScaledMorseRadicand_differentiableOn_joint dom hW hθ hD lam)
    (b, z) ⟨hbMin, mem_univ _⟩).differentiableAt
      ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hbMin, mem_univ _⟩)
  have hc0 : Continuous (fun x : ℂ × ℂ => cepsScaledMorseRadicand D θ ρW lam x.2 0) := by
    unfold cepsScaledMorseRadicand
    fun_prop
  have h1 : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z), x.1 ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam) :=
    continuous_fst.tendsto (b, z) (isOpen_ball.mem_nhds hbMin)
  have h2 : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z), x.1 ∈ ball (0 : ℂ) (dom.scaledMorseJointRadius lam R) :=
    continuous_fst.tendsto (b, z) (isOpen_ball.mem_nhds hbChart)
  have h3 := hcoord.continuousAt.norm.eventually (isOpen_Iio.mem_nhds hr)
  have h4 := hrad.continuousAt.eventually (isOpen_slitPlane.mem_nhds hbranch)
  have h5 := hc0.tendsto (b, z) (isOpen_slitPlane.mem_nhds hbranchZero)
  have hev : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, z),
      x.1 ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam) ∧
      x.1 ∈ ball (0 : ℂ) (dom.scaledMorseJointRadius lam R) ∧
      ‖cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < R ∧
      cepsScaledMorseRadicand D θ ρW lam x.2 x.1 ∈ slitPlane ∧
      cepsScaledMorseRadicand D θ ρW lam x.2 0 ∈ slitPlane := by
    filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
    exact ⟨hx1, hx2, hx3, hx4, hx5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun sign hsign x hx => ?_⟩
  have hxball : x ∈ ball (b, z) ε := by simpa only [ball_prod_same] using hx
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hball (mem_ball.mp hxball)
  exact (cepsScaledSignedRoot_differentiableAt_of_branch_conditions dom hW hθ hD lam hR
    hsign hx1 hx2 hx3 hx4 hx5).differentiableWithinAt

end PGM
