import PLAStochastic.Index.CEPS.Scaled.MorseChartIdentification

/-! # Actual scaled-root joint holomorphy away from the joint drift-frequency origin

The joint origin remains a square-root point for individual roots. Symmetric
kernels must use signed-coordinate descent there.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.jointRootScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.actualRootScaleRadius lam z)
    (dom.scaledMorseJointRadius lam (1 + dom.scaledRootCoordinateBound lam z))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem jointRootScaleRadius_pos (lam : ℝ) (z : ℂ) : 0 < dom.jointRootScaleRadius lam z := by
  exact lt_min (actualRootScaleRadius_pos dom hW hθ hD lam z)
    (scaledMorseJointRadius_pos dom (lam : ℂ) (by
      unfold CepsCanonDomain.scaledRootCoordinateBound; positivity))

include hW hθ hD in
theorem cepsScaledMorseRadicand_differentiableOn_joint (lam : ℂ) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseRadicand D θ ρW lam x.2 x.1)
      (ball 0 (dom.minimumScaleRadius lam) ×ˢ univ) := by
  have hu : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseMinUnit D θ ρW (x.1 * lam))
      (ball 0 (dom.minimumScaleRadius lam) ×ˢ univ) :=
    (cepsMorseMinUnit_class_budget dom hW hθ hD).1.comp
    (differentiableOn_fst.mul_const lam)
    (fun _ hx => dom.minimumScale_mapsTo lam hx.1)
  exact (differentiableOn_snd.mul ((differentiableOn_const (1 : ℂ)).add
    (differentiableOn_fst.mul_const lam))).sub (hu.const_mul (lam ^ 2))

include hW hθ hD in
theorem cepsScaledRootCoordinate_differentiableAt_joint (lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam))
    (hr : cepsScaledMorseRadicand D θ ρW lam z b ∈ slitPlane) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsScaledRootCoordinate D θ ρW lam x.2 x.1) (b, z) :=
  (differentiableAt_sqrt hr).comp (b, z)
    (((cepsScaledMorseRadicand_differentiableOn_joint dom hW hθ hD lam) _ ⟨hb, mem_univ _⟩).differentiableAt
      ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hb, mem_univ _⟩))

include hW hθ hD in
theorem cepsScaledSignedRoot_differentiableAt_joint (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.jointRootScaleRadius lam z)) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1) (b, z) := by
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let R := 1 + dom.scaledRootCoordinateBound lam z
  have hR : 0 < R := by dsimp [R, CepsCanonDomain.scaledRootCoordinateBound]; positivity
  have hbA := ball_subset_ball (min_le_left _ _) hb
  have hbR := ball_subset_ball (min_le_left _ _) hbA
  have hsub : dom.radicandScaleRadius lam ≤ dom.minimumScaleRadius lam :=
    (radicandScaleRadius_budget dom hW hθ hD lam).2.trans
      (half_le_self (dom.minimumScaleRadius_pos lam).le)
  have hbMin := ball_subset_ball hsub hbR
  have hrad := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hbR
  have hcoord := cepsScaledRootCoordinate_differentiableAt_joint dom hW hθ hD lam hbMin hrad
  have hr : sign * r ∈ ball (0 : ℂ) R := by
    have hn := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbR
    rw [mem_ball_zero_iff, norm_mul]
    have hh := mul_le_mul hsign hn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [R]
    linarith [one_mul ‖r‖]
  have hchart : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam x.2 x.1)
      (b, sign * r) :=
    ((cepsScaledMorseChart_differentiableOn_joint dom hW hθ hD (lam : ℂ) hR) _
      ⟨ball_subset_ball (min_le_right _ _) hb, hr⟩).differentiableAt
        ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ball_subset_ball (min_le_right _ _) hb, hr⟩)
  have hd := hchart.comp (b, z) (differentiableAt_fst.prodMk (hcoord.const_mul sign))
  have hrad0 := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne
    (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)
  have he : (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 sign x.1) =ᶠ[𝓝 (b, z)]
      (fun x => cepsScaledMorseChart D θ ρW lam (sign * cepsScaledRootCoordinate D θ ρW lam x.2 x.1) x.1) := by
    have hcont : Continuous (fun x : ℂ × ℂ => cepsScaledMorseRadicand D θ ρW lam x.2 0) := by
      unfold cepsScaledMorseRadicand
      fun_prop
    have hZ := hcont.tendsto (b, z) (isOpen_slitPlane.mem_nhds hrad0)
    filter_upwards [hZ] with x hx
    have hm := (cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) x.2).1
    have hc : DifferentiableAt ℂ (cepsScaledRootCoordinate D θ ρW lam x.2) 0 :=
      (differentiableAt_sqrt hx).comp 0
        ((hm 0 (mem_ball_self (dom.minimumScaleRadius_pos lam))).differentiableAt
          (ball_mem_nhds _ (dom.minimumScaleRadius_pos lam)))
    exact cepsScaledSignedRoot_eq_fixed_chart_of_differentiable hW hθ hD lam x.2 sign hc x.1
  exact hd.congr_of_eventuallyEq he

end PGM
