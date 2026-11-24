import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialUnit
import PLAStochastic.Index.CEPS.Scaled.QuotientZero
import PLAStochastic.Index.CEPS.Scaled.RootJetApprox
import PLAStochastic.Index.CEPS.Normal.MovingSecondSlopeAt
import PLAStochastic.Index.CEPS.Normal.SecondSlopeScaleFactor
import PLAStochastic.Index.CEPS.Normal.SlopePolynomial

/-! # The actual scaled quadratic quotient as a removable spatial-unit slope -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology Finset
open PGM.WienerHopf
namespace PGM

def cepsScaledUnitQuotient (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  dslope (dslope (cepsScaledQuotientSpatialUnit ρW lam z b)
    (cepsScaledSignedRoot D θ ρW lam z 1 b))
      (cepsScaledSignedRoot D θ ρW lam z (-1) b) ξ

def cepsScaledUnitQuotientAtRoot (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  cepsScaledUnitQuotient D θ ρW lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)

def cepsCumulantJetQuotient (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  dslope (dslope (cepsCumulantQuotientSpatialUnit p N lam z b)
    (cepsCumulantRootModel p N lam z 1 N b))
      (cepsCumulantRootModel p N lam z (-1) N b) ξ

def cepsCumulantJetQuotientAtRoot (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  cepsCumulantJetQuotient p N lam z b (cepsCumulantRootModel p N lam z sign N b)

theorem cepsScaledUnitQuotient_zero (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z ξ : ℂ) :
    cepsScaledUnitQuotient D θ ρW lam z 0 ξ = cepsCgfUnit ρW 0 := by
  have he : cepsScaledQuotientSpatialUnit ρW lam z 0 =
      fun ξ : ℂ => cepsCgfUnit ρW 0 * ξ ^ 2 + (lam : ℂ) * ξ + (-z) := by
    funext ξ
    simp only [cepsScaledQuotientSpatialUnit, quadraticExpUnit_zero, cepsScaledQuadraticEquation,
      zero_mul]
    ring
  unfold cepsScaledUnitQuotient
  rw [he, cepsNormal_second_dslope_quadratic]

theorem cepsCumulantJetQuotient_zero (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z ξ : ℂ) :
    cepsCumulantJetQuotient p N lam z 0 ξ = (p (cepsJetCode (.inl 0)) : ℂ) / 2 := by
  have hP : cepsCgfJetPolynomial p N 0 = (p (cepsJetCode (.inl 0)) : ℂ) / 2 := by
    simp [cepsCgfJetPolynomial, sum_range_succ']
    ring
  have he : cepsCumulantQuotientSpatialUnit p N lam z 0 =
      fun ξ : ℂ => ((p (cepsJetCode (.inl 0)) : ℂ) / 2) * ξ ^ 2 + (lam : ℂ) * ξ + (-z) := by
    funext ξ
    simp only [cepsCumulantQuotientSpatialUnit, quadraticExpUnit_zero, cepsCumulantQuadraticEquation,
      zero_mul, hP]
    ring
  unfold cepsCumulantJetQuotient
  rw [he, cepsNormal_second_dslope_quadratic]

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotient_eq_unit_of_nonzero (lam : ℝ) (z : ℂ) {b ξ : ℂ}
    (hb : b ≠ 0) {R : ℝ} (hbR : ‖b‖ * R ≤ cepsCgfRadius D θ)
    (hp : cepsScaledSignedRoot D θ ρW lam z 1 b ∈ ball 0 R)
    (hm : cepsScaledSignedRoot D θ ρW lam z (-1) b ∈ ball 0 R) (hξ : ξ ∈ ball 0 R) :
    cepsScaledQuotient D θ ρW lam z b (b * ξ) = cepsScaledUnitQuotient D θ ρW lam z b ξ := by
  have hmap (ξ : ℂ) (hξ : ξ ∈ ball 0 R) : b * ξ ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    rw [mem_ball_zero_iff, norm_mul]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hξ) (norm_pos_iff.mpr hb)).trans_le hbR
  let f : ℂ → ℂ := fun w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w
  have hf : DifferentiableOn ℂ f (ball 0 (cepsCgfRadius D θ)) := by
    have hM : DifferentiableOn ℂ (stepTransform ρW) (ball 0 (cepsCgfRadius D θ)) :=
      (differentiableOn_stepTransform_ball hW hθ hD.le).mono
      (ball_subset_ball (by have := cepsCgfRadius_le (D := D) (θ := θ); linarith))
    dsimp [f]; unfold cepsD
    exact ((differentiableOn_const (1 : ℂ)).sub
      ((((differentiableOn_id.const_mul (b * lam)).cexp).const_mul
        (Complex.exp (-cepsComplexScaledDiscount lam z b))).mul hM)).neg
  have hg : DifferentiableOn ℂ (cepsScaledQuotientSpatialUnit ρW lam z b) (ball 0 R) := by
    intro ξ hξ
    have he := cepsScaledQuotientSpatialUnit_joint_analyticAt hW hθ hD lam z (b, ξ)
      (mem_ball_zero_iff.mp (hmap ξ hξ))
    exact he.curry_right.differentiableAt.differentiableWithinAt
  have hEq : EqOn (fun ξ => f (b * ξ)) (fun ξ => b ^ 2 * cepsScaledQuotientSpatialUnit ρW lam z b ξ)
      (ball 0 R) := by
    intro ξ hξ
    exact cepsD_scaled_eq_quadraticSpatialUnit hW hθ hD lam z b ξ (mem_ball_zero_iff.mp (hmap ξ hξ))
  have hfS := (differentiableOn_dslope (isOpen_ball.mem_nhds (hmap _ hp))).mpr hf
  exact cepsNormal_second_dslope_scale_factor hb isOpen_ball hg hEq hp hm hξ
    ((hf _ (hmap _ hp)).differentiableAt (isOpen_ball.mem_nhds (hmap _ hp)))
    ((hfS _ (hmap _ hm)).differentiableAt (isOpen_ball.mem_nhds (hmap _ hm)))

variable (dom : CepsCanonDomain D θ v)

include dom hW hθ hD in
theorem cepsScaledQuotientAtRoot_eq_unit_eventually (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    cepsScaledQuotientAtRoot D θ ρW lam z sign =ᶠ[𝓝 (0 : ℂ)]
      cepsScaledUnitQuotientAtRoot D θ ρW lam z sign := by
  let a := cepsScaledSignedRoot D θ ρW lam z 1
  let d := cepsScaledSignedRoot D θ ρW lam z (-1)
  let t := cepsScaledSignedRoot D θ ρW lam z sign
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hd := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have ht := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  let R : ℝ := 1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d 0), norm_nonneg (t 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (t 0)]
  have ht0 : t 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]
  have hscale : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) (cepsCgfRadius D θ / R) :=
    ball_mem_nhds _ (div_pos (cepsCgfRadius_pos hD hθ) hR)
  filter_upwards [hscale, ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0),
    hd.continuousAt.eventually (isOpen_ball.mem_nhds hd0),
    ht.continuousAt.eventually (isOpen_ball.mem_nhds ht0)] with b hbs hab hdb htb
  by_cases hb : b = 0
  · subst b
    rw [cepsScaledQuotientAtRoot_zero hW hθ hD]
    unfold cepsScaledUnitQuotientAtRoot
    rw [cepsScaledUnitQuotient_zero, cepsCgfUnit_zero hW hθ hD]
  · have hbR : ‖b‖ * R ≤ cepsCgfRadius D θ :=
      ((lt_div_iff₀ hR).mp (mem_ball_zero_iff.mp hbs)).le
    exact cepsScaledQuotient_eq_unit_of_nonzero hW hθ hD lam z hb hbR hab hdb htb

end PGM
