import PLAStochastic.Index.CEPS.Scaled.RootModelFrequency
import PLAStochastic.Index.CEPS.Scaled.KernelGJointJets
import PLAStochastic.Index.CEPS.Normal.TwoParameterSpatialFamily

/-! # Genuine frequency neighborhoods for explicit finite spatial kernel models -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsCumulantQuotientSpatialUnit_frequency_analyticAt (p : ℕ → ℝ)
    (N : ℕ) (lam : ℝ) (x : (ℂ × ℂ) × ℂ) :
    AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsCumulantQuotientSpatialUnit p N lam x.1.2 x.1.1 x.2) x := by
  have hb : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1) x :=
    analyticAt_fst.comp (x := x) (f := fun x : (ℂ × ℂ) × ℂ => x.1) analyticAt_fst
  have hz : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.2) x :=
    analyticAt_snd.comp (x := x) (f := fun x : (ℂ × ℂ) × ℂ => x.1) analyticAt_fst
  have hξ : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => x.2) x := analyticAt_snd
  have hP : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => cepsCgfJetPolynomial p N (x.1.1 * x.2)) x :=
    ((cepsCgfJetPolynomial_differentiable p N).analyticAt (x.1.1 * x.2)).comp
      (x := x) (f := fun x : (ℂ × ℂ) × ℂ => x.1.1 * x.2) (hb.mul hξ)
  have hT : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsCumulantQuadraticEquation p N lam x.1.2 x.1.1 x.2) x :=
    (((hξ.pow 2).mul hP).add (analyticAt_const.mul hξ)).sub
      (hz.mul (analyticAt_const.add (hb.mul analyticAt_const)))
  exact (quadraticExpUnit_joint_analyticAt
    (x.1.1, cepsCumulantQuadraticEquation p N lam x.1.2 x.1.1 x.2)).comp
      (x := x) (f := fun x : (ℂ × ℂ) × ℂ =>
        (x.1.1, cepsCumulantQuadraticEquation p N lam x.1.2 x.1.1 x.2)) (hb.prod hT)

theorem cepsCumulantJetQuotient_frequency_family (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ CepsHolomorphicSpatialFamily
      (fun x ξ => cepsCumulantJetQuotient p N lam x.2 x.1 ξ) (ball 0 B) (ball z B) R := by
  let a : ℂ × ℂ → ℂ := fun x => cepsCumulantRootModel p N lam x.2 1 N x.1
  let d : ℂ × ℂ → ℂ := fun x => cepsCumulantRootModel p N lam x.2 (-1) N x.1
  have ha : AnalyticAt ℂ a (0, z) := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne (by norm_num) 0 N
  have hd : AnalyticAt ℂ d (0, z) := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne (by norm_num) 0 N
  let S : ℝ := R + 1 + ‖a (0, z)‖ + ‖d (0, z)‖
  have ha0 : a (0, z) ∈ ball (0 : ℂ) S := by rw [mem_ball_zero_iff]; dsimp [S]; linarith [norm_nonneg (d (0, z))]
  have hd0 : d (0, z) ∈ ball (0 : ℂ) S := by rw [mem_ball_zero_iff]; dsimp [S]; linarith [norm_nonneg (a (0, z))]
  have hev : ∀ᶠ x in 𝓝 ((0, z) : ℂ × ℂ), AnalyticAt ℂ a x ∧ AnalyticAt ℂ d x ∧
      a x ∈ ball 0 S ∧ d x ∈ ball 0 S :=
    ha.eventually_analyticAt.and (hd.eventually_analyticAt.and
      ((ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0)).and
        (hd.continuousAt.eventually (isOpen_ball.mem_nhds hd0))))
  obtain ⟨B, hB, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hrect : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball ((0, z) : ℂ × ℂ) B := by
    intro x hx
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
      (show dist x.1 0 < B ∧ dist x.2 z < B from hx)
  have hda : DifferentiableOn ℂ a (ball 0 B ×ˢ ball z B) :=
    fun x hx => (hball (hrect hx)).1.differentiableAt.differentiableWithinAt
  have hdd : DifferentiableOn ℂ d (ball 0 B ×ˢ ball z B) :=
    fun x hx => (hball (hrect hx)).2.1.differentiableAt.differentiableWithinAt
  have hma : MapsTo a (ball 0 B ×ˢ ball z B) (ball 0 S) := fun _ hx => (hball (hrect hx)).2.2.1
  have hmd : MapsTo d (ball 0 B ×ˢ ball z B) (ball 0 S) := fun _ hx => (hball (hrect hx)).2.2.2
  have hF : CepsHolomorphicSpatialFamily
      (fun x ξ => cepsCumulantQuotientSpatialUnit p N lam x.2 x.1 ξ) (ball 0 B) (ball z B) S :=
    .of_differentiable (fun x _ =>
      (cepsCumulantQuotientSpatialUnit_frequency_analyticAt p N lam x).differentiableAt.differentiableWithinAt)
  exact ⟨B, hB, ((hF.dslope isOpen_ball isOpen_ball hda hma).dslope
    isOpen_ball isOpen_ball hdd hmd).mono Subset.rfl Subset.rfl
      (show R ≤ S by dsimp [S]; linarith [norm_nonneg (a (0, z)), norm_nonneg (d (0, z))])⟩

theorem cepsKernelGJetModel_frequency_family (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ CepsHolomorphicSpatialFamily
      (fun x ξ => cepsKernelGJetModel p N lam x.2 x.1 ξ) (ball 0 B) (ball z B) R := by
  obtain ⟨B, hB, hQ⟩ := cepsCumulantJetQuotient_frequency_family p hp N lam hz hne hR
  have hE : CepsHolomorphicSpatialFamily
      (fun x ξ => exp (-ξ * (1 + x.1 * lam))) (ball 0 B) (ball z B) R :=
    .of_differentiable (by fun_prop)
  have hcurve : ∀ x : (ℂ × ℂ) × ℂ, AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ =>
      (x.1.1 * (lam : ℂ), (cepsComplexScaledDiscount lam x.1.2 x.1.1, x.1.1 * x.2))) x := by
    intro x
    have hb : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1) x :=
      analyticAt_fst.comp (x := x) (f := fun x : (ℂ × ℂ) × ℂ => x.1) analyticAt_fst
    have hz : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.2) x :=
      analyticAt_snd.comp (x := x) (f := fun x : (ℂ × ℂ) × ℂ => x.1) analyticAt_fst
    exact (hb.mul analyticAt_const).prod
      ((((hb.pow 2).mul hz).mul (analyticAt_const.add (hb.mul analyticAt_const))).prod
        (hb.mul analyticAt_snd))
  have hL : CepsHolomorphicSpatialFamily
      (fun x ξ => exp (-2 * cepsCanonJetPolynomial p N (x.1 * lam)
        (cepsComplexScaledDiscount lam x.2 x.1) (x.1 * ξ))) (ball 0 B) (ball z B) R := by
    apply CepsHolomorphicSpatialFamily.of_differentiable
    intro x _
    have hp := (cepsCanonJetPolynomial_joint_analyticAt p N
      (x.1.1 * lam, (cepsComplexScaledDiscount lam x.1.2 x.1.1, x.1.1 * x.2))).comp
        (x := x) (f := fun x : (ℂ × ℂ) × ℂ =>
          (x.1.1 * (lam : ℂ), (cepsComplexScaledDiscount lam x.1.2 x.1.1, x.1.1 * x.2))) (hcurve x)
    exact (((analyticAt_const (v := (-2 : ℂ))).mul hp).cexp).differentiableAt.differentiableWithinAt
  exact ⟨B, hB, hE.mul (hQ.mul hL)⟩

end PGM
