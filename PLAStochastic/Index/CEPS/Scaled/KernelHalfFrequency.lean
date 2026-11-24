import PLAStochastic.Index.CEPS.Scaled.KernelFactorsFrequency
import PLAStochastic.Index.CEPS.Scaled.KernelHalfModelAnalytic
import PLAStochastic.Index.CEPS.Scaled.KernelFactorsActualFrequency

/-! # Genuine joint scale-frequency neighborhoods of the finite half-line factors -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

theorem cepsKernelHalfFactors_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    (hRm0 : cepsCumulantRootModel p N lam z (-1) N 0 ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelHalfBridgeJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelHalfEntranceJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  obtain ⟨C, hC, _, _, hGP, _, hQ⟩ := cepsKernelFiniteSlopes_frequency_neighborhood p hp N lam hz hne
  have hRp := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne
    (by norm_num : (1 : ℂ) ≠ 0) 0 N
  have hRm := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne
    (by norm_num : (-1 : ℂ) ≠ 0) 0 N
  obtain ⟨D, hD, hDC, hball⟩ := exists_polydisc_of_eventually_le hC
    (hRp.eventually_analyticAt.and hRm.eventually_analyticAt)
  have hsub : ball (0 : ℂ) D ×ˢ ball z D ⊆ ball (0 : ℂ) C ×ˢ ball z C :=
    fun _ hx => ⟨ball_subset_ball hDC hx.1, ball_subset_ball hDC hx.2⟩
  have hpD : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCumulantRootModel p N lam x.2 1 N x.1)
      (ball 0 D ×ˢ ball z D) := fun x hx => (hball x hx).1.differentiableAt.differentiableWithinAt
  have hmD : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCumulantRootModel p N lam x.2 (-1) N x.1)
      (ball 0 D ×ˢ ball z D) := fun x hx => (hball x hx).2.differentiableAt.differentiableWithinAt
  have hmark : DifferentiableOn ℂ (fun x : ℂ × ℂ => x.1 * x.2) (ball 0 D ×ˢ ball z D) := by fun_prop
  have hDen := (hQ.mono hsub).mul (hmark.sub hmD)
  have hx : ((0, z) : ℂ × ℂ) ∈ ball (0 : ℂ) D ×ˢ ball z D := ⟨mem_ball_self hD, mem_ball_self hD⟩
  have hDen0 : cepsCumulantJetQuotient p N lam z 0 (0 * z) *
      (0 * z - cepsCumulantRootModel p N lam z (-1) N 0) ≠ 0 := by
    rw [cepsCumulantJetQuotient_zero]
    exact mul_ne_zero (div_ne_zero (by exact_mod_cast hp.ne') (by norm_num))
      (by simpa only [zero_mul, zero_sub, neg_ne_zero] using hRm0)
  obtain ⟨B, hB, hBD, hnon⟩ := exists_polydisc_ne_zero hD
    (hDen.continuousOn.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)) hDen0
  have hsubD : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) D ×ˢ ball z D :=
    fun _ hx => ⟨ball_subset_ball hBD hx.1, ball_subset_ball hBD hx.2⟩
  have hBridge := ((hpD.sub hmD).mul (hGP.mono hsub)).mono hsubD
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (cepsCanonJetPolynomial p N (x.1 * lam)
      (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2))) (ball 0 B ×ˢ ball z B) :=
    fun x _ => (cepsMarkedCanonJetPolynomial_frequency_analyticAt p N lam x).differentiableAt.differentiableWithinAt
  have hEntrance := hL.mul ((hDen.mono hsubD).inv hnon)
  refine ⟨B, hB, ?_, ?_⟩
  · simpa only [cepsKernelHalfBridgeJetModel, Pi.mul_apply, Pi.sub_apply] using! hBridge
  · simpa only [cepsKernelHalfEntranceJetModel, div_eq_mul_inv, Pi.mul_apply, Pi.sub_apply, Pi.inv_apply] using! hEntrance

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsKernelHalfFactors_cepsJet_frequency_neighborhood (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelHalfBridgeJetModel (cepsJet f) N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelHalfEntranceJetModel (cepsJet f) N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  have hR : 0 < dom.pairPolynomialScaleBase N 0 / (1 + |lam| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N 0]
  have hGap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N 0 lam hlam hz (mem_ball_self hR)
  have hRm0 : cepsCumulantRootModel (cepsJet f) N lam z (-1) N 0 ≠ 0 := by
    rw [cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz (by norm_num) N]
    have he := norm_pos_iff.mp ((positiveMarkerGapLower_pos dom hW hθ hD).trans_le hGap)
    simpa only [zero_mul, zero_sub, neg_ne_zero] using he
  exact cepsKernelHalfFactors_frequency_neighborhood (cepsJet f)
    (cepsCumulantJet_variance_pos hW hθ hD hfW) N lam hz (Or.inl (by linarith)) hRm0

end PGM
