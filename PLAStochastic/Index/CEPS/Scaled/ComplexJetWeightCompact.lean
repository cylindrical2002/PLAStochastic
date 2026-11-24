import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientCompact

/-! # Uniform compact finite-vector limits of the full canonical spatial weight -/

noncomputable section
open Complex Set Metric Filter Topology Finset
namespace PGM

def cepsComplexKernelJetWeight (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  cepsComplexCumulantJetQuotient p N lam z b ξ *
    exp (-2 * cepsCanonComplexJetPolynomial p N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b * ξ))

theorem cepsComplexKernelGJetModel_eq_weight (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) :
    cepsComplexKernelGJetModel p N lam z b ξ =
      exp (-ξ * (1 + b * lam)) * cepsComplexKernelJetWeight p N lam z b ξ := rfl

theorem cepsCanonComplexJetPolynomial_zero (p : ℕ → ℂ) (N : ℕ) :
    cepsCanonComplexJetPolynomial p N 0 0 0 = p (cepsJetCode (.inr (0, 0, 0))) := by
  unfold cepsCanonComplexJetPolynomial
  rw [sum_range_succ']
  simp [sum_range_succ']

def cepsFiniteKernelWeightZero (d : ℕ) (p : Fin d → ℂ) : ℂ :=
  cepsComplexJetPad d p (cepsJetCode (.inl 0)) / 2 *
    exp (-2 * cepsComplexJetPad d p (cepsJetCode (.inr (0, 0, 0))))

def cepsFiniteKernelWeightAt (d N : ℕ) (b : ℂ) (x : CepsFiniteQuotientParams d) : ℂ :=
  cepsFiniteQuotientAt d N b x * exp (-2 * cepsCanonComplexJetPolynomial
    (cepsComplexJetPad d x.1) N (b * x.2.1)
    (cepsComplexScaledDiscount x.2.1 x.2.2.1 b) (b * x.2.2.2.2.2))

theorem cepsFiniteKernelWeightZero_continuous (d : ℕ) :
    Continuous (cepsFiniteKernelWeightZero d) := by
  exact ((cepsComplexJetPad_continuous d _).div_const 2).mul
    ((continuous_const.mul (cepsComplexJetPad_continuous d _)).cexp)

theorem cepsFiniteKernelWeightAt_continuous (d N : ℕ) :
    Continuous (fun x : ℂ × CepsFiniteQuotientParams d => cepsFiniteKernelWeightAt d N x.1 x.2) := by
  have hL : Continuous (fun x : ℂ × CepsFiniteQuotientParams d => cepsCanonComplexJetPolynomial
      (cepsComplexJetPad d x.2.1) N (x.1 * x.2.2.1)
      (cepsComplexScaledDiscount x.2.2.1 x.2.2.2.1 x.1) (x.1 * x.2.2.2.2.2.2)) :=
    cepsCanonComplexJetPolynomial_continuous
      (fun i => (cepsComplexJetPad_continuous d i).comp (by fun_prop))
      (by fun_prop) (by unfold cepsComplexScaledDiscount; fun_prop) (by fun_prop) N
  exact (cepsFiniteQuotientAt_continuous d N).mul ((continuous_const.mul hL).cexp)

theorem cepsFiniteKernelWeightAt_zero (d N : ℕ) (x : CepsFiniteQuotientParams d) :
    cepsFiniteKernelWeightAt d N 0 x = cepsFiniteKernelWeightZero d x.1 := by
  simp only [cepsFiniteKernelWeightAt, cepsFiniteKernelWeightZero, cepsFiniteQuotientAt_zero,
    zero_mul, cepsComplexScaledDiscount, zero_pow (by omega : 2 ≠ 0),
    cepsCanonComplexJetPolynomial_zero]

/-- One positive scale radius pays uniform convergence of the entire canonical spatial
weight on every bounded finite-vector and independent-node parameter set. -/
theorem cepsFiniteKernelWeightAt_uniform_zero_budget (d N : ℕ) (L : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (b : ℂ) (x : CepsFiniteQuotientParams d),
      ‖b‖ ≤ δ → ‖x‖ ≤ L →
      ‖cepsFiniteKernelWeightAt d N b x - cepsFiniteKernelWeightZero d x.1‖ ≤ ε := by
  let H : ℂ × CepsFiniteQuotientParams d → ℝ := fun w =>
    ‖cepsFiniteKernelWeightAt d N w.1 w.2 - cepsFiniteKernelWeightZero d w.2.1‖
  have hH : Continuous H := ((cepsFiniteKernelWeightAt_continuous d N).sub
    ((cepsFiniteKernelWeightZero_continuous d).comp (by fun_prop))).norm
  have hzero (x : CepsFiniteQuotientParams d) : H (0, x) = 0 := by
    simp [H, cepsFiniteKernelWeightAt_zero]
  have he : ∀ x ∈ closedBall (0 : CepsFiniteQuotientParams d) L,
      ∀ᶠ w in 𝓝 ((0 : ℂ), x), H w < ε := by
    intro x _
    exact hH.continuousAt.eventually (gt_mem_nhds (by rw [hzero]; exact hε))
  have hh := (isCompact_closedBall (0 : CepsFiniteQuotientParams d) L).eventually_forall_of_forall_eventually
    (x₀ := (0 : ℂ)) (P := fun b x => H (b, x) < ε) he
  obtain ⟨r, hr, hre⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r / 2, by positivity, ?_⟩
  intro b x hb hx
  have hb' : b ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (hb.trans_lt (by linarith))
  exact (hre hb' x (mem_closedBall_zero_iff.mpr hx)).le

end PGM
