import PLAStochastic.Index.CEPS.Scaled.ComplexJetContinuity
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDependence
import PLAStochastic.Index.CEPS.Normal.SlopePolynomial
import Mathlib.Topology.Compactness.Compact

/-! # A genuine uniform compact finite-parameter budget for the quadratic quotient -/

noncomputable section
open Complex Set Metric Filter Topology Finset
namespace PGM

theorem cepsCgfComplexJetPolynomial_zero (p : ℕ → ℂ) (N : ℕ) :
    cepsCgfComplexJetPolynomial p N 0 = p (cepsJetCode (.inl 0)) / 2 := by
  unfold cepsCgfComplexJetPolynomial
  rw [sum_range_succ']
  simp
  ring

theorem cepsComplexCumulantQuotientSpatialUnit_second_slope_zero (p : ℕ → ℂ)
    (N : ℕ) (lam : ℝ) (z a d ξ : ℂ) :
    dslope (dslope (cepsComplexCumulantQuotientSpatialUnit p N lam z 0) a) d ξ =
      p (cepsJetCode (.inl 0)) / 2 := by
  have he : cepsComplexCumulantQuotientSpatialUnit p N lam z 0 =
      fun t => p (cepsJetCode (.inl 0)) / 2 * t ^ 2 + (lam : ℂ) * t + (-z) := by
    funext t
    simp only [cepsComplexCumulantQuotientSpatialUnit, quadraticExpUnit_zero,
      cepsComplexCumulantQuadraticEquation, zero_mul, cepsCgfComplexJetPolynomial_zero,
      add_zero, mul_one]
    ring
  rw [he, cepsNormal_second_dslope_quadratic]

abbrev CepsFiniteQuotientParams (d : ℕ) := (Fin d → ℂ) × (ℝ × (ℂ × (ℂ × (ℂ × ℂ))))

def cepsFiniteQuotientAt (d N : ℕ) (b : ℂ) (x : CepsFiniteQuotientParams d) : ℂ :=
  dslope (dslope (cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d x.1)
    N x.2.1 x.2.2.1 b) x.2.2.2.1) x.2.2.2.2.1 x.2.2.2.2.2

theorem cepsFiniteQuotientAt_continuous (d N : ℕ) :
    Continuous (fun x : ℂ × CepsFiniteQuotientParams d => cepsFiniteQuotientAt d N x.1 x.2) := by
  exact cepsComplexCumulantQuotientSpatialUnit_moving_second_slope_continuous
    (fun i => (cepsComplexJetPad_continuous d i).comp (by fun_prop))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) N

theorem cepsFiniteQuotientAt_zero (d N : ℕ) (x : CepsFiniteQuotientParams d) :
    cepsFiniteQuotientAt d N 0 x = cepsComplexJetPad d x.1 (cepsJetCode (.inl 0)) / 2 :=
  cepsComplexCumulantQuotientSpatialUnit_second_slope_zero _ N _ _ _ _ _

/-- The radius is chosen before every bounded finite vector, drift, frequency, and three
independent spatial nodes. It follows from continuity of the actual removable slopes. -/
theorem cepsFiniteQuotientAt_uniform_zero_budget (d N : ℕ) (L : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (b : ℂ) (x : CepsFiniteQuotientParams d),
      ‖b‖ ≤ δ → ‖x‖ ≤ L →
      ‖cepsFiniteQuotientAt d N b x - cepsComplexJetPad d x.1 (cepsJetCode (.inl 0)) / 2‖ ≤ ε := by
  let H : ℂ × CepsFiniteQuotientParams d → ℝ := fun w =>
    ‖cepsFiniteQuotientAt d N w.1 w.2 - cepsComplexJetPad d w.2.1 (cepsJetCode (.inl 0)) / 2‖
  have hH : Continuous H := ((cepsFiniteQuotientAt_continuous d N).sub
    (((cepsComplexJetPad_continuous d (cepsJetCode (.inl 0))).comp
      (by fun_prop)).div_const 2)).norm
  have hzero (x : CepsFiniteQuotientParams d) : H (0, x) = 0 := by
    simp [H, cepsFiniteQuotientAt_zero]
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
