import PLAStochastic.Index.CEPS.Scaled.ComplexJetRoots
import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialUnit
import PLAStochastic.ForMathlib.Analysis.Complex.ExpUnitAlgebra

/-! # Genuine functional lifts of the finite cumulant spatial unit -/

noncomputable section
open Complex Finset
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def cepsCgfContinuousJetPolynomial (p : ℕ → ℂ) (N : ℕ) (S : C(K, ℂ)) : C(K, ℂ) :=
  ∑ j ∈ range (N + 1), ContinuousMap.const K ((j + 2).factorial : ℂ)⁻¹ * S ^ j *
    ContinuousMap.const K (p (cepsJetCode (.inl j)))

omit [CompactSpace K] in
theorem cepsCgfContinuousJetPolynomial_apply (p : ℕ → ℂ) (N : ℕ) (S : C(K, ℂ)) (s : K) :
    cepsCgfContinuousJetPolynomial p N S s = cepsCgfComplexJetPolynomial p N (S s) := by
  simp [cepsCgfContinuousJetPolynomial, cepsCgfComplexJetPolynomial]

def cepsComplexCumulantQuadraticEquation (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  ξ ^ 2 * cepsCgfComplexJetPolynomial p N (b * ξ) + (lam : ℂ) * ξ - z * (1 + b * lam)

def cepsComplexCumulantQuotientSpatialUnit (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  quadraticExpUnit b (cepsComplexCumulantQuadraticEquation p N lam z b ξ)

def cepsContinuousCumulantQuotientSpatialUnit (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ)
    (S : C(K, ℂ)) : C(K, ℂ) :=
  quadraticExpUnitAlgebra b (S ^ 2 * cepsCgfContinuousJetPolynomial p N
    (ContinuousMap.const K b * S) + ContinuousMap.const K (lam : ℂ) * S -
      ContinuousMap.const K z * (1 + ContinuousMap.const K b * ContinuousMap.const K (lam : ℂ)))

theorem cepsContinuousCumulantQuotientSpatialUnit_apply (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b : ℂ) (S : C(K, ℂ)) (s : K) :
    cepsContinuousCumulantQuotientSpatialUnit p N lam z b S s =
      cepsComplexCumulantQuotientSpatialUnit p N lam z b (S s) := by
  rw [cepsContinuousCumulantQuotientSpatialUnit, quadraticExpUnitAlgebra_apply]
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    ContinuousMap.pow_apply, ContinuousMap.const_apply, ContinuousMap.one_apply,
    cepsCgfContinuousJetPolynomial_apply, cepsComplexCumulantQuotientSpatialUnit,
    cepsComplexCumulantQuadraticEquation]

theorem cepsComplexCumulantQuotientSpatialUnit_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ)
    (z b ξ : ℂ) : cepsComplexCumulantQuotientSpatialUnit (fun i => (p i : ℂ)) N lam z b ξ =
      cepsCumulantQuotientSpatialUnit p N lam z b ξ := rfl

theorem cepsCgfContinuousJetPolynomial_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {S : E → C(K, ℂ)}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hS : AnalyticAt ℂ S x) (N : ℕ) :
    AnalyticAt ℂ (fun x => cepsCgfContinuousJetPolynomial (p x) N (S x)) x := by
  unfold cepsCgfContinuousJetPolynomial
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((analyticAt_const.mul (hS.pow j)).mul ((hp _).continuousMap_const))

/-- Every finite cumulant coordinate, scale, and frequency is analytic before taking slopes. -/
theorem cepsContinuousCumulantQuotientSpatialUnit_analyticAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ}
    {b z : E → ℂ} {S : E → C(K, ℂ)}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hb : AnalyticAt ℂ b x)
    (hz : AnalyticAt ℂ z x) (hS : AnalyticAt ℂ S x) (N : ℕ) (lam : ℝ) :
    AnalyticAt ℂ (fun x => cepsContinuousCumulantQuotientSpatialUnit (p x) N lam (z x) (b x) (S x)) x := by
  have hP := cepsCgfContinuousJetPolynomial_analyticAt hp (hb.continuousMap_const.mul hS) N
  exact quadraticExpUnitAlgebra_analyticAt hb
    ((((hS.pow 2).mul hP).add (analyticAt_const.mul hS)).sub
      (hz.continuousMap_const.mul (analyticAt_const.add (hb.continuousMap_const.mul analyticAt_const))))

/-- The scalar finite unit is entire in its spatial coordinate for every complex jet vector. -/
theorem cepsComplexCumulantQuotientSpatialUnit_differentiable (p : ℕ → ℂ) (N : ℕ)
    (lam : ℝ) (z b : ℂ) : Differentiable ℂ (cepsComplexCumulantQuotientSpatialUnit p N lam z b) := by
  intro ξ
  have hP : AnalyticAt ℂ (fun s : ℂ => cepsCgfComplexJetPolynomial p N (b * s)) ξ := by
    simpa only [Pi.mul_apply, id_eq] using!
      (cepsCgfComplexJetPolynomial_analyticAt (p := fun _ : ℂ => p) (s := fun s : ℂ => b * s)
        (x := ξ) (fun _ => analyticAt_const) (analyticAt_const.mul analyticAt_id) N)
  have hT : AnalyticAt ℂ (fun ξ : ℂ => cepsComplexCumulantQuadraticEquation p N lam z b ξ) ξ :=
    ((((analyticAt_id.pow 2).mul hP).add (analyticAt_const.mul analyticAt_id)).sub analyticAt_const)
  have ha := (quadraticExpUnit_joint_analyticAt (b, cepsComplexCumulantQuadraticEquation p N lam z b ξ)).comp
    (x := ξ) (f := fun ξ => (b, cepsComplexCumulantQuadraticEquation p N lam z b ξ))
      (analyticAt_const.prod hT)
  exact ha.differentiableAt

end PGM
