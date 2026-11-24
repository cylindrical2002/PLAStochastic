import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientLift
import PLAStochastic.Index.CEPS.Scaled.KernelGJetModel

/-! # Genuine analytic compact-function spatial kernel for complex finite jets -/

noncomputable section
open Complex Finset
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def cepsCanonContinuousJetPolynomial (p : ℕ → ℂ) (N : ℕ) (μ q : ℂ) (Z : C(K, ℂ)) : C(K, ℂ) :=
  ∑ j ∈ range (N + 1), ContinuousMap.const K ((j.factorial : ℂ)⁻¹ * μ ^ j) *
    ∑ m ∈ range (N + 1), ContinuousMap.const K (m.factorial : ℂ)⁻¹ * Z ^ m *
      ∑ n ∈ range (N + 1), ContinuousMap.const K
        ((n.factorial : ℂ)⁻¹ * q ^ n * p (cepsJetCode (.inr (j, m, n))))

omit [CompactSpace K] in
theorem cepsCanonContinuousJetPolynomial_apply (p : ℕ → ℂ) (N : ℕ) (μ q : ℂ) (Z : C(K, ℂ))
    (k : K) : cepsCanonContinuousJetPolynomial p N μ q Z k =
      cepsCanonComplexJetPolynomial p N μ q (Z k) := by
  simp [cepsCanonContinuousJetPolynomial, cepsCanonComplexJetPolynomial]

theorem cepsCanonContinuousJetPolynomial_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {μ q : E → ℂ} {Z : E → C(K, ℂ)}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hμ : AnalyticAt ℂ μ x)
    (hq : AnalyticAt ℂ q x) (hZ : AnalyticAt ℂ Z x) (N : ℕ) :
    AnalyticAt ℂ (fun x => cepsCanonContinuousJetPolynomial (p x) N (μ x) (q x) (Z x)) x := by
  unfold cepsCanonContinuousJetPolynomial
  apply Finset.analyticAt_fun_sum
  intro j _
  apply ((analyticAt_const.mul (hμ.pow j)).continuousMap_const).mul
  apply Finset.analyticAt_fun_sum
  intro m _
  apply (analyticAt_const.mul (hZ.pow m)).mul
  apply Finset.analyticAt_fun_sum
  intro n _
  exact (((analyticAt_const.mul (hq.pow n)).mul (hp _)).continuousMap_const)

def cepsComplexKernelGJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  exp (-ξ * (1 + b * lam)) * (cepsComplexCumulantJetQuotient p N lam z b ξ *
    exp (-2 * cepsCanonComplexJetPolynomial p N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b * ξ)))

theorem cepsComplexKernelGJetModel_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) :
    cepsComplexKernelGJetModel (fun i => (p i : ℂ)) N lam z b ξ = cepsKernelGJetModel p N lam z b ξ := by
  simp only [cepsComplexKernelGJetModel, cepsKernelGJetModel,
    cepsComplexCumulantJetQuotient_real, cepsCanonComplexJetPolynomial_real]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cepsContinuousKernelGJetModel (p : E → ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b : E → ℂ) (X : E → C(K, ℂ)) (u : E) : C(K, ℂ) :=
  NormedSpace.exp (-X u * (1 + ContinuousMap.const K (b u) * ContinuousMap.const K (lam : ℂ))) *
    (cepsContinuousCumulantJetQuotient p N lam z b X u *
      NormedSpace.exp (ContinuousMap.const K (-2 : ℂ) *
        cepsCanonContinuousJetPolynomial (p u) N (b u * lam)
          (cepsComplexScaledDiscount lam (z u) (b u)) (ContinuousMap.const K (b u) * X u)))

theorem cepsContinuousKernelGJetModel_apply {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} (X : E → C(K, ℂ)) {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (k : K) :
    cepsContinuousKernelGJetModel p N lam z b X x k =
      cepsComplexKernelGJetModel (p x) N lam (z x) (b x) (X x k) := by
  simp only [cepsContinuousKernelGJetModel, ContinuousMap.mul_apply,
    continuousMap_exp_apply, ContinuousMap.neg_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, ContinuousMap.const_apply, cepsCanonContinuousJetPolynomial_apply,
    cepsContinuousCumulantJetQuotient_apply N lam X hp hb hz, cepsComplexKernelGJetModel]

theorem cepsContinuousKernelGJetModel_analyticAt {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} {X : E → C(K, ℂ)} {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (hX : AnalyticAt ℂ X x)
    (hv : p x (cepsJetCode (.inl 0)) ≠ 0)
    (hsv : 2 / p x (cepsJetCode (.inl 0)) ∈ slitPlane)
    (hsz : z x + (lam : ℂ) ^ 2 / (2 * p x (cepsJetCode (.inl 0))) ∈ slitPlane)
    (hgapP : cepsComplexCumulantRootGap (p x) lam (z x) 1 ≠ 0)
    (hgapM : cepsComplexCumulantRootGap (p x) lam (z x) (-1) ≠ 0) :
    AnalyticAt ℂ (cepsContinuousKernelGJetModel p N lam z b X) x := by
  have hQ := cepsContinuousCumulantJetQuotient_analyticAt N lam hp hb hz hX hv hsv hsz hgapP hgapM
  have hμ : AnalyticAt ℂ (fun u => b u * lam) x := hb.mul analyticAt_const
  have hq : AnalyticAt ℂ (fun u => cepsComplexScaledDiscount lam (z u) (b u)) x := by
    unfold cepsComplexScaledDiscount
    exact ((hb.pow 2).mul hz).mul (analyticAt_const.add (hb.mul analyticAt_const))
  have hL := cepsCanonContinuousJetPolynomial_analyticAt hp hμ hq (hb.continuousMap_const.mul hX) N
  have hE : AnalyticAt ℂ (fun u => NormedSpace.exp
      (-X u * (1 + ContinuousMap.const K (b u) * ContinuousMap.const K (lam : ℂ)))) x :=
    (hX.neg.mul (analyticAt_const.add (hb.continuousMap_const.mul analyticAt_const))).continuousMap_exp
  exact hE.mul (hQ.mul ((analyticAt_const.mul hL).continuousMap_exp))

/-- Every scalar finite kernel is genuinely entire in space, even with arbitrary complex jets. -/
theorem cepsComplexKernelGJetModel_spatial_differentiable (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b : ℂ) : Differentiable ℂ (cepsComplexKernelGJetModel p N lam z b) := by
  have hF := cepsComplexCumulantQuotientSpatialUnit_differentiable p N lam z b
  have hD (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a : ℂ) : Differentiable ℂ (dslope f a) := by
    have hd := (differentiableOn_dslope (s := Set.univ) (c := a) Filter.univ_mem).mpr hf.differentiableOn
    exact fun ξ => (hd ξ (Set.mem_univ ξ)).differentiableAt Filter.univ_mem
  have hQ : Differentiable ℂ (cepsComplexCumulantJetQuotient p N lam z b) :=
    hD _ (hD _ hF (cepsComplexCumulantRootModel p N lam z 1 N b))
      (cepsComplexCumulantRootModel p N lam z (-1) N b)
  intro ξ
  have hP : AnalyticAt ℂ (fun ξ : ℂ => cepsCanonComplexJetPolynomial p N
      (b * lam) (cepsComplexScaledDiscount lam z b) (b * ξ)) ξ := by
    simpa only [Pi.mul_apply, id_eq] using!
      (cepsCanonComplexJetPolynomial_analyticAt (p := fun _ : ℂ => p)
        (μ := fun _ : ℂ => b * lam) (q := fun _ : ℂ => cepsComplexScaledDiscount lam z b)
        (ζ := fun ξ : ℂ => b * ξ) (x := ξ) (fun _ => analyticAt_const)
        analyticAt_const analyticAt_const (analyticAt_const.mul analyticAt_id) N)
  have hE : AnalyticAt ℂ (fun ξ : ℂ => exp (-ξ * (1 + b * lam))) ξ := by fun_prop
  exact (hE.differentiableAt.mul ((hQ ξ).mul ((analyticAt_const.mul hP).cexp.differentiableAt)))

end PGM
