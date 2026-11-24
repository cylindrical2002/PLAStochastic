import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfFunction
import PLAStochastic.ForMathlib.Analysis.Complex.ScalarBlockDerivative
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseGerm

/-! # Genuine critical centers for arbitrary finite complex cumulant inputs -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual critical derivative has a two-sided inverse on genuine parameter neighborhoods. -/
theorem exists_cepsComplexCgfJetModel_derivative_inverse {p : E → ℕ → ℂ} {p₀ : E}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) p₀) (N : ℕ)
    (hV : p p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ g : E × ℂ → ℂ, AnalyticAt ℂ g (p₀, 0) ∧ g (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        deriv (cepsComplexCgfJetModel (p u.1) N) (g u) = u.2) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        g (u.1, deriv (cepsComplexCgfJetModel (p u.1) N) u.2) = u.2) := by
  let f : E × ℂ → ℂ := fun u => deriv (cepsComplexCgfJetModel (p u.1) N) u.2
  have hp' : ∀ i, AnalyticAt ℂ (fun u : E × ℂ => p u.1 i) (p₀, 0) := by
    intro i
    simpa only [Function.comp_apply] using!
      (hp i).comp (x := (p₀, (0 : ℂ))) (f := (Prod.fst : E × ℂ → E)) analyticAt_fst
  have hF : AnalyticAt ℂ (fun u : E × ℂ =>
      cepsComplexCgfJetModel (p u.1) N u.2) (p₀, 0) :=
    cepsComplexCgfJetModel_analyticAt (p := fun u : E × ℂ => p u.1)
      (s := Prod.snd) (x := (p₀, (0 : ℂ))) hp'
      analyticAt_snd N
  have hf : AnalyticAt ℂ f (p₀, 0) := hF.deriv_snd
  have hz : ∀ u : E, f (u, 0) = 0 := fun u => cepsComplexCgfJetModel_deriv_zero (p u) N
  have hd : HasFDerivAt f
      (p p₀ (cepsJetCode (.inl 0)) • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0) :=
    hasFDerivAt_scalar_block_of_zero_section hf.differentiableAt
      (Filter.Eventually.of_forall hz) (cepsComplexCgfJetModel_deriv_hasDerivAt_zero (p p₀) N)
  exact exists_analytic_parametric_inverse_germ hf hd hV (hz p₀)

/-- The critical center belongs to a genuine joint parameter neighborhood. No
probability-law realization of the finite cumulant coordinates is required. -/
theorem exists_cepsComplexCgfJetModel_critical_center {p : E → ℕ → ℂ} {p₀ : E}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) p₀) (N : ℕ)
    (hV : p p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ η : E × ℂ → ℂ, AnalyticAt ℂ η (p₀, 0) ∧ η (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        deriv (cepsComplexCgfJetModel (p u.1) N) (η u) + u.2 = 0) ∧
      (∀ᶠ u in 𝓝 p₀, η (u, 0) = 0) := by
  let f : E × ℂ → ℂ := fun u => deriv (cepsComplexCgfJetModel (p u.1) N) u.2
  have hz : ∀ u : E, f (u, 0) = 0 := fun u => cepsComplexCgfJetModel_deriv_zero (p u) N
  obtain ⟨g, hg, hg₀, hr, hl⟩ := exists_cepsComplexCgfJetModel_derivative_inverse hp N hV
  let η : E × ℂ → ℂ := fun u => g (u.1, -u.2)
  have hm : AnalyticAt ℂ (fun u : E × ℂ => (u.1, -u.2)) (p₀, 0) :=
    analyticAt_fst.prod analyticAt_snd.neg
  have hg' : AnalyticAt ℂ g (p₀, -(0 : ℂ)) := by simpa only [neg_zero] using hg
  have ht : Tendsto (fun u : E × ℂ => (u.1, -u.2))
      (𝓝 (p₀, (0 : ℂ))) (𝓝 (p₀, (0 : ℂ))) := by
    simpa only [neg_zero] using hm.continuousAt.tendsto
  have hη : AnalyticAt ℂ η (p₀, 0) := by
    simpa only [η, Function.comp_apply] using!
      hg'.comp (x := (p₀, (0 : ℂ))) (f := fun u : E × ℂ => (u.1, -u.2)) hm
  refine ⟨η, hη, by simpa [η] using hg₀, ?_, ?_⟩
  · have he : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), f (u.1, g (u.1, -u.2)) = -u.2 := by
      exact ht.eventually hr
    filter_upwards [he] with u hu
    change f (u.1, g (u.1, -u.2)) + u.2 = 0
    rw [hu]
    exact neg_add_cancel u.2
  · have hm₀ : AnalyticAt ℂ (fun u : E => (u, (0 : ℂ))) p₀ :=
      analyticAt_id.prod analyticAt_const
    have he : ∀ᶠ u in 𝓝 p₀, g (u, f (u, 0)) = 0 :=
      hm₀.continuousAt.tendsto.eventually hl
    filter_upwards [he] with u hu
    simpa [η, hz] using hu

end PGM
