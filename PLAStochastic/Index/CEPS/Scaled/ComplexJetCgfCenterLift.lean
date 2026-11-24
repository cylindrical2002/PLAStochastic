import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfCenter
import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfUnit
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseLift
import PLAStochastic.ForMathlib.Analysis.Complex.CompactLiftDerivative

/-! # Actual finite cumulant critical inverses in compact continuous-function spaces -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The exact critical derivative is inverted for nonconstant function arguments.
The functional and scalar inverses agree throughout one genuine neighborhood. -/
theorem exists_cepsComplexCgfJetModel_derivative_inverse_lift (d N : ℕ)
    (p₀ : Fin d → ℂ) (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ g : (Fin d → ℂ) × ℂ → ℂ, ∃ G : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ g (p₀, 0) ∧ g (p₀, 0) = 0 ∧
      AnalyticAt ℂ G (p₀, 0) ∧ G (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (g u) = u.2) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k,
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (G u k) = u.2 k) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, G u k = g (u.1, u.2 k)) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        g (u.1, deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) u.2) = u.2) := by
  let E := Fin d → ℂ
  let p : E → ℕ → ℂ := cepsComplexJetPad d
  have hp : ∀ u i, AnalyticAt ℂ (fun v => p v i) u :=
    fun u i => cepsComplexJetPad_analyticAt d i u
  let f : E × ℂ → ℂ := fun u => deriv (cepsComplexCgfJetModel (p u.1) N) u.2
  have hF : AnalyticAt ℂ (fun u : E × ℂ => cepsComplexCgfJetModel (p u.1) N u.2) (p₀, 0) := by
    apply cepsComplexCgfJetModel_analyticAt (p := fun u : E × ℂ => p u.1)
      (s := Prod.snd) (x := (p₀, (0 : ℂ))) _ analyticAt_snd N
    intro i
    simpa only [Function.comp_apply] using!
      (hp p₀ i).comp (x := (p₀, (0 : ℂ))) (f := (Prod.fst : E × ℂ → E)) analyticAt_fst
  have hf : AnalyticAt ℂ f (p₀, 0) := hF.deriv_snd
  have hz : ∀ u : E, f (u, 0) = 0 := fun u => cepsComplexCgfJetModel_deriv_zero (p u) N
  have hd : HasFDerivAt f
      (p p₀ (cepsJetCode (.inl 0)) • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0) :=
    hasFDerivAt_scalar_block_of_zero_section hf.differentiableAt (Filter.Eventually.of_forall hz)
      (cepsComplexCgfJetModel_deriv_hasDerivAt_zero (p p₀) N)
  let H₀ : E × C(K, ℂ) → C(K, ℂ) := fun u => cepsContinuousCgfJetModel (p u.1) N u.2
  let H := compactSpatialDeriv H₀
  have hH : AnalyticAt ℂ H (p₀, 0) :=
    compactSpatialDeriv_analyticAt (cepsContinuousCgfJetModel_joint_analyticAt (hp p₀) N 0)
  have he : ∀ u : E × C(K, ℂ), ∀ k, H u k = f (u.1, u.2 k) := by
    intro u k
    exact compactSpatialDeriv_apply (H := H₀) (f := fun v : E => cepsComplexCgfJetModel (p v) N)
      (cepsContinuousCgfJetModel_joint_analyticAt (hp u.1) N u.2)
      (fun S q => cepsContinuousCgfJetModel_apply (p u.1) N S q)
      (fun s => by
        simpa only [id_eq] using!
          (cepsComplexCgfJetModel_analyticAt (p := fun _ : ℂ => p u.1) (s := id) (x := s)
            (fun _ => analyticAt_const) analyticAt_id N).differentiableAt) k
  have hHD := hasFDerivAt_compact_lift_of_scalar_block hH hd (Filter.Eventually.of_forall he)
  have hH₀ : H (p₀, 0) = 0 := by
    apply ContinuousMap.ext
    intro k
    simpa only [ContinuousMap.zero_apply] using (he (p₀, 0) k).trans (hz p₀)
  obtain ⟨g, hg, hg₀, hr, hl⟩ := exists_cepsComplexCgfJetModel_derivative_inverse (hp p₀) N hV
  obtain ⟨G, hG, hG₀, hGr, hGe⟩ := exists_analytic_parametric_inverse_lift_germ
    hH hHD hV hH₀ (Filter.Eventually.of_forall he) hl
  refine ⟨g, G, hg, hg₀, hG, hG₀, hr, ?_, hGe, hl⟩
  filter_upwards [hGr] with u hu
  intro k
  have hk := congrArg (fun S : C(K, ℂ) => S k) hu
  change H (u.1, G u) k = u.2 k at hk
  rwa [he] at hk

end PGM
