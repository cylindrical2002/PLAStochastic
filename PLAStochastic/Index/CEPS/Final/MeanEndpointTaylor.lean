import PLAStochastic.Index.CEPS.Final.KernelComplexForm
import PLAStochastic.Index.CEPS.Final.AnalyticBox
import PLAStochastic.Index.CEPS.Scaled.KernelFactorsActualFrequency
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv

/-! # Reference jets and the zero-discount endpoint coefficients

The reference jet vector `J Λ` has positive variance coordinate. The scale coefficients of the
zero-discount endpoint polynomial are polynomial in finitely many jet coordinates, hence have
box Taylor representations around `J Λ`.
-/

noncomputable section
open Complex Finset
namespace PGM

theorem cepsJetLaw_cepsLambda_eq : cepsJetLaw cepsLambda = cepsJet cepsLambdaDensity :=
  cepsJetLaw_eq_cepsJet contDiff_cepsLambdaDensity.continuous.measurable cepsLambdaDensity_nonneg
    cepsLambda_eq_withDensity

theorem cepsJetLaw_cepsLambda_variance_pos :
    0 < cepsJetLaw cepsLambda (cepsJetCode (.inl 0)) := by
  rw [cepsJetLaw_cepsLambda_eq]
  exact cepsCumulantJet_variance_pos cepsRef.hW cepsRef.hθ cepsRef.hD fun _ => rfl

/-- The zero-discount endpoint polynomial on complex jet vectors. -/
def cepsComplexZeroEndpointJetPolynomial (p : ℕ → ℂ) (N : ℕ) (b : ℂ) : ℂ :=
  1 - p (cepsJetCode (.inl 0)) / 2 +
    b * (1 + 2 * ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * b ^ j *
      p (cepsJetCode (.inr (j, 1, 0)))) - b ^ 2 / 2

theorem cepsComplexZeroEndpointJetPolynomial_real (p : ℕ → ℝ) (N : ℕ) :
    cepsComplexZeroEndpointJetPolynomial (fun i => (p i : ℂ)) N = cepsZeroEndpointJetPolynomial p N :=
  rfl

theorem cepsComplexZeroEndpointJetPolynomial_analyticAt (d N : ℕ) (q : Fin d → ℂ) (b : ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ =>
      cepsComplexZeroEndpointJetPolynomial (cepsComplexJetPad d v.1) N v.2) (q, b) := by
  have hp (i : ℕ) : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsComplexJetPad d v.1 i) (q, b) :=
    (cepsComplexJetPad_analyticAt d i q).comp (x := (q, b))
      (f := (Prod.fst : (Fin d → ℂ) × ℂ → Fin d → ℂ)) analyticAt_fst
  have hb : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => v.2) (q, b) := analyticAt_snd
  have hs : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => ∑ j ∈ range (N + 1),
      (j.factorial : ℂ)⁻¹ * v.2 ^ j * cepsComplexJetPad d v.1 (cepsJetCode (.inr (j, 1, 0)))) (q, b) :=
    Finset.analyticAt_fun_sum (range (N + 1)) fun j _ =>
      (analyticAt_const.mul (hb.pow j)).mul (hp (cepsJetCode (.inr (j, 1, 0))))
  have hV : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ =>
      cepsComplexJetPad d v.1 (cepsJetCode (.inl 0)) / 2) (q, b) := (hp _).div_const
  have hb2 : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => v.2 ^ 2 / 2) (q, b) := (hb.pow 2).div_const
  unfold cepsComplexZeroEndpointJetPolynomial
  exact ((analyticAt_const.sub hV).add
    (hb.mul (analyticAt_const.add (analyticAt_const.mul hs)))).sub hb2

/-- Box Taylor representation of the zero-discount endpoint coefficients. -/
theorem cepsZeroEndpointCoeff_jetScal (k : ℕ) {d : ℕ} (hd : cepsJetDim (k + 1) ≤ d) :
    ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal (cepsJetLaw cepsLambda)
      (fun p => cepsScaleCoeff k (cepsZeroEndpointJetPolynomial p k)) T := by
  let F : (Fin d → ℂ) → ℂ := fun q =>
    cepsScaleCoeff k (fun b => cepsComplexZeroEndpointJetPolynomial (cepsComplexJetPad d q) k b)
  have hF : AnalyticAt ℂ F (fun i : Fin d => (cepsJetLaw cepsLambda i : ℂ)) := by
    have h := (cepsComplexZeroEndpointJetPolynomial_analyticAt d k
      (fun i : Fin d => (cepsJetLaw cepsLambda i : ℂ)) 0).iteratedDeriv_snd k
    exact analyticAt_const.mul (h.comp (x := (fun i : Fin d => (cepsJetLaw cepsLambda i : ℂ)))
      (f := fun q : Fin d → ℂ => (q, (0 : ℂ))) (analyticAt_id.prod analyticAt_const))
  obtain ⟨T, hT⟩ := cepsJetScal_of_analytic_finite_model (cepsJetLaw cepsLambda) hF
  refine ⟨T, hT.congr_fun ⟨1, one_pos, fun p _ => ?_⟩⟩
  have hpad : cepsComplexJetPad d (fun i : Fin d => (p i : ℂ)) =
      fun i => (cepsJetTruncate d p i : ℂ) := cepsComplexJetPad_cepsJetEmbed d p
  have hz : cepsZeroEndpointJetPolynomial (cepsJetTruncate d p) k = cepsZeroEndpointJetPolynomial p k :=
    cepsZeroEndpointJetPolynomial_congr k fun i hi => by
      simp [cepsJetTruncate, lt_of_lt_of_le hi hd]
  simp only [F, hpad, cepsComplexZeroEndpointJetPolynomial_real, hz]

end PGM
