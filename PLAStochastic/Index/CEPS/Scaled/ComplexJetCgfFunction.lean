import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientCompact
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv

/-! # Actual finite cumulant functions and their critical derivatives -/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsComplexCgfJetModel (p : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  s ^ 2 * cepsCgfComplexJetPolynomial p N s

theorem cepsComplexCgfJetModel_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {s : E → ℂ}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) x) (hs : AnalyticAt ℂ s x) (N : ℕ) :
    AnalyticAt ℂ (fun u => cepsComplexCgfJetModel (p u) N (s u)) x :=
  (hs.pow 2).mul (cepsCgfComplexJetPolynomial_analyticAt hp hs N)

theorem cepsComplexCgfJetModel_hasDerivAt_zero (p : ℕ → ℂ) (N : ℕ) :
    HasDerivAt (cepsComplexCgfJetModel p N) 0 0 := by
  have hP : AnalyticAt ℂ (cepsCgfComplexJetPolynomial p N) 0 :=
    cepsCgfComplexJetPolynomial_analyticAt (p := fun _ : ℂ => p) (s := id) (x := (0 : ℂ))
      (fun _ => analyticAt_const) analyticAt_id N
  simpa [cepsComplexCgfJetModel, Pi.mul_apply, Pi.pow_apply, id_eq] using!
    ((hasDerivAt_id (0 : ℂ)).pow 2).mul hP.differentiableAt.hasDerivAt

theorem cepsComplexCgfJetModel_deriv_zero (p : ℕ → ℂ) (N : ℕ) :
    deriv (cepsComplexCgfJetModel p N) 0 = 0 := (cepsComplexCgfJetModel_hasDerivAt_zero p N).deriv

private theorem hasDerivAt_deriv_square_mul_zero {P : ℂ → ℂ} (hP : AnalyticAt ℂ P 0) :
    HasDerivAt (deriv (fun s : ℂ => s ^ 2 * P s)) (2 * P 0) 0 := by
  have he : deriv (fun s : ℂ => s ^ 2 * P s) =ᶠ[𝓝 0]
      (fun s : ℂ => 2 * s * P s + s ^ 2 * deriv P s) := by
    filter_upwards [hP.eventually_analyticAt] with s hs
    simpa [Pi.mul_def, Pi.pow_def, id_eq] using!
      (((hasDerivAt_id s).pow 2).mul hs.differentiableAt.hasDerivAt).deriv
  have h1 : HasDerivAt (fun s : ℂ => 2 * s * P s) (2 * P 0) 0 := by
    simpa [Pi.mul_apply, id_eq] using!
      ((hasDerivAt_id (0 : ℂ)).const_mul 2).mul hP.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℂ => s ^ 2 * deriv P s) 0 0 := by
    simpa [Pi.mul_apply, Pi.pow_apply, id_eq] using!
      ((hasDerivAt_id (0 : ℂ)).pow 2).mul hP.deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun s : ℂ => 2 * s * P s + s ^ 2 * deriv P s) (2 * P 0) 0 := by
    simpa only [Pi.add_apply, add_zero] using! h1.add h2
  exact hd.congr_of_eventuallyEq he

/-- The derivative is the actual scalar derivative, with the exact input variance. -/
theorem cepsComplexCgfJetModel_deriv_hasDerivAt_zero (p : ℕ → ℂ) (N : ℕ) :
    HasDerivAt (deriv (cepsComplexCgfJetModel p N)) (p (cepsJetCode (.inl 0))) 0 := by
  have hP : AnalyticAt ℂ (cepsCgfComplexJetPolynomial p N) 0 :=
    cepsCgfComplexJetPolynomial_analyticAt (p := fun _ : ℂ => p) (s := id) (x := (0 : ℂ))
      (fun _ => analyticAt_const) analyticAt_id N
  have h := hasDerivAt_deriv_square_mul_zero hP
  have he : 2 * cepsCgfComplexJetPolynomial p N 0 = p (cepsJetCode (.inl 0)) := by
    rw [cepsCgfComplexJetPolynomial_zero]
    ring
  rwa [he] at h

end PGM
