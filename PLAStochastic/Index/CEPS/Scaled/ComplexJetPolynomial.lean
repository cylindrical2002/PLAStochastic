import PLAStochastic.Index.CEPS.Scaled.CanonJetCurves
import PLAStochastic.Index.CEPS.Scaled.CgfUnitJets

/-! # Complexification of the finite cumulant and canonical mixed-jet polynomials -/

noncomputable section
open Complex Finset
namespace PGM

/-- Complex jet coordinates used for Cauchy estimates in a finite input box. -/
def cepsCgfComplexJetPolynomial (p : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), ((j + 2).factorial : ℂ)⁻¹ * s ^ j * p (cepsJetCode (.inl j))

/-- The complex canonical mixed-jet polynomial uses exactly the original rectangular support. -/
def cepsCanonComplexJetPolynomial (p : ℕ → ℂ) (N : ℕ) (μ q ζ : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * μ ^ j *
    ∑ m ∈ range (N + 1), (m.factorial : ℂ)⁻¹ * ζ ^ m *
      ∑ n ∈ range (N + 1), (n.factorial : ℂ)⁻¹ * q ^ n * p (cepsJetCode (.inr (j, m, n)))

theorem cepsCgfComplexJetPolynomial_real (p : ℕ → ℝ) (N : ℕ) :
    cepsCgfComplexJetPolynomial (fun i => (p i : ℂ)) N = cepsCgfJetPolynomial p N := rfl

theorem cepsCanonComplexJetPolynomial_real (p : ℕ → ℝ) (N : ℕ) :
    cepsCanonComplexJetPolynomial (fun i => (p i : ℂ)) N = cepsCanonJetPolynomial p N := rfl

/-- Joint analyticity is stated on arbitrary analytic parameter curves, so it also applies to
all finite-dimensional complex coordinate spaces without a realization by a density. -/
theorem cepsCgfComplexJetPolynomial_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {s : E → ℂ}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hs : AnalyticAt ℂ s x) (N : ℕ) :
    AnalyticAt ℂ (fun x => cepsCgfComplexJetPolynomial (p x) N (s x)) x := by
  unfold cepsCgfComplexJetPolynomial
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((analyticAt_const.mul (hs.pow j)).mul (hp _))

theorem cepsCanonComplexJetPolynomial_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {μ q ζ : E → ℂ}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hμ : AnalyticAt ℂ μ x)
    (hq : AnalyticAt ℂ q x) (hζ : AnalyticAt ℂ ζ x) (N : ℕ) :
    AnalyticAt ℂ (fun x => cepsCanonComplexJetPolynomial (p x) N (μ x) (q x) (ζ x)) x := by
  unfold cepsCanonComplexJetPolynomial
  apply Finset.analyticAt_fun_sum
  intro j _
  apply (analyticAt_const.mul (hμ.pow j)).mul
  apply Finset.analyticAt_fun_sum
  intro m _
  apply (analyticAt_const.mul (hζ.pow m)).mul
  apply Finset.analyticAt_fun_sum
  intro n _
  exact (analyticAt_const.mul (hq.pow n)).mul (hp _)

end PGM
