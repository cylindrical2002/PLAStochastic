import PLAStochastic.Index.CEPS.Scaled.CanonDriftTaylor
import PLAStochastic.Index.CEPS.Jets.Consistency
import PLAStochastic.ForMathlib.Analysis.Complex.BivariateTaylor

/-! # Explicit finite mixed-jet polynomial of the canonical logarithmic factor -/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

def cepsCanonJetPolynomial (p : ℕ → ℝ) (N : ℕ) (μ q ζ : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * μ ^ j *
    ∑ m ∈ range (N + 1), (m.factorial : ℂ)⁻¹ * ζ ^ m *
      ∑ n ∈ range (N + 1), (n.factorial : ℂ)⁻¹ * q ^ n *
        (p (cepsJetCode (.inr (j, m, n))) : ℂ)

def cepsCanonDriftRectTaylor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (μ q ζ : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * μ ^ j *
    bivariateTaylorSum (cepsCanonDriftCoeff dom ρW j) N q ζ

theorem cepsCanonJetPolynomial_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) :
    cepsCanonJetPolynomial p N = cepsCanonJetPolynomial p' N := by
  funext μ q ζ
  unfold cepsCanonJetPolynomial
  apply sum_congr rfl
  intro j hj
  congr 1
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [hp (cepsJetCode (.inr (j, m, n)))
    (cepsJetCode_lt_cepsJetDim (by
      have := mem_range.mp hj; have := mem_range.mp hm; have := mem_range.mp hn
      simp only [cepsJetWeight]; omega))]

theorem cepsCanonJetPolynomial_curve_differentiable (p : ℕ → ℝ) (N : ℕ)
    {μ q ζ : ℂ → ℂ} (hμ : Differentiable ℂ μ) (hq : Differentiable ℂ q)
    (hζ : Differentiable ℂ ζ) :
    Differentiable ℂ (fun b => cepsCanonJetPolynomial p N (μ b) (q b) (ζ b)) := by
  unfold cepsCanonJetPolynomial
  fun_prop

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsCanonDriftRectTaylor_eq_jetPolynomial :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m →
        cepsCanonDriftRectTaylor dom ρW N = cepsCanonJetPolynomial (cepsJet f) N := by
  obtain ⟨r, hr, he⟩ := cepsJet_contour_eq dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hclose N hN
  funext μ q ζ
  unfold cepsCanonDriftRectTaylor cepsCanonJetPolynomial
  apply sum_congr rfl
  intro j hj
  congr 1
  unfold bivariateTaylorSum
  apply sum_congr rfl
  intro l _
  congr 1
  unfold complexTaylorSum
  simp only [sub_zero]
  apply sum_congr rfl
  intro k _
  rw [show iteratedDeriv k (fun w : ℂ => iteratedDeriv l
      (cepsCanonDriftCoeff dom ρW j w) 0) 0 =
      (cepsJet f (cepsJetCode (.inr (j, l, k))) : ℂ) from
    he hW hfW hneg hη hf hclose j l k (by have := mem_range.mp hj; omega)]

end PGM
