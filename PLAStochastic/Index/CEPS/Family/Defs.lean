import PLAStochastic.Index.CEPS.Reference.Density
import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion

/-!
# The one-layer family interface

A family of laws `ν ε` expands in the exponentially weighted `W^{m,1}` size if its
densities differ from the reference density of `Λ` by a finite polynomial in `ε⁻¹`
up to a remainder of the next order. The one-layer interface asks the actual layer
map to send such families to such families, with output coefficients given by one
triangular map, and asks the mean segment length to expand as well.

Regularity of the input (mean one, positive support, exponential density envelope)
is a separate hypothesis. The actual orbit of `Λ` supplies it by orbit closure, so the
output conclusion need not repeat it.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The exponentially weighted `W^{m,1}` size `∑_{r ≤ m} ∫ e^{η|x|} |f^{(r)}(x)| dx`. -/
def cepsSobolev (m : ℕ) (η : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), ∫ x, Real.exp (η * |x|) * |iteratedDeriv r f x|

/-- `C^m` functions whose derivatives up to order `m` are integrable against `e^{η|x|}`. -/
structure CepsSobolevClass (m : ℕ) (η : ℝ) (f : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ m f
  integrable : ∀ r : ℕ, r ≤ m →
    Integrable (fun x => Real.exp (η * |x|) * iteratedDeriv r f x)

/-- A family of laws expands to order `P` in the weighted `W^{m,1}` size, with density
coefficients `g 1, …, g P`. The reference field restricts the weight to the envelope
of `Λ`; beyond it the remainder is not integrable and its Bochner size would vanish by
convention, making the remainder estimate void. -/
structure CepsFamilyExpansion (ν : ℝ → ProbabilityMeasure ℝ) (m : ℕ) (η : ℝ) (P : ℕ)
    (g : ℕ → ℝ → ℝ) : Prop where
  reference : CepsSobolevClass m η cepsLambdaDensity
  coeff : ∀ n ∈ Finset.Icc 1 P, CepsSobolevClass m η (g n)
  density : ∃ f : ℝ → ℝ → ℝ,
    (∀ᶠ eps in atTop, (∀ x, 0 ≤ f eps x) ∧ CepsSobolevClass m η (f eps) ∧
      (ν eps : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f eps x))) ∧
    IsInverseOrder (fun eps => cepsSobolev m η (fun x =>
      f eps x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x)) (P + 1)

/-- Eventual membership in one fixed regular class: mean one, support in `(0, ∞)`,
an exponential density envelope and a variance window. -/
def CepsEventuallyRegular (ν : ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∃ D θ vlo vhi : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
    ∀ᶠ eps in atTop, RegLaw D θ vlo vhi (ν eps)

/-- The coefficient of order `n` depends only on the input coefficients of orders `1, …, n - 1`. -/
def CepsTriangular (G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ (g g' : ℕ → ℝ → ℝ) (n : ℕ), (∀ i, 1 ≤ i → i < n → g i = g' i) → G g n = G g' n

/-- One layer with coefficient map `G`: every target order and derivative budget has an
input requirement. Any positive input weight gives some positive output weight. -/
def CepsOneLayerStep (G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ P' m' : ℕ, ∃ P m : ℕ, ∀ (ν : ℝ → ProbabilityMeasure ℝ) (g : ℕ → ℝ → ℝ) (η : ℝ),
    CepsEventuallyRegular ν → 0 < η → CepsFamilyExpansion ν m η P g →
      ∃ η' : ℝ, 0 < η' ∧
        CepsFamilyExpansion (fun eps => lawPhi eps (ν eps)) m' η' P' (G g) ∧
        ∃ c : ℕ → ℝ, HasInverseExpansionAtOrder (fun eps => lawC eps (ν eps) / eps ^ 2) c P'

/-- The one-layer family interface (OLF) of the P-CEPS assembly. -/
def CepsOneLayerFamily : Prop :=
  ∃ G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ, CepsTriangular G ∧ CepsOneLayerStep G

theorem cepsSobolev_nonneg (m : ℕ) (η : ℝ) (f : ℝ → ℝ) : 0 ≤ cepsSobolev m η f :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)

/-- The order-zero term is the exponentially weighted `L¹` size. -/
theorem integral_expWeighted_abs_le_cepsSobolev (m : ℕ) (η : ℝ) (f : ℝ → ℝ) :
    ∫ x, Real.exp (η * |x|) * |f x| ≤ cepsSobolev m η f := by
  have h := Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun r => ∫ x, Real.exp (η * |x|) * |iteratedDeriv r f x|)
    (fun _ _ => integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
    (Finset.mem_range.mpr (Nat.succ_pos m))
  unfold cepsSobolev
  simpa only [iteratedDeriv_zero] using h

theorem CepsSobolevClass.continuous_iteratedDeriv {m : ℕ} {η : ℝ} {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) {r : ℕ} (hr : r ≤ m) : Continuous (iteratedDeriv r f) :=
  hf.contDiff.continuous_iteratedDeriv r (by exact_mod_cast hr)

theorem CepsSobolevClass.continuous {m : ℕ} {η : ℝ} {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) : Continuous f := by
  simpa only [iteratedDeriv_zero] using hf.continuous_iteratedDeriv (Nat.zero_le m)

theorem CepsSobolevClass.integrable_zero {m : ℕ} {η : ℝ} {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) : Integrable (fun x => Real.exp (η * |x|) * f x) := by
  simpa only [iteratedDeriv_zero] using hf.integrable 0 (Nat.zero_le m)

theorem cepsSobolevClass_zero (m : ℕ) (η : ℝ) : CepsSobolevClass m η (fun _ => 0) where
  contDiff := contDiff_const
  integrable r _ := by
    simp only [iteratedDeriv_fun_const_zero, mul_zero]
    exact integrable_zero _ _ _

/-- Every derivative budget admits a positive weight inside the envelope of `Λ`. -/
theorem exists_cepsSobolevClass_cepsLambdaDensity (m : ℕ) :
    ∃ η : ℝ, 0 < η ∧ CepsSobolevClass m η cepsLambdaDensity := by
  obtain ⟨η, hη, hi⟩ := cepsLambdaDensity_finite_jet_integrability m
  exact ⟨η, hη, contDiff_cepsLambdaDensity.of_le (by exact_mod_cast le_top), hi⟩

end

end PGM
