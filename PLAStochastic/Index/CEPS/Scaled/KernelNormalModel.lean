import PLAStochastic.Index.CEPS.Scaled.KernelDiscountJets
import PLAStochastic.Index.CEPS.Scaled.KernelIntegralJets
import PLAStochastic.Index.CEPS.Scaled.KernelEndpointJets
import PLAStochastic.Index.CEPS.Scaled.ZeroEndpointJets

/-! # Explicit finite mixed-jet normal-transform and mean coefficient models -/

noncomputable section
open Complex PowerSeries
namespace PGM

def cepsKernelNormalSeriesJetModel (p : ℕ → ℝ) (N : ℕ) (z : ℂ) : PowerSeries ℂ :=
  complexTaylorSeries (cepsKernelMarkedEndpointJetModel p N z) 0 -
    complexTaylorSeries (cepsKernelMarkedDiscountJetModel p N z) 0 *
      PowerSeries.mk (fun j => cepsKernelPairIntegralCoeffJetModel p (N + 1) j z)

def cepsKernelMeanSeriesJetModel (p : ℕ → ℝ) (N : ℕ) : PowerSeries ℂ :=
  complexTaylorSeries (cepsZeroEndpointJetPolynomial p N) 0 +
    PowerSeries.mk (fun j => cepsKernelPairIntegralCoeffJetModel p (N + 1) j 0)

def cepsKernelNormalCoeffJetModel (p : ℕ → ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  coeff j (cepsKernelNormalSeriesJetModel p j z)

def cepsKernelMeanCoeffJetModel (p : ℕ → ℝ) (j : ℕ) : ℂ :=
  coeff j (cepsKernelMeanSeriesJetModel p j)

theorem cepsKernelNormalSeriesModels_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * (N + 1)) → p i = p' i) (z : ℂ) :
    cepsKernelNormalSeriesJetModel p N z = cepsKernelNormalSeriesJetModel p' N z ∧
    cepsKernelMeanSeriesJetModel p N = cepsKernelMeanSeriesJetModel p' N := by
  have hp4N : ∀ i, i < cepsJetDim (4 * N) → p i = p' i :=
    fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega)))
  have hpN : ∀ i, i < cepsJetDim N → p i = p' i :=
    fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega)))
  have hpN1 : ∀ i, i < cepsJetDim (N + 1) → p i = p' i :=
    fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega)))
  have hE := (cepsKernelHalfFactors_congr N hp4N 1 z).2.2
  have hD := cepsKernelMarkedDiscountJetModel_congr N hpN z
  have hZ := cepsZeroEndpointJetPolynomial_congr N hpN1
  have hI (z : ℂ) : PowerSeries.mk (fun j => cepsKernelPairIntegralCoeffJetModel p (N + 1) j z) =
      PowerSeries.mk (fun j => cepsKernelPairIntegralCoeffJetModel p' (N + 1) j z) := by
    exact congrArg (fun a : ℕ → ℂ => PowerSeries.mk a)
      (funext fun j => (cepsKernelPairCoefficients_congr (N + 1) hp j z).2)
  exact ⟨by simp only [cepsKernelNormalSeriesJetModel, hE, hD, hI],
    by simp only [cepsKernelMeanSeriesJetModel, hZ, hI]⟩

theorem cepsKernelNormalCoefficients_congr {p p' : ℕ → ℝ} (j : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * (j + 1)) → p i = p' i) (z : ℂ) :
    cepsKernelNormalCoeffJetModel p j z = cepsKernelNormalCoeffJetModel p' j z ∧
    cepsKernelMeanCoeffJetModel p j = cepsKernelMeanCoeffJetModel p' j := by
  exact ⟨congrArg (coeff j) (cepsKernelNormalSeriesModels_congr j hp z).1,
    congrArg (coeff j) (cepsKernelNormalSeriesModels_congr j hp z).2⟩

end PGM
