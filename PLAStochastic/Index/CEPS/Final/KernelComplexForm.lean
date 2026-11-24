import PLAStochastic.Index.CEPS.Final.KernelDefs
import PLAStochastic.Index.CEPS.Scaled.ComplexJetPair
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDependence

/-! # The concrete kernel coefficients through complex finite-jet models

`cepsKernelGk j p y` and `cepsKernelCs k p` only read finitely many jet coordinates. Once `d`
covers them, both are written through the complex finite-jet models evaluated at the zero-padded
first `d` coordinates of `p`: scale coefficients of the marked endpoint and marked discount, and
drift integrals of scale coefficients of the complete subtracted pair.
-/

noncomputable section
open Complex PowerSeries Finset MeasureTheory
namespace PGM

/-- The first `d` coordinates of a real jet vector, as a complex vector. -/
def cepsJetEmbed (d : ℕ) (p : ℕ → ℝ) : Fin d → ℂ := fun i => (p i : ℂ)

/-- The `n`-th scale coefficient `(n!)⁻¹ ∂_bⁿ f(0)`. -/
def cepsScaleCoeff (n : ℕ) (f : ℂ → ℂ) : ℂ := (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

/-- Scale coefficient of the complex marked endpoint. -/
def cepsKernelEndpointCoeffC (d j : ℕ) (q : Fin d → ℂ) (z : ℂ) : ℂ :=
  cepsScaleCoeff j (fun b => cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d q) j z b)

/-- Scale coefficient of the complex marked discount. -/
def cepsKernelDiscountCoeffC (d j a : ℕ) (q : Fin d → ℂ) (z : ℂ) : ℂ :=
  cepsScaleCoeff a (fun b => -cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d q) j 0 z b (b * z))

/-- Scale coefficient of the complex complete subtracted pair at drift `lam`. -/
def cepsKernelPairCoeffC (d N n : ℕ) (q : Fin d → ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  cepsScaleCoeff n (fun b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b)

/-- The real vector truncated to its first `d` coordinates. -/
def cepsJetTruncate (d : ℕ) (p : ℕ → ℝ) : ℕ → ℝ := fun i => if i < d then p i else 0

theorem cepsComplexJetPad_cepsJetEmbed (d : ℕ) (p : ℕ → ℝ) :
    cepsComplexJetPad d (cepsJetEmbed d p) = fun i => (cepsJetTruncate d p i : ℂ) := by
  funext i
  by_cases hi : i < d
  · simp [cepsComplexJetPad, cepsJetEmbed, cepsJetTruncate, hi]
  · simp [cepsComplexJetPad, cepsJetTruncate, hi]

theorem coeff_complexTaylorSeries_zero (n : ℕ) (f : ℂ → ℂ) :
    coeff n (complexTaylorSeries f 0) = cepsScaleCoeff n f := by
  simp [complexTaylorSeries, cepsScaleCoeff]

theorem cepsKernelGk_eq_complex {d j : ℕ} (hd : cepsJetDim (4 * (j + 1)) ≤ d)
    (p : ℕ → ℝ) (y : ℝ) :
    cepsKernelGk j p y = cepsKernelEndpointCoeffC d j (cepsJetEmbed d p) (I * y) -
      ∑ x ∈ antidiagonal j, cepsKernelDiscountCoeffC d j x.1 (cepsJetEmbed d p) (I * y) *
        ∫ lam, cepsKernelPairCoeffC d (j + 1) x.2 (cepsJetEmbed d p) lam (I * y) := by
  set p' := cepsJetTruncate d p with hp'
  have hpp : ∀ i, i < cepsJetDim (4 * (j + 1)) → p i = p' i := by
    intro i hi
    simp [hp', cepsJetTruncate, lt_of_lt_of_le hi hd]
  have hpad : cepsComplexJetPad d (cepsJetEmbed d p) = fun i => (p' i : ℂ) :=
    cepsComplexJetPad_cepsJetEmbed d p
  have hE : (fun b => cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d (cepsJetEmbed d p))
      j (I * y) b) = cepsKernelMarkedEndpointJetModel p' j (I * y) := by
    funext b
    rw [hpad]
    exact (cepsComplexKernelHalfFactors_real p' j 1 (I * y) b).2.2
  have hD : (fun b => -cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d (cepsJetEmbed d p))
      j 0 (I * y) b (b * (I * y))) = cepsKernelMarkedDiscountJetModel p' j (I * y) := by
    funext b
    rw [hpad, cepsComplexCumulantQuotientSpatialUnit_real]
    rfl
  have hP (n : ℕ) (lam : ℝ) : (fun b => cepsComplexKernelSubtractedPairJetModel
      (cepsComplexJetPad d (cepsJetEmbed d p)) (j + 1) lam (I * y) b) =
      cepsKernelSubtractedPairJetModel p' (j + 1) lam (I * y) := by
    funext b
    rw [hpad]
    exact (cepsComplexKernelPairModels_real p' (j + 1) lam (I * y) b).2.2
  have hI (n : ℕ) : cepsKernelPairIntegralCoeffJetModel p' (j + 1) n (I * y) =
      ∫ lam, cepsKernelPairCoeffC d (j + 1) n (cepsJetEmbed d p) lam (I * y) := by
    unfold cepsKernelPairIntegralCoeffJetModel
    refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
    simp only [cepsKernelPairCoeffJetModel, cepsKernelPairCoeffC, coeff_complexTaylorSeries_zero, hP n lam]
  have hG : cepsKernelGk j p y = cepsKernelNormalCoeffJetModel p' j (I * y) :=
    (cepsKernelNormalCoefficients_congr j hpp (I * y)).1
  rw [hG, cepsKernelNormalCoeffJetModel, cepsKernelNormalSeriesJetModel, map_sub, coeff_mul,
    coeff_complexTaylorSeries_zero, cepsKernelEndpointCoeffC, hE]
  refine congrArg (fun t => cepsScaleCoeff j (cepsKernelMarkedEndpointJetModel p' j (I * y)) - t) ?_
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_complexTaylorSeries_zero, coeff_mk, cepsKernelDiscountCoeffC, hD, hI]

theorem cepsKernelCs_eq_complex {d k : ℕ} (hd : cepsJetDim (4 * (k + 1)) ≤ d) (p : ℕ → ℝ) :
    cepsKernelCs k p = (cepsScaleCoeff k (cepsZeroEndpointJetPolynomial p k) +
      ∫ lam, cepsKernelPairCoeffC d (k + 1) k (cepsJetEmbed d p) lam 0).re := by
  set p' := cepsJetTruncate d p with hp'
  have hpp : ∀ i, i < cepsJetDim (4 * (k + 1)) → p i = p' i := by
    intro i hi
    simp [hp', cepsJetTruncate, lt_of_lt_of_le hi hd]
  have hpad : cepsComplexJetPad d (cepsJetEmbed d p) = fun i => (p' i : ℂ) :=
    cepsComplexJetPad_cepsJetEmbed d p
  have hP (lam : ℝ) : (fun b => cepsComplexKernelSubtractedPairJetModel
      (cepsComplexJetPad d (cepsJetEmbed d p)) (k + 1) lam 0 b) =
      cepsKernelSubtractedPairJetModel p' (k + 1) lam 0 := by
    funext b
    rw [hpad]
    exact (cepsComplexKernelPairModels_real p' (k + 1) lam 0 b).2.2
  have hI : cepsKernelPairIntegralCoeffJetModel p' (k + 1) k 0 =
      ∫ lam, cepsKernelPairCoeffC d (k + 1) k (cepsJetEmbed d p) lam 0 := by
    unfold cepsKernelPairIntegralCoeffJetModel
    refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
    simp only [cepsKernelPairCoeffJetModel, cepsKernelPairCoeffC, coeff_complexTaylorSeries_zero, hP lam]
  have hz : cepsZeroEndpointJetPolynomial p' k = cepsZeroEndpointJetPolynomial p k :=
    cepsZeroEndpointJetPolynomial_congr k fun i hi =>
      (hpp i (hi.trans_le (cepsJetDim_monotone (by omega)))).symm
  have hC : cepsKernelCs k p = (cepsKernelMeanCoeffJetModel p' k).re := by
    unfold cepsKernelCs
    rw [(cepsKernelNormalCoefficients_congr k hpp 0).2]
  rw [hC, cepsKernelMeanCoeffJetModel, cepsKernelMeanSeriesJetModel, map_add,
    coeff_complexTaylorSeries_zero, coeff_mk, hz, hI]

end PGM
