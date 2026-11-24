import PLAStochastic.Index.CEPS.Jets.Reference
import PLAStochastic.Index.CEPS.Jets.Cumulant

/-!
# X8: the jet vector and the JF coefficients

* `cepsJetAt f i`: the cumulant `κ_{k+2}(f)` for `i = inl k`; the real part of the contour jet
  `cepsContourJetC cepsJetLine (cepsJetTransform f) j m n` for `i = inr (j, m, n)`.
* `cepsJet f n = cepsJetAt f (Denumerable.ofNat CepsJetIdx n)`: the jet vector; the jet `i` sits
  at position `cepsJetCode i`, and all jets of weight `≤ k` sit below `cepsJetDim k`.
* `cepsJetLaw ν = cepsJet (density of ν)` with the Radon–Nikodym density.
* `cepsJetCoeff i n g`: the `n`-th JF coefficient. For cumulants it is the `n`-th coefficient of
  the cumulant series of the moment series (`cepsCumSeries`); for contour jets it is
  `Re (Φ⁽ⁿ⁾(0)/n!)` with `Φ(h)` the contour jet of the transform `M^Λ + ∑_{p ≤ n} h^p M^{g_p}`
  (complex `h`). Both read only `g 1, …, g n` (`cepsJetCoeff_triangular`).
-/

noncomputable section

open MeasureTheory Complex

namespace PGM

/-- The jet `i` of a (signed) density. -/
def cepsJetAt (f : ℝ → ℝ) : CepsJetIdx → ℝ
  | .inl k => cepsCumulant f (k + 2)
  | .inr (j, m, n) => (cepsContourJetC cepsJetLine (cepsJetTransform f) j m n).re

/-- The jet vector of a (signed) density. -/
def cepsJet (f : ℝ → ℝ) (i : ℕ) : ℝ := cepsJetAt f (Denumerable.ofNat CepsJetIdx i)

theorem cepsJet_code (f : ℝ → ℝ) (i : CepsJetIdx) : cepsJet f (cepsJetCode i) = cepsJetAt f i := by
  rw [cepsJet, ofNat_cepsJetCode]

/-- The Radon–Nikodym density of a law. -/
def cepsLawDensity (ν : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ((ν : Measure ℝ).rnDeriv volume x).toReal

/-- The jet vector of a law (`CepsJetData.jet`). -/
def cepsJetLaw (ν : ProbabilityMeasure ℝ) (i : ℕ) : ℝ := cepsJet (cepsLawDensity ν) i

/-- The perturbed transform `M^Λ(s) + ∑_{p=1}^{n} h^p M^{g_p}(s)`. -/
def cepsJetPerturbed (g : ℕ → ℝ → ℝ) (n : ℕ) (h s : ℂ) : ℂ :=
  cepsJetTransform cepsLambdaDensity s + ∑ p ∈ Finset.Icc 1 n, h ^ p * cepsJetTransform (g p) s

/-- The `n`-th JF coefficient of the contour jet `(j, m, l)`. -/
def cepsContourCoeff (j m l : ℕ) (g : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  (iteratedDeriv n (fun h : ℂ => cepsContourJetC cepsJetLine (cepsJetPerturbed g n h) j m l) 0 /
    (n.factorial : ℂ)).re

/-- The `n`-th JF coefficient of the jet `i`. -/
def cepsJetCoeffAt : CepsJetIdx → ℕ → (ℕ → ℝ → ℝ) → ℝ
  | .inl k, n, g => PowerSeries.coeff n (cepsCumSeries g (k + 2))
  | .inr (j, m, l), n, g => cepsContourCoeff j m l g n

/-- The JF coefficients (`CepsJetData.jetCoeff`). -/
def cepsJetCoeff (i n : ℕ) (g : ℕ → ℝ → ℝ) : ℝ :=
  cepsJetCoeffAt (Denumerable.ofNat CepsJetIdx i) n g

theorem cepsJetPerturbed_congr {g g' : ℕ → ℝ → ℝ} {n : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ n → g j = g' j) : cepsJetPerturbed g n = cepsJetPerturbed g' n := by
  funext x s
  unfold cepsJetPerturbed
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_Icc] at hp
  rw [h p hp.1 hp.2]

/-- **JF, triangularity.** The `n`-th coefficient reads only `g 1, …, g n`. -/
theorem cepsJetCoeff_triangular (i n : ℕ) (g g' : ℕ → ℝ → ℝ)
    (h : ∀ j, 1 ≤ j → j ≤ n → g j = g' j) : cepsJetCoeff i n g = cepsJetCoeff i n g' := by
  unfold cepsJetCoeff
  rcases Denumerable.ofNat CepsJetIdx i with k | ⟨j, m, l⟩
  · exact coeff_cepsCumSeries_congr h (k + 2)
  · simp only [cepsJetCoeffAt, cepsContourCoeff, cepsJetPerturbed_congr h]

end PGM
