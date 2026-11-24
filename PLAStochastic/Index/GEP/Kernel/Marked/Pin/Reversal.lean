import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullDensity
import PLAStochastic.Index.GEP.Kernel.Marked.CorrelationSplit

/-! # Reversal of the actual marked density at every pair of lengths -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kernelMarkedFullDens_symm {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β x : ℝ) (l r : ℕ) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a x l r y z =
      kernelMarkedFullDens J ν f (-β) (-a) x r l z y := by
  cases l with
  | zero =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [kernelMarkedFullDens]
      rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha r]
      rw [show y- -β+-a*x = y+β-a*x by ring]
      ring
  | succ l =>
    cases r with
    | zero =>
      simp only [kernelMarkedFullDens]
      rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha l]
      rw [show z+ -β- -a*x = z-β+a*x by ring]
      ring
    | succ r =>
      apply Complex.ofReal_injective
      simp only [kernelMarkedFullDens]
      rw [kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν ha,
        kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν (neg_ne_zero.mpr ha)]
      simp only [neg_neg]
      rw [kernelCorrelation_flip]
      congr 1
      ring

end
end PGM
