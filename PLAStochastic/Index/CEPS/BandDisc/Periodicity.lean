import PLAStochastic.Index.CEPS.BandDisc.Series

/-! # Exact periodicity of the actual discount series

This records the domain issue in the original X7 handoff: a global linear lower
bound in `|q|` is incompatible with the discrete-time discount periodicity.
The class-uniform `w⁻²` bound on a fixed disc is a separate statement.
-/

namespace PGM
noncomputable section

lemma cepsBandDisc_exp_shift {T : ℂ} (hT : Complex.exp (-T) = 1) (q : ℂ) (n : ℕ) :
    Complex.exp (-(q + T) * n) = Complex.exp (-q * n) := by
  rw [show -(q + T) * (n : ℂ) = -q * n + -T * n by ring, Complex.exp_add,
    mul_comm (-T), Complex.exp_nat_mul, hT, one_pow, mul_one]

/-- Any integer-time exponential series is invariant under a discount period. -/
theorem cepsDiscJet_periodic {T : ℂ} (hT : Complex.exp (-T) = 1)
    (c : ℕ → ℂ) (s k : ℕ) (q : ℂ) :
    cepsDiscJet c s k (q + T) = cepsDiscJet c s k q := by
  unfold cepsDiscJet
  simp_rw [cepsBandDisc_exp_shift hT]

/-- The actual marked entrance shares this exact periodicity, independently of its mark. -/
theorem cepsStripEntrance_discount_periodic {T : ℂ} (hT : Complex.exp (-T) = 1)
    (ν : MeasureTheory.ProbabilityMeasure ℝ) (t : ℂ) (μ l : ℝ) (q : ℂ) :
    cepsStripEntrance ν t μ (q + T) l = cepsStripEntrance ν t μ q l := by
  unfold cepsStripEntrance
  simp_rw [cepsBandDisc_exp_shift hT]

end
end PGM
