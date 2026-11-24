import PLAStochastic.Swing.Ladder.Renewal.ExpansionInterface

/-! # Blanchet--Glynn's scaled renewal-remainder interface

This file records the positive-half-line part of Blanchet--Glynn Theorem 1(i)
with the scaling used in the paper.  The predicate below is deliberately an
interface: its Fourier/renewal proof is the separate BG analytic task.  The
bridge theorem is unconditional and only converts the source normalization to
the older project-wide renewal-expansion predicate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The positive-half-line remainder in Blanchet--Glynn's normalization:
`μ² |U(t) - (t/μ + E[H²]/(2μ²))| ≤ K exp(-c t)`. -/
def BGUniformRenewalRemainder
    (L : ℝ → Measure ℝ) (S : Set ℝ) (K c : ℝ) : Prop :=
  0 < c ∧ 0 ≤ K ∧
    ∀ a ∈ S, ∀ u : ℝ, 0 ≤ u →
      (ladderMean (L a)) ^ 2 *
          |ladderRenewalFunction (L a) u -
            (u / ladderMean (L a) + ladderRenewalConstant (L a))| ≤
        K * Real.exp (-c * u)

theorem uniformLadderRenewalExpansion_of_bgUniformRenewalRemainder
    {L : ℝ → Measure ℝ} {S : Set ℝ} {K c μmin : ℝ}
    (hμmin : 0 < μmin)
    (hμ : ∀ a ∈ S, μmin ≤ ladderMean (L a))
    (h : BGUniformRenewalRemainder L S K c) :
    UniformLadderRenewalExpansion L S (K / μmin ^ 2) c := by
  obtain ⟨hc, hK, hrem⟩ := h
  refine ⟨hc, ?_, ?_⟩
  · positivity
  · intro a ha u hu
    have hμa : μmin ≤ ladderMean (L a) := hμ a ha
    have hμa0 : 0 ≤ ladderMean (L a) := le_trans (le_of_lt hμmin) hμa
    have hsq : μmin ^ 2 ≤ (ladderMean (L a)) ^ 2 := by
      nlinarith
    have hrem' := hrem a ha u hu
    have hden : 0 < (ladderMean (L a)) ^ 2 := by
      have : 0 < ladderMean (L a) := lt_of_lt_of_le hμmin hμa
      positivity
    have hscale :
        |ladderRenewalFunction (L a) u -
            (u / ladderMean (L a) + ladderRenewalConstant (L a))| ≤
          (K * Real.exp (-c * u)) / (ladderMean (L a)) ^ 2 := by
      exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hrem')
    have hdiv :
        (K * Real.exp (-c * u)) / (ladderMean (L a)) ^ 2 ≤
          K * Real.exp (-c * u) / μmin ^ 2 := by
      have hnum : 0 ≤ K * Real.exp (-c * u) := by positivity
      exact div_le_div_of_nonneg_left hnum (by positivity) hsq
    calc
      _ ≤ (K * Real.exp (-c * u)) / (ladderMean (L a)) ^ 2 := hscale
      _ ≤ (K * Real.exp (-c * u)) / μmin ^ 2 := hdiv
      _ = K / μmin ^ 2 * Real.exp (-c * u) := by ring

end SwingRepair
