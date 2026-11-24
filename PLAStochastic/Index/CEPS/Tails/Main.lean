import PLAStochastic.Index.CEPS.Tails.CutoffBounds
import PLAStochastic.Index.CEPS.Tails.DrawupOccupation
import PLAStochastic.Index.CEPS.Tails.ScalarBudget

/-!
# Class-uniform actual outer tails

The positive outer pair, including the deterministic short prefix, is compared
with the actual `OK` drawup occupation. The negative outer pair is negligible.
Both conclusions hold for every mark with nonnegative real part, with constants
depending only on the regular-law class and the fixed drift cutoff.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset WienerHopf

/-- S-7(a)(b), for the actual pair and actual drawup occupation.
The same constants work for every law in the prescribed `RegLaw` class. -/
theorem ceps_outer_tails_of_regLaw {D θ vlo vhi δ : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ K C w₀ : ℝ, 0 < K ∧ 0 < C ∧ 0 < w₀ ∧
      ∀ (ν : ProbabilityMeasure ℝ), RegLaw D θ vlo vhi ν →
      ∀ (f : ℝ → ℝ), CepsGapDensity ν f D →
      ∀ (w : ℝ), w₀ ≤ w → ∀ (t : ℂ), 0 ≤ t.re →
        ‖(∑ k ∈ Finset.range (⌊w⌋₊ + 1), cepsLaplace ν t ^ k) +
            (∫ μ in Ici δ, cepsActualPair ν f (w / 2) t μ) -
            cepsDrawupOccupation ν δ (w * (1 + δ)) t‖ ≤
          K * w ^ 9 * Real.exp (-C * w) ∧
        ‖∫ μ in Ioo (-1) (-δ), cepsActualPair ν f (w / 2) t μ‖ ≤
          K * w ^ 9 * Real.exp (-C * w) := by
  let a := driftRate (D * Real.exp θ) θ δ * (1 - δ)
  let b := tailRate * regV vlo
  let c := driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2
  have hr := driftRate_pos hθ (show 0 < D * Real.exp θ by positivity) hδ
  have ha : 0 < a := mul_pos hr (sub_pos.mpr hδ1)
  have hb : 0 < b := mul_pos tailRate_pos (regV_pos hvlo)
  have hc : 0 < c := by
    have hr' := driftRate_pos hθ (show 0 < D * Real.exp θ by positivity) (half_pos hδ)
    dsimp [c]
    positivity
  obtain ⟨K, C, u, hK, hC, hu, hbudget⟩ :=
    cepsTail_exists_cubic_budget ha hb hc hδ hδ1.le
  let w₀ := max u (max 1 (2 * epsZero (regB vhi) (regBeta D θ vlo)))
  refine ⟨K, C, w₀, hK, hC, lt_of_lt_of_le hu (le_max_left _ _), ?_⟩
  intro ν hν f hf w hw t ht
  have hwu : u ≤ w := (le_max_left _ _).trans hw
  have hw1 : 1 ≤ w := (le_max_left _ _).trans ((le_max_right _ _).trans hw)
  have hw0 : 0 < w := by linarith
  have heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ w / 2 := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans hw)
    linarith
  let N : ℕ := ⌈w ^ 3⌉₊
  obtain ⟨hB, hN⟩ := hbudget w hwu
  change ((N : ℝ) + 1) ^ 3 * Real.exp (-a * w) +
      (72 / 71 : ℝ) * Real.exp (-(4 * b * N / w ^ 2)) /
        (1 - Real.exp (-(4 * b / w ^ 2))) +
      Real.exp (-c * N) / (1 - Real.exp (-c)) ≤ K * w ^ 9 * Real.exp (-C * w) at hB
  have hN' : 2 * (2 * (w / 2) * (1 + δ)) ≤ δ * N / 2 := by
    convert hN using 1
    ring
  have hfinite : driftRate (D * Real.exp θ) θ δ * (2 * (w / 2) * (1 - δ)) = a * w := by
    dsimp [a]
    ring
  have hlate : -(tailRate * regV vlo) * (N : ℝ) / (w / 2) ^ 2 = -(4 * b * N / w ^ 2) := by
    dsimp [b]
    field_simp
    ring
  have hrate : -(tailRate * regV vlo) / (w / 2) ^ 2 = -(4 * b / w ^ 2) := by
    dsimp [b]
    field_simp
    ring
  have hdenb : 0 < 1 - Real.exp (-(4 * b / w ^ 2)) := by
    have he := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (show 0 < 4 * b / w ^ 2 by positivity))
    linarith
  have hdenc : 0 < 1 - Real.exp (-c) := by
    have he := Real.exp_lt_one_iff.mpr (show -c < 0 by linarith)
    linarith
  have hneg := ceps_negative_tail_cutoff hν hθ hD hvlo hδ hδ1 heps hf ht N
  have hpos := ceps_positive_tail_cutoff hν hθ hD hvlo hδ heps hf ht N hN'
  simp only [Nat.cast_add, Nat.cast_one, hfinite, hlate, hrate] at hneg
  simp only [Nat.cast_add, Nat.cast_one, hfinite] at hpos
  rw [← neg_mul a w] at hneg hpos
  have hwid : 2 * (w / 2) = w := by ring
  rw [hwid] at hpos
  change _ ≤ ((N : ℝ) + 1) ^ 3 * Real.exp (-a * w) +
    Real.exp (-c * N) / (1 - Real.exp (-c)) at hpos
  constructor
  · refine hpos.trans (le_trans ?_ hB)
    have hnonneg : 0 ≤ (72 / 71 : ℝ) * Real.exp (-(4 * b * N / w ^ 2)) /
        (1 - Real.exp (-(4 * b / w ^ 2))) := by positivity
    linarith
  · refine hneg.trans (le_trans ?_ hB)
    have hnonneg : 0 ≤ Real.exp (-c * N) / (1 - Real.exp (-c)) := by positivity
    linarith

end

end PGM
