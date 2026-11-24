import PLAStochastic.Swing.Ladder.Law.CommonMinorization
import PLAStochastic.ForMathlib.Probability.Moments.IntegerGridExpTail

/-! Finite moments obtained directly from the proved compact exponential tail. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

theorem gaussianAscendingLadderHeight_integrable_compact
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    Integrable (gaussianAscendingLadderHeight X a) μ := by
  haveI : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let H : Ω → ℝ := gaussianAscendingLadderHeight X a
  let Y : Ω → ℝ := fun ω => max (H ω - M) 0
  have hH : Measurable H := gaussianAscendingLadderHeight_measurable hX a
  have hY : Measurable Y := (hH.sub measurable_const).max measurable_const
  have hYnonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω := Eventually.of_forall (fun ω => le_max_right _ _)
  let r : ℝ := gaussianAscendingLadderTailRate δ
  have hr : 0 < r := gaussianAscendingLadderTailRate_pos hδ
  let C : ℝ := 3 * Real.exp r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ Y ω} ≤
      ENNReal.ofReal (C * Real.exp (-r * (n : ℝ))) := by
    intro n
    by_cases hn0 : n ≤ 1
    · have hprob : μ {ω | (n : ℝ) ≤ Y ω} ≤ 1 := by
        calc μ {ω | (n : ℝ) ≤ Y ω} ≤ μ Set.univ := measure_mono (subset_univ _)
             _ = 1 := by simp
      have hge : (1 : ℝ) ≤ C * Real.exp (-r * (n : ℝ)) := by
        dsimp [C]
        have : (n : ℝ) ≤ 1 := by exact_mod_cast hn0
        have hexp : Real.exp r * Real.exp (-r * (n : ℝ)) =
            Real.exp (r + (-r * (n : ℝ))) := by rw [← Real.exp_add]
        rw [show (3 : ℝ) * Real.exp r * Real.exp (-r * (n : ℝ)) =
          3 * Real.exp (r + (-r * (n : ℝ))) by
            calc
              3 * Real.exp r * Real.exp (-r * (n : ℝ)) =
                  3 * (Real.exp r * Real.exp (-r * (n : ℝ))) := by ring
              _ = 3 * Real.exp (r + (-r * (n : ℝ))) := by rw [hexp]]
        have harg : 0 ≤ r + (-r * (n : ℝ)) := by nlinarith
        nlinarith [Real.one_le_exp harg]
      exact hprob.trans (by simpa using (ENNReal.ofReal_le_ofReal hge))
    · have hn2 : 2 ≤ n := by omega
      have hsubset : {ω | (n : ℝ) ≤ Y ω} ⊆
          {ω | M + ((n-1 : ℕ) : ℝ) < H ω} := by
        intro ω hω
        have hω' : (n : ℝ) ≤ max (H ω - M) 0 := hω
        have hpos : 0 < (n : ℝ) := by positivity
        have hsub : (n : ℝ) ≤ H ω - M := by
          by_contra hnot
          have hlt : H ω - M < (n : ℝ) := lt_of_not_ge hnot
          have hmax : max (H ω - M) 0 < (n : ℝ) := max_lt_iff.mpr ⟨hlt, hpos⟩
          linarith
        have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (R := ℝ) (m := 1) (n := n) (by omega)]
          norm_num
        rw [hcast]
        change M + ((n : ℝ) - 1) < H ω
        linarith
      have hreal := (measureReal_mono hsubset).trans
        (gaussianAscendingLadderHeight_compact_tail hX hi hG hδ hδa haM (N := n-1) (by omega))
      · rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        apply ENNReal.ofReal_le_ofReal
        calc
          μ.real {ω | (n : ℝ) ≤ Y ω} ≤
              3 * Real.exp (-r * ((n-1 : ℕ) : ℝ)) := hreal
          _ = C * Real.exp (-r * (n : ℝ)) := by
            dsimp [C]
            rw [show ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 by
              rw [Nat.cast_sub (R := ℝ) (m := 1) (n := n) (by omega)]; norm_num]
            calc
              3 * Real.exp (-r * ((n : ℝ) - 1)) =
                  3 * Real.exp (r + (-r * (n : ℝ))) := by
                    have he : -r * ((n : ℝ) - 1) = r + (-r * (n : ℝ)) := by ring
                    rw [he]
              _ = 3 * Real.exp r * Real.exp (-r * (n : ℝ)) := by
                rw [Real.exp_add]
                ring
  have hYint : Integrable Y μ := by
    simpa [Y] using (integrable_pow_of_expTail hY hYnonneg hC hr htail 1)
  have hbound : ∀ᵐ ω ∂μ, ‖H ω‖ ≤ M + Y ω := by
    filter_upwards [] with ω
    have hHnonneg : 0 ≤ H ω := by
      simpa [H] using (gaussianAscendingLadderHeight_nonneg (X := X) a ω)
    dsimp [Y]
    by_cases hh : H ω ≤ M
    · have hMnonneg : 0 ≤ M := hδ.le.trans hδa |>.trans haM
      rw [abs_of_nonneg hHnonneg, max_eq_right (sub_nonpos.mpr hh)]
      linarith
    · have h : H ω - M > 0 := by linarith
      rw [abs_of_nonneg hHnonneg, max_eq_left (le_of_lt h)]
      have hMnonneg : 0 ≤ M := hδ.le.trans hδa |>.trans haM
      linarith
  have hmajor : Integrable (fun ω => M + Y ω) μ := (integrable_const M).add hYint
  apply hmajor.mono' hH.aestronglyMeasurable
  simpa [Pi.add_apply] using hbound

end SwingRepair
