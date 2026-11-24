import PLAStochastic.Swing.FrozenCarry.Path.FloorFeasibility
import PLAStochastic.Swing.FrozenCarry.Path.SlopeLaw

/-! # The actual pathwise frozen carry length limit -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Finite native lengths are converted to real values only after finiteness has been proved. -/
def frozenPrefixLengthReal {Ω : Type*} (X : ℕ → Ω → ℝ) (w E : ℝ) (ω : Ω) : ℝ :=
  ((frozenPrefixLength X w E ω).untopD 0 : ℕ)

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {w : ℝ} {ω : Ω}

/-- On each sublinear path with positive actual magnitude, every tolerance has a finite prefix. -/
theorem frozenPrefixLength_finite_of_magnitude
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hA : 0 < frozenSlopeMagnitude X w ω) (E : ℝ) : frozenPrefixLength X w E ω ≠ ⊤ := by
  obtain ⟨u, ⟨j, rfl⟩, hj⟩ := exists_lt_of_lt_csSup
    (show (Set.range (fun n => -frozenUpperSlope X w n ω)).Nonempty from Set.range_nonempty _) hA
  exact frozenPrefixLength_finite_of_sublinear hv ⟨j, by linarith⟩ E

/-- Theorem 3.1 pathwise core for all real tolerances tending to infinity. -/
theorem frozenPrefixLengthReal_tendsto_of_sublinear
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hA : 0 < frozenSlopeMagnitude X w ω) :
    Tendsto (fun E : ℝ => frozenPrefixLengthReal X w E ω / E) atTop
      (𝓝 (2/frozenSlopeMagnitude X w ω)) := by
  have ht := frozenPrefixLength_finite_of_magnitude hv hA
  have hlim : 0 < 2/frozenSlopeMagnitude X w ω := div_pos (by norm_num) hA
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨q, hq, hql⟩ := exists_between (show max 0 b < 2/frozenSlopeMagnitude X w ω from max_lt hlim hb)
    have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hq
    have hbq : b < q := lt_of_le_of_lt (le_max_right _ _) hq
    have hfl := (tendsto_nat_floor_mul_div_atTop hq0.le).eventually (Ioi_mem_nhds hbq)
    filter_upwards [frozenPrefix_floor_feasible_eventually hv hA hq0 hql, hfl,
      eventually_gt_atTop (0 : ℝ)] with E hE hfloor hE0
    have hN : (⌊q*E⌋₊ : ℝ) ≤ frozenPrefixLengthReal X w E ω := by
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ht E)
      rw [← hk] at hE
      have hh : ⌊q*E⌋₊ ≤ k := WithTop.coe_le_coe.mp hE
      have hkR : frozenPrefixLengthReal X w E ω = k := by rw [frozenPrefixLengthReal, ← hk]; rfl
      rw [hkR]
      exact_mod_cast hh
    exact hfloor.trans_le (div_le_div_of_nonneg_right hN hE0.le)
  · intro b hb
    obtain ⟨q, hlq, hqb⟩ := exists_between hb
    have hq0 : 0 < q := hlim.trans hlq
    have hfl := (tendsto_nat_floor_mul_div_atTop hq0.le).eventually (Iio_mem_nhds hqb)
    filter_upwards [frozenPrefix_floor_infeasible_eventually hv hA hlq, hfl,
      eventually_gt_atTop (0 : ℝ)] with E hE hfloor hE0
    have hN : frozenPrefixLengthReal X w E ω < (⌊q*E⌋₊ : ℝ) := by
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ht E)
      rw [← hk] at hE
      have hh : k < ⌊q*E⌋₊ := lt_of_not_ge (fun h => hE (WithTop.coe_le_coe.mpr h))
      have hkR : frozenPrefixLengthReal X w E ω = k := by rw [frozenPrefixLengthReal, ← hk]; rfl
      rw [hkR]
      exact_mod_cast hh
    exact (div_lt_div_of_pos_right hN hE0).trans hfloor

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual Gaussian frozen-state limit on one full-measure set for every real tolerance. -/
theorem frozenPrefixLength_tendsto_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) :
    ∀ᵐ ω ∂μ, 0 < frozenSlopeMagnitude X w ω ∧
      (∀ E : ℝ, frozenPrefixLength X w E ω ≠ ⊤) ∧
      Tendsto (fun E : ℝ => frozenPrefixLengthReal X w E ω/E) atTop
        (𝓝 (2/frozenSlopeMagnitude X w ω)) := by
  filter_upwards [frozenSlopeMagnitude_positive_ae hX hi hG w] with ω hω
  exact ⟨hω.2, frozenPrefixLength_finite_of_magnitude hω.1 hω.2,
    frozenPrefixLengthReal_tendsto_of_sublinear hω.1 hω.2⟩

end SwingRepair
