import PLAStochastic.Swing.FrozenCarry.Path.Prefix

/-! # Pathwise sublinear bounds for the actual frozen slope envelope -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Sublinear sequences admit a global linear envelope with an arbitrarily small slope. -/
theorem sublinear_succ_envelope {v : ℕ → ℝ}
    (hv : Tendsto (fun n => v n / ((n : ℝ)+1)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |v n| ≤ C+ε*((n : ℝ)+1) := by
  have ht : ∀ᶠ n : ℕ in atTop, |v n / ((n : ℝ)+1)| < ε := by
    simpa only [Real.norm_eq_abs, norm_zero] using hv.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  let C : ℝ := ∑ k ∈ Finset.range N, |v k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => abs_nonneg (v k))
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hb := hN n hn
    rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ)+1)] at hb
    have hh := (div_lt_iff₀ (by positivity : 0 < (n : ℝ)+1)).mp hb
    linarith
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hh : |v n| ≤ C := Finset.single_le_sum (fun k _ => abs_nonneg (v k)) hmem
    have hp : 0 ≤ ε*((n : ℝ)+1) := by positivity
    linarith

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {w : ℝ} {ω : Ω}

/-- Convergence to zero supplies the boundedness required by the actual real supremum. -/
theorem frozenSlopeMagnitude_bddAbove
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0)) :
    BddAbove (Set.range (fun n => -frozenUpperSlope X w n ω)) := hv.neg.bddAbove_range

theorem neg_frozenUpperSlope_le_magnitude
    (hb : BddAbove (Set.range (fun n => -frozenUpperSlope X w n ω))) (n : ℕ) :
    -frozenUpperSlope X w n ω ≤ frozenSlopeMagnitude X w ω :=
  le_csSup hb ⟨n, rfl⟩

/-- The true slope magnitude is nonnegative by the limiting zero slopes. -/
theorem frozenSlopeMagnitude_nonneg
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0)) :
    0 ≤ frozenSlopeMagnitude X w ω := by
  have h := le_of_tendsto hv.neg (Eventually.of_forall (neg_frozenUpperSlope_le_magnitude
    (frozenSlopeMagnitude_bddAbove hv)))
  simpa only [neg_zero] using h

/-- Any actual negative observed position makes the true slope magnitude strictly positive. -/
theorem frozenSlopeMagnitude_pos_of_negative
    (hv : Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0))
    (hn : ∃ n, w+cumulativeSamples X n ω < 0) : 0 < frozenSlopeMagnitude X w ω := by
  obtain ⟨n, hn⟩ := hn
  have hs : frozenUpperSlope X w n ω < 0 := div_neg_of_neg_of_pos hn (by positivity)
  exact (neg_pos.mpr hs).trans_le (neg_frozenUpperSlope_le_magnitude (frozenSlopeMagnitude_bddAbove hv) n)

/-- Choosing the actual extremal upper slope proves a whole prefix feasible at once. -/
theorem frozenPrefix_feasible_of_envelope
    (hb : BddAbove (Set.range (fun n => -frozenUpperSlope X w n ω)))
    {C ε E : ℝ} (hεA : 0 ≤ frozenSlopeMagnitude X w ω+ε)
    (hbound : ∀ j : ℕ, w+cumulativeSamples X j ω ≤ C+ε*((j : ℝ)+1))
    {n : ℕ} (hn : C+(frozenSlopeMagnitude X w ω+ε)*(n : ℝ) ≤ 2*E) :
    (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω := by
  apply (le_frozenPrefixLength_iff X w E n ω).mpr
  refine ⟨-frozenSlopeMagnitude X w ω, fun j hj => ?_⟩
  have hjp : 0 < (j : ℝ) := by have := Finset.mem_Icc.mp hj; exact_mod_cast (show 0 < j by omega)
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hjcast : ((j-1 : ℕ) : ℝ)+1 = j := by
    have hh : j-1+1 = j := by have := Finset.mem_Icc.mp hj; omega
    exact_mod_cast hh
  have hl := hbound (j-1)
  rw [hjcast] at hl
  have hu := neg_frozenUpperSlope_le_magnitude hb (j-1)
  change -((w+cumulativeSamples X (j-1) ω)/(((j-1 : ℕ) : ℝ)+1)) ≤ _ at hu
  rw [hjcast] at hu
  have hu' : -frozenSlopeMagnitude X w ω ≤ (w+cumulativeSamples X (j-1) ω)/(j : ℝ) := by linarith
  have hmul := (le_div_iff₀ hjp).mp hu'
  refine ⟨?_, hmul⟩
  nlinarith [mul_le_mul_of_nonneg_left hjn hεA]

end SwingRepair
