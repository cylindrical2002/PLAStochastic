import PLAStochastic.Swing.Restart.Chain.PathwiseBounds
import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail
import PLAStochastic.Swing.FrozenCarry.Path.SlopeLaw

/-! # The actual fresh-walk slope envelope has a uniform Gaussian tail -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The unused zero partial sum is omitted from the supremum. -/
def nativeGaussianEnvelope (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  max 0 (⨆ n : ℕ, |cumulativeSamples X (n+1) ω|/((n : ℝ)+2))

def nativeGaussianEnvelopeTailConstant : ℝ := 2/(1-Real.exp (-(1/2 : ℝ)))

omit [MeasurableSpace Ω] in
theorem nativeGaussianEnvelope_nonneg (X : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ nativeGaussianEnvelope X ω := le_max_left _ _

theorem nativeGaussianEnvelope_measurable (hX : ∀ n, Measurable (X n)) :
    Measurable (nativeGaussianEnvelope X) := by
  exact measurable_const.max (Measurable.iSup fun n =>
    ((Finset.measurable_sum (Finset.range (n+1)) (fun k _ => hX k)).abs.div_const _))

theorem nativeGaussianEnvelope_bounds_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ nativeGaussianEnvelope X ω*((n : ℝ)+1) := by
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hX hi hG 0] with ω hω
  have ht : Tendsto (fun n : ℕ => |cumulativeSamples X (n+1) ω|/((n : ℝ)+2))
      atTop (𝓝 0) := by
    have hh := (hω.comp (tendsto_add_atTop_nat 1)).abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [] with n
    dsimp only [Function.comp_def, frozenUpperSlope]
    rw [zero_add, abs_div, abs_of_pos (by positivity : 0 < ((n+1 : ℕ) : ℝ)+1)]
    push_cast
    congr 1
    ring
  intro n
  cases n with
  | zero => simp [nativeGaussianEnvelope_nonneg]
  | succ n =>
    have hh : |cumulativeSamples X (n+1) ω|/((n : ℝ)+2) ≤ nativeGaussianEnvelope X ω :=
      (le_ciSup ht.bddAbove_range n).trans (le_max_right _ _)
    have hp : (0 : ℝ) < (n : ℝ)+2 := by positivity
    have hb := (div_le_iff₀ hp).mp hh
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hb

theorem nativeGaussianEnvelope_tail_constant_pos : 0 < nativeGaussianEnvelopeTailConstant := by
  have hq : Real.exp (-(1/2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact div_pos (by norm_num) (sub_pos.mpr hq)

/-- The tail estimate is a union bound over genuine Gaussian partial sums. -/
theorem nativeGaussianEnvelope_tail_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {t : ℝ} (ht : 1 ≤ t) :
    μ.real {ω | t < nativeGaussianEnvelope X ω} ≤
      nativeGaussianEnvelopeTailConstant*Real.exp (-t^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have ht0 : 0 ≤ t := by linarith
  let q : ℝ := Real.exp (-(1/2 : ℝ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  let S : ℕ → Set Ω := fun n => {ω | t*((n : ℝ)+2) ≤ |cumulativeSamples X (n+1) ω|}
  have hcover : {ω | t < nativeGaussianEnvelope X ω} ⊆ ⋃ n, S n := by
    intro ω hω
    by_contra hn
    have hall : ∀ n, |cumulativeSamples X (n+1) ω|/((n : ℝ)+2) ≤ t := by
      intro n
      have hnot : ω ∉ S n := fun h => hn (mem_iUnion.mpr ⟨n, h⟩)
      have hlt : |cumulativeSamples X (n+1) ω| < t*((n : ℝ)+2) := lt_of_not_ge hnot
      exact ((div_lt_iff₀ (by positivity : 0 < (n : ℝ)+2)).mpr hlt).le
    have hb : nativeGaussianEnvelope X ω ≤ t := max_le ht0 (ciSup_le hall)
    exact (not_lt_of_ge hb) hω
  have htail (n : ℕ) : μ.real (S n) ≤ 2*Real.exp (-t^2)*q^n := by
    have hh := cumulativeSamples_abs_tail_bound hX hi hG (n+1)
      (show 0 ≤ t*((n : ℝ)+2) by positivity)
    refine hh.trans ?_
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hnp : 0 < 2*((n+1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hnp).mpr
    push_cast
    have ht2 : 1 ≤ t^2 := by nlinarith
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (sub_nonneg.mpr ht2) hn,
      mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg (n : ℝ))]
  have hsum : Summable (fun n : ℕ => 2*Real.exp (-t^2)*q^n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have htotal : (∑' n : ℕ, 2*Real.exp (-t^2)*q^n) =
      nativeGaussianEnvelopeTailConstant*Real.exp (-t^2) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    dsimp [nativeGaussianEnvelopeTailConstant, q]
    ring
  have hENN : μ {ω | t < nativeGaussianEnvelope X ω} ≤
      ENNReal.ofReal (nativeGaussianEnvelopeTailConstant*Real.exp (-t^2)) := by
    calc
      _ ≤ μ (⋃ n, S n) := measure_mono hcover
      _ ≤ ∑' n, μ (S n) := measure_iUnion_le S
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (2*Real.exp (-t^2)*q^n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        have hh := ENNReal.ofReal_le_ofReal (htail n)
        simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ (S n))] using hh
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, htotal]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (mul_nonneg nativeGaussianEnvelope_tail_constant_pos.le (Real.exp_pos _).le)] using hh

end SwingRepair
