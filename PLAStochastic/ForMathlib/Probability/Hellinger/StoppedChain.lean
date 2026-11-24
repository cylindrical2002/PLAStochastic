import PLAStochastic.ForMathlib.Probability.Hellinger.Joint
import PLAStochastic.ForMathlib.Probability.NatExpectation.TruncatedTail

/-!
# Active-step chain budgets and stopping-time tail sums

The one-step bound follows from the exact joint-density chain rule. Only states
in the active event pay for a conditional perturbation. Finite tail sums are
bounded by the actual stopping-time first moment under each density; no
independence between increments and the stopping decision is assumed.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

theorem sqrt_mul_le_average {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Conditional distances vanish after stopping; active states pay only their mass. -/
theorem hellinger_sq_joint_le_active [SFinite μ] [SFinite ν]
    (p q : HellingerDensity μ) (k l : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2))
    (hl : Measurable (fun z : α × β => (l z.1).density z.2))
    {s : Set α} (hs : MeasurableSet s) {δ : ℝ}
    (hcond : ∀ x, ((k x).hellinger (l x)) ^ 2 ≤ s.indicator (fun _ => δ ^ 2) x) :
    (p.joint k hk).hellinger (q.joint l hl) ^ 2 ≤ p.hellinger q ^ 2 +
      δ ^ 2 / 2 * (p.mass s + q.mass s) := by
  rw [hellinger_sq_joint]
  apply add_le_add le_rfl
  have hip := p.integrable.indicator hs
  have hiq := q.integrable.indicator hs
  calc
    (∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        ((k x).hellinger (l x)) ^ 2 ∂μ) ≤
        ∫ x, δ ^ 2 / 2 * (s.indicator p.density x + s.indicator q.density x) ∂μ := by
      apply integral_mono (weighted_conditional_hellinger_integrable p q k l hk hl)
        ((hip.add hiq).const_mul (δ ^ 2 / 2))
      intro x
      change Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        ((k x).hellinger (l x)) ^ 2 ≤
        δ ^ 2 / 2 * (s.indicator p.density x + s.indicator q.density x)
      have hx := hcond x
      by_cases hxs : x ∈ s
      · simp only [indicator_of_mem hxs] at hx ⊢
        have hmul := mul_le_mul_of_nonneg_left hx
          (mul_nonneg (Real.sqrt_nonneg (p.density x)) (Real.sqrt_nonneg (q.density x)))
        have havg := mul_le_mul_of_nonneg_right
          (sqrt_mul_le_average (p.nonneg x) (q.nonneg x)) (sq_nonneg δ)
        nlinarith only [hmul, havg]
      · simp only [indicator_of_notMem hxs] at hx ⊢
        have hz : (k x).hellinger (l x) ^ 2 = 0 := le_antisymm hx (sq_nonneg _)
        rw [hz]
        simp
    _ = δ ^ 2 / 2 * (p.mass s + q.mass s) := by
      rw [integral_const_mul, integral_add hip hiq, integral_indicator hs,
        integral_indicator hs]
      rfl

/-- Tail masses of a stopping time, weighted by the actual density. -/
theorem sum_mass_tail_le_integral (p : HellingerDensity μ) {T : α → ℕ}
    (hT : Measurable T) (hInt : Integrable (fun x => (T x : ℝ) * p.density x) μ)
    (N : ℕ) :
    ∑ j ∈ range N, p.mass {x | j < T x} ≤ ∫ x, (T x : ℝ) * p.density x ∂μ := by
  have hs (j : ℕ) : MeasurableSet {x | j < T x} :=
    hT (measurableSet_lt measurable_const measurable_id)
  have hi (j : ℕ) : Integrable ({x | j < T x}.indicator p.density) μ :=
    p.integrable.indicator (hs j)
  have he : (∑ j ∈ range N, p.mass {x | j < T x}) =
      ∫ x, ((min (T x) N : ℕ) : ℝ) * p.density x ∂μ := by
    simp only [mass, ← integral_indicator (hs _)]
    rw [← integral_finsetSum _ (fun j _ => hi j)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have hpoint (j : ℕ) : {x | j < T x}.indicator p.density x =
          ({x | j < T x}.indicator (fun _ => (1 : ℝ)) x) * p.density x := by
        by_cases hx : j < T x
        · simp only [indicator_of_mem (show x ∈ {x | j < T x} from hx), one_mul]
        · simp only [indicator_of_notMem (show x ∉ {x | j < T x} from hx), zero_mul]
      simp_rw [hpoint, ← sum_mul, sum_indicator_nat_gt]
  rw [he]
  have htrunc : Integrable (fun x => ((min (T x) N : ℕ) : ℝ) * p.density x) μ := by
    apply (p.integrable.const_mul (N : ℝ)).mono'
      ((measurable_from_nat.comp (hT.min measurable_const)).mul
        p.measurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖((min (T x) N : ℕ) : ℝ) * p.density x‖ ≤ (N : ℝ) * p.density x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (p.nonneg x))]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right (T x) N)) (p.nonneg x)
  exact integral_mono htrunc hInt (fun x =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left (T x) N)) (p.nonneg x))

/-- Accumulated active-step budgets are controlled by stopping-time means, not depth. -/
theorem stopped_chain_sq_le (p q : HellingerDensity μ) {T S : α → ℕ}
    (hT : Measurable T) (hS : Measurable S)
    (hTp : Integrable (fun x => (T x : ℝ) * p.density x) μ)
    (hSq : Integrable (fun x => (S x : ℝ) * q.density x) μ)
    {h : ℕ → ℝ} {δ : ℝ} (h0 : h 0 = 0)
    (hstep : ∀ j, h (j + 1) ^ 2 ≤ h j ^ 2 +
      δ ^ 2 / 2 * (p.mass {x | j < T x} + q.mass {x | j < S x})) (N : ℕ) :
    h N ^ 2 ≤ δ ^ 2 / 2 *
      ((∫ x, (T x : ℝ) * p.density x ∂μ) + (∫ x, (S x : ℝ) * q.density x ∂μ)) := by
  have hsum : ∀ n, h n ^ 2 ≤ δ ^ 2 / 2 *
      (∑ j ∈ range n, (p.mass {x | j < T x} + q.mass {x | j < S x})) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [sum_range_succ, mul_add]
      exact (hstep n).trans (add_le_add ih le_rfl)
  have hb := add_le_add (sum_mass_tail_le_integral p hT hTp N)
    (sum_mass_tail_le_integral q hS hSq N)
  have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ δ ^ 2 / 2)
  simp only [sum_add_distrib] at hsum
  exact (hsum N).trans hc

end

end ProbabilityTheory.HellingerDensity
