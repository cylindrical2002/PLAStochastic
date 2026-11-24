import PLAStochastic.ForMathlib.Probability.StoppedSum.PredictableWeights
import PLAStochastic.ForMathlib.Probability.StoppedSum.WaldENat
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Moments of sums stopped at an extended-valued stopping time

Segment lengths take values in `ℕ∞`.  For such a `T` whose events `{t < T}` are
`F t`-measurable, the truncated stopped sums are the predictably weighted sums
with weights `1{t < T}`.  Fatou's lemma turns the finite-horizon identities of
`PLAStochastic.ForMathlib.Probability.StoppedSum.PredictableWeights` into bounds for the stopped sum itself:

* `E[S_T^2] ≤ σ² E T` (`lintegral_stoppedSumE_sq_le`);
* `E|S_T|^3 ≤ 3σ³ B + κ E T` whenever `∑_{t<n} √t √P(t<T) ≤ B` for all `n`
  (`lintegral_stoppedSumE_cube_le`).

`stoppedSumE Y T ω = ∑_{t < T ω} Y t ω` (the value on `{T = ⊤}` is irrelevant).
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The weight `1{t < T}`. -/
noncomputable def stopWeight (T : Ω → ℕ∞) (t : ℕ) (ω : Ω) : ℝ :=
  if (t : ℕ∞) < T ω then 1 else 0

/-- The sum stopped at `T` (with an arbitrary value on `{T = ⊤}`). -/
noncomputable def stoppedSumE (Y : ℕ → Ω → ℝ) (T : Ω → ℕ∞) (ω : Ω) : ℝ :=
  partialSum Y (T ω).toNat ω

variable {P : Measure Ω} {F : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {T : Ω → ℕ∞}

theorem stopWeight_predictable (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω}) :
    PredictableWeight F (stopWeight T) := by
  refine ⟨fun t => ?_, fun t ω => ?_⟩
  · exact Measurable.ite (hT t) measurable_const measurable_const
  · unfold stopWeight; split_ifs <;> simp

omit mΩ in
theorem stopWeight_sq (T : Ω → ℕ∞) (t : ℕ) (ω : Ω) : stopWeight T t ω ^ 2 = stopWeight T t ω := by
  unfold stopWeight; split_ifs <;> simp

omit mΩ in
theorem abs_stopWeight_cube (T : Ω → ℕ∞) (t : ℕ) (ω : Ω) :
    |stopWeight T t ω| ^ 3 = stopWeight T t ω := by
  unfold stopWeight; split_ifs <;> simp

theorem integral_stopWeight [IsProbabilityMeasure P]
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω}) (t : ℕ) :
    ∫ ω, stopWeight T t ω ∂P = P.real {ω | (t : ℕ∞) < T ω} := by
  have : (fun ω => stopWeight T t ω) = Set.indicator {ω | (t : ℕ∞) < T ω} (fun _ => (1 : ℝ)) := by
    funext ω; simp [stopWeight, Set.indicator]
  rw [this, integral_indicator (F.le t _ (hT t))]
  simp

omit mΩ in
/-- Once the horizon passes `T ω`, the truncated sum is the stopped sum. -/
theorem weightedSum_stopWeight_eq (Y : ℕ → Ω → ℝ) (T : Ω → ℕ∞) {ω : Ω} (hω : T ω ≠ ⊤)
    {n : ℕ} (hn : (T ω).toNat ≤ n) :
    weightedSum (stopWeight T) Y n ω = stoppedSumE Y T ω := by
  set k := (T ω).toNat with hk
  have hTk : T ω = k := (ENat.natCast_toNat hω).symm
  simp only [weightedSum, stoppedSumE, partialSum, ← hk]
  rw [← sum_range_add_sum_Ico _ hn]
  have h1 : ∑ t ∈ range k, stopWeight T t ω * Y t ω = ∑ t ∈ range k, Y t ω :=
    sum_congr rfl fun t ht => by
      have : (t : ℕ∞) < T ω := by rw [hTk]; exact_mod_cast mem_range.1 ht
      simp [stopWeight, this]
  have h2 : ∑ t ∈ Ico k n, stopWeight T t ω * Y t ω = 0 :=
    sum_eq_zero fun t ht => by
      have : ¬ (t : ℕ∞) < T ω := by
        rw [hTk, not_lt]; exact_mod_cast (mem_Ico.1 ht).1
      simp [stopWeight, this]
  rw [h1, h2, add_zero]

theorem measurable_T_of_stopping (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω}) :
    Measurable T :=
  wald_measurable_of_lt fun t => F.le t _ (hT t)

/-- Fatou's lemma along the truncations, for a nonnegative continuous functional. -/
theorem lintegral_stopped_le_liminf {φ : ℝ → ℝ} (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤)
    (hmeas : ∀ n, Measurable fun ω => ENNReal.ofReal (φ (weightedSum (stopWeight T) Y n ω))) :
    ∫⁻ ω, ENNReal.ofReal (φ (stoppedSumE Y T ω)) ∂P ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (φ (weightedSum (stopWeight T) Y n ω)) ∂P) atTop := by
  calc ∫⁻ ω, ENNReal.ofReal (φ (stoppedSumE Y T ω)) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (φ (weightedSum (stopWeight T) Y n ω))) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with ω hω
        symm
        apply Filter.Tendsto.liminf_eq
        apply tendsto_atTop_of_eventually_const (i₀ := (T ω).toNat)
        intro n hn
        rw [weightedSum_stopWeight_eq Y T hω hn]
    _ ≤ _ := lintegral_liminf_le hmeas

/-- Second moment of a stopped sum of centred increments: `E[S_T^2] ≤ σ² E T`. -/
theorem lintegral_stoppedSumE_sq_le [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σsq : ℝ}
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σsq) (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (stoppedSumE Y T ω ^ 2) ∂P ≤
      ENNReal.ofReal σsq * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
  have hW := stopWeight_predictable hT
  have hσ0 : 0 ≤ σsq := le_trans (integral_nonneg fun _ => sq_nonneg _) (hσ 0)
  refine (lintegral_stopped_le_liminf (φ := fun x => x ^ 2) hfin
    (fun n => ((weightedSum_measurable h hW n).pow_const 2).ennreal_ofReal)).trans ?_
  refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
  have hint : Integrable (fun ω => weightedSum (stopWeight T) Y n ω ^ 2) P :=
    (memLp_weightedSum h hW hY2 n).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _),
    integral_weightedSum_sq h hW hY2 hY0 n]
  simp only [stopWeight_sq, integral_stopWeight hT]
  calc ENNReal.ofReal (∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω} * ∫ ω, Y t ω ^ 2 ∂P)
      ≤ ENNReal.ofReal (σsq * ∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω}) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_sum]
        exact sum_le_sum fun t _ => by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hσ t) measureReal_nonneg
    _ = ENNReal.ofReal σsq * ∑ t ∈ range n, P {ω | (t : ℕ∞) < T ω} := by
        rw [ENNReal.ofReal_mul hσ0, ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
        congr 1
        exact sum_congr rfl fun t _ => ofReal_measureReal (measure_ne_top _ _)
    _ ≤ ENNReal.ofReal σsq * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
        rw [lintegral_enat_eq_tsum (measurable_T_of_stopping hT)]
        gcongr
        exact ENNReal.sum_le_tsum _

/-- Cauchy–Schwarz for real square-integrable functions. -/
theorem sq_integral_mul_le [IsProbabilityMeasure P] {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * ∫ ω, g ω ^ 2 ∂P := by
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have key : ∀ x : ℝ, 0 ≤ (∫ ω, g ω ^ 2 ∂P) * (x * x) + (-(2 * ∫ ω, f ω * g ω ∂P)) * x +
      ∫ ω, f ω ^ 2 ∂P := by
    intro x
    have hnn : 0 ≤ ∫ ω, (f ω - x * g ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hexp : (fun ω => (f ω - x * g ω) ^ 2) =
        fun ω => f ω ^ 2 + ((-(2 * x)) * (f ω * g ω) + x ^ 2 * g ω ^ 2) := by
      funext ω; ring
    rw [hexp, integral_add (f := fun ω => f ω ^ 2)
      (g := fun ω => (-(2 * x)) * (f ω * g ω) + x ^ 2 * g ω ^ 2) hf.integrable_sq
      ((hfg.const_mul _).add (hg.integrable_sq.const_mul _)),
      integral_add (f := fun ω => (-(2 * x)) * (f ω * g ω)) (g := fun ω => x ^ 2 * g ω ^ 2)
      (hfg.const_mul _) (hg.integrable_sq.const_mul _),
      integral_const_mul, integral_const_mul] at hnn
    nlinarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- Third moment of a stopped sum of centred increments. -/
theorem lintegral_stoppedSumE_cube_le [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hY3 : ∀ t, MemLp (Y t) 3 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σ κ B : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σ ^ 2) (hκ : ∀ t, ∫ ω, |Y t ω| ^ 3 ∂P ≤ κ)
    (hB : ∀ n, ∑ t ∈ range n, Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω}) ≤ B)
    (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (|stoppedSumE Y T ω| ^ 3) ∂P ≤
      ENNReal.ofReal (3 * σ ^ 3 * B) + ENNReal.ofReal κ * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
  have hW := stopWeight_predictable hT
  have hY2 : ∀ t, MemLp (Y t) 2 P := fun t => (hY3 t).mono_exponent (by norm_num)
  have hκ0 : 0 ≤ κ := le_trans (integral_nonneg fun _ => by positivity) (hκ 0)
  refine (lintegral_stopped_le_liminf (φ := fun x => |x| ^ 3) hfin
    (fun n => ((continuous_abs.measurable.comp (weightedSum_measurable h hW n)).pow_const
      3).ennreal_ofReal)).trans ?_
  refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
  have hint : Integrable (fun ω => |weightedSum (stopWeight T) Y n ω| ^ 3) P :=
    memLp_three_integrable_abs_cube (memLp_weightedSum h hW hY3 n)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)]
  have hbase := integral_abs_weightedSum_cube_le h hW hY3 hY0 hσ hκ n
  simp only [stopWeight_sq, abs_stopWeight_cube, integral_stopWeight hT] at hbase
  -- each mixed term is at most `σ √t √P(t < T)`
  have hmix : ∀ t, ∫ ω, |weightedSum (stopWeight T) Y t ω| * stopWeight T t ω ∂P ≤
      σ * (Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω})) := by
    intro t
    have hM2 : MemLp (fun ω => |weightedSum (stopWeight T) Y t ω|) 2 P :=
      (memLp_weightedSum h hW hY2 t).abs
    have hw2 : MemLp (stopWeight T t) 2 P :=
      memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun ω => by
        unfold stopWeight; split_ifs <;> simp) (hW.measurable' t).aestronglyMeasurable 2
    have hcs := sq_integral_mul_le hM2 hw2
    have hsq1 : ∫ ω, |weightedSum (stopWeight T) Y t ω| ^ 2 ∂P ≤ σ ^ 2 * t := by
      simp only [sq_abs]
      rw [integral_weightedSum_sq h hW hY2 hY0 t]
      simp only [stopWeight_sq, integral_stopWeight hT]
      calc ∑ s ∈ range t, P.real {ω | (s : ℕ∞) < T ω} * ∫ ω, Y s ω ^ 2 ∂P
          ≤ ∑ _s ∈ range t, 1 * σ ^ 2 := sum_le_sum fun s _ =>
            mul_le_mul measureReal_le_one (hσ s) (integral_nonneg fun _ => sq_nonneg _)
              zero_le_one
        _ = σ ^ 2 * t := by simp; ring
    have hsq2 : ∫ ω, stopWeight T t ω ^ 2 ∂P = P.real {ω | (t : ℕ∞) < T ω} := by
      simp only [stopWeight_sq, integral_stopWeight hT]
    rw [hsq2] at hcs
    have hnn : 0 ≤ ∫ ω, |weightedSum (stopWeight T) Y t ω| * stopWeight T t ω ∂P :=
      integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (by unfold stopWeight; split_ifs <;> simp)
    have hrhs : (σ * (Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω}))) ^ 2 =
        σ ^ 2 * t * P.real {ω | (t : ℕ∞) < T ω} := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg t), Real.sq_sqrt measureReal_nonneg]
      ring
    have hle : (∫ ω, |weightedSum (stopWeight T) Y t ω| * stopWeight T t ω ∂P) ^ 2 ≤
        (σ * (Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω}))) ^ 2 := by
      rw [hrhs]
      exact hcs.trans (mul_le_mul_of_nonneg_right hsq1 measureReal_nonneg)
    exact (sq_le_sq₀ hnn (by positivity)).1 hle
  have hsum : ∑ t ∈ range n, (3 * σ ^ 2 *
        ∫ ω, |weightedSum (stopWeight T) Y t ω| * stopWeight T t ω ∂P +
        κ * P.real {ω | (t : ℕ∞) < T ω}) ≤
      3 * σ ^ 3 * B + κ * ∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω} := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 : ∑ t ∈ range n, ∫ ω, |weightedSum (stopWeight T) Y t ω| * stopWeight T t ω ∂P ≤
        σ * B := by
      calc _ ≤ ∑ t ∈ range n, σ * (Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω})) :=
            sum_le_sum fun t _ => hmix t
        _ = σ * ∑ t ∈ range n, Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω}) := by
            rw [mul_sum]
        _ ≤ σ * B := mul_le_mul_of_nonneg_left (hB n) hσ0
    have : 0 ≤ 3 * σ ^ 2 := by positivity
    nlinarith
  have hsumP : ENNReal.ofReal (∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω}) ≤
      ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg,
      lintegral_enat_eq_tsum (measurable_T_of_stopping hT)]
    calc ∑ t ∈ range n, ENNReal.ofReal (P.real {ω | (t : ℕ∞) < T ω})
        = ∑ t ∈ range n, P {ω | (t : ℕ∞) < T ω} :=
          sum_congr rfl fun t _ => ofReal_measureReal (measure_ne_top _ _)
      _ ≤ _ := ENNReal.sum_le_tsum _
  have hB0 : 0 ≤ B := le_trans (sum_nonneg fun t _ => by positivity) (hB 0)
  calc ENNReal.ofReal (∫ ω, |weightedSum (stopWeight T) Y n ω| ^ 3 ∂P)
      ≤ ENNReal.ofReal (3 * σ ^ 3 * B + κ * ∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω}) :=
        ENNReal.ofReal_le_ofReal (hbase.trans hsum)
    _ ≤ ENNReal.ofReal (3 * σ ^ 3 * B) +
          ENNReal.ofReal κ * ENNReal.ofReal (∑ t ∈ range n, P.real {ω | (t : ℕ∞) < T ω}) := by
        rw [← ENNReal.ofReal_mul hκ0]
        exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr

end PGM
