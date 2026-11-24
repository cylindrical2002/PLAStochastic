import PLAStochastic.ForMathlib.Probability.StoppedSum.IndepIncrements
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Data.ENNReal.Holder

/-!
# Moments of predictably weighted sums of independent increments

For increments `Y` with `IndepIncrements P F Y` and weights `H t` that are
`F t`-measurable with `|H t| ≤ 1`, put `M n = ∑ t < n, H t * Y t`.
The single engine of this file is the bilinear orthogonality relation

`E[M^H_n M^K_n] = ∑ t < n, E[H_t K_t] E[Y_t^2]`   (centred `Y`),

and a third-moment recursion from the pointwise inequality
`|a+b|^3 ≤ |a|^3 + 3 a|a| b + 3|a| b^2 + |b|^3`.  Taking `H ≡ 1` gives plain
partial sums, `H t = 1{t < T}` gives stopped sums, and `H t = ±1` gives the
signed block sums of the anti-concentration argument.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `weightedSum H Y n = ∑ t < n, H t * Y t`. -/
def weightedSum (H Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, H t ω * Y t ω

omit mΩ in
@[simp] theorem weightedSum_zero (H Y : ℕ → Ω → ℝ) : weightedSum H Y 0 = fun _ => 0 := by
  funext ω; simp [weightedSum]

omit mΩ in
theorem weightedSum_succ (H Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedSum H Y (n + 1) ω = weightedSum H Y n ω + H n ω * Y n ω := by
  simp [weightedSum, sum_range_succ]

/-- Predictable weights bounded by one. -/
structure PredictableWeight (F : Filtration ℕ mΩ) (H : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable[F t] (H t)
  abs_le_one : ∀ t ω, |H t ω| ≤ 1

theorem PredictableWeight.one (F : Filtration ℕ mΩ) :
    PredictableWeight F (fun _ _ => (1 : ℝ)) :=
  ⟨fun _ => measurable_const, fun _ _ => by simp⟩

variable {P : Measure Ω} {F : Filtration ℕ mΩ} {Y H K : ℕ → Ω → ℝ}

theorem IndepIncrements.measurable' (h : IndepIncrements P F Y) (t : ℕ) :
    Measurable (Y t) :=
  (h.measurable t).mono (F.le (t + 1)) le_rfl

theorem PredictableWeight.measurable' (hH : PredictableWeight F H) (t : ℕ) :
    Measurable (H t) :=
  (hH.measurable t).mono (F.le t) le_rfl

theorem weightedSum_measurable_past (h : IndepIncrements P F Y) (hH : PredictableWeight F H)
    (n : ℕ) : Measurable[F n] (weightedSum H Y n) := by
  unfold weightedSum
  refine Finset.measurable_fun_sum _ fun t ht => ?_
  have ht' : t + 1 ≤ n := Finset.mem_range.1 ht
  exact ((hH.measurable t).mono (F.mono (by omega)) le_rfl).mul
    ((h.measurable t).mono (F.mono ht') le_rfl)

theorem weightedSum_measurable (h : IndepIncrements P F Y) (hH : PredictableWeight F H)
    (n : ℕ) : Measurable (weightedSum H Y n) :=
  (weightedSum_measurable_past h hH n).mono (F.le n) le_rfl

theorem memLp_weight_mul {p : ENNReal} (h : IndepIncrements P F Y) (hH : PredictableWeight F H)
    (hY : ∀ t, MemLp (Y t) p P) (t : ℕ) : MemLp (fun ω => H t ω * Y t ω) p P := by
  refine (hY t).of_le ((hH.measurable' t).mul (h.measurable' t)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hH.abs_le_one t ω)

theorem memLp_weightedSum {p : ENNReal} (h : IndepIncrements P F Y)
    (hH : PredictableWeight F H) (hY : ∀ t, MemLp (Y t) p P) (n : ℕ) :
    MemLp (weightedSum H Y n) p P := by
  unfold weightedSum
  exact memLp_finsetSum _ fun t _ => memLp_weight_mul h hH hY t

/-- Independence of the next increment from a past-measurable factor, after
    applying a measurable function to the increment. -/
theorem IndepIncrements.integral_mul_past_comp (h : IndepIncrements P F Y) (t : ℕ)
    {Z : Ω → ℝ} (hZ : Measurable[F t] Z) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ ω, Z ω * φ (Y t ω) ∂P = (∫ ω, Z ω ∂P) * ∫ ω, φ (Y t ω) ∂P := by
  have hind : IndepFun (fun ω => φ (Y t ω)) Z P := (h.indepFun_past t hZ).comp hφ measurable_id
  exact hind.symm.integral_mul_eq_mul_integral
    ((hZ.mono (F.le t) le_rfl).aestronglyMeasurable)
    (hφ.comp (h.measurable' t)).aestronglyMeasurable

theorem memLp_mul_weight {p : ENNReal} {Z : Ω → ℝ} (hZ : MemLp Z p P)
    (hH : PredictableWeight F H) (t : ℕ) : MemLp (fun ω => Z ω * H t ω) p P := by
  refine hZ.of_le (hZ.aestronglyMeasurable.mul (hH.measurable' t).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hH.abs_le_one t ω)

theorem integrable_sq_of_memLp {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    Integrable (fun ω => Z ω ^ 2) P := hZ.integrable_sq

/-- Bilinear orthogonality of two predictably weighted sums of centred increments. -/
theorem integral_weightedSum_mul [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hH : PredictableWeight F H) (hK : PredictableWeight F K)
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) :
    ∀ n, ∫ ω, weightedSum H Y n ω * weightedSum K Y n ω ∂P =
      ∑ t ∈ range n, (∫ ω, H t ω * K t ω ∂P) * ∫ ω, Y t ω ^ 2 ∂P
  | 0 => by simp
  | n + 1 => by
    have ih := integral_weightedSum_mul h hH hK hY2 hY0 n
    set A := weightedSum H Y n with hA
    set B := weightedSum K Y n with hB
    have hA2 : MemLp A 2 P := memLp_weightedSum h hH hY2 n
    have hB2 : MemLp B 2 P := memLp_weightedSum h hK hY2 n
    have hAm : Measurable[F n] A := weightedSum_measurable_past h hH n
    have hBm : Measurable[F n] B := weightedSum_measurable_past h hK n
    have hexp : (fun ω => weightedSum H Y (n + 1) ω * weightedSum K Y (n + 1) ω) =
        fun ω => A ω * B ω + (A ω * K n ω) * Y n ω + (B ω * H n ω) * Y n ω +
          (H n ω * K n ω) * (Y n ω) ^ 2 := by
      funext ω; rw [weightedSum_succ, weightedSum_succ]; ring
    have i1 : Integrable (fun ω => A ω * B ω) P := hA2.integrable_mul hB2
    have i2 : Integrable (fun ω => (A ω * K n ω) * Y n ω) P :=
      (memLp_mul_weight hA2 hK n).integrable_mul (hY2 n)
    have i3 : Integrable (fun ω => (B ω * H n ω) * Y n ω) P :=
      (memLp_mul_weight hB2 hH n).integrable_mul (hY2 n)
    have i4 : Integrable (fun ω => (H n ω * K n ω) * (Y n ω) ^ 2) P := by
      refine (hY2 n).integrable_sq.bdd_mul
        ((hH.measurable' n).mul (hK.measurable' n)).aestronglyMeasurable
        (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      nlinarith [hH.abs_le_one n ω, hK.abs_le_one n ω, abs_nonneg (H n ω), abs_nonneg (K n ω)]
    rw [hexp,
      integral_add (f := fun ω => A ω * B ω + A ω * K n ω * Y n ω + B ω * H n ω * Y n ω)
        (g := fun ω => H n ω * K n ω * Y n ω ^ 2) ((i1.add i2).add i3) i4,
      integral_add (f := fun ω => A ω * B ω + A ω * K n ω * Y n ω)
        (g := fun ω => B ω * H n ω * Y n ω) (i1.add i2) i3,
      integral_add (f := fun ω => A ω * B ω) (g := fun ω => A ω * K n ω * Y n ω) i1 i2]
    have e2 : ∫ ω, (A ω * K n ω) * Y n ω ∂P = 0 := by
      rw [h.integral_mul_past n (Z := fun ω => A ω * K n ω) (hAm.mul (hK.measurable n))
        (h.measurable' n), hY0 n,
        mul_zero]
    have e3 : ∫ ω, (B ω * H n ω) * Y n ω ∂P = 0 := by
      rw [h.integral_mul_past n (Z := fun ω => B ω * H n ω) (hBm.mul (hH.measurable n))
        (h.measurable' n), hY0 n,
        mul_zero]
    have e4 : ∫ ω, (H n ω * K n ω) * (Y n ω) ^ 2 ∂P =
        (∫ ω, H n ω * K n ω ∂P) * ∫ ω, Y n ω ^ 2 ∂P :=
      h.integral_mul_past_comp n (Z := fun ω => H n ω * K n ω)
        ((hH.measurable n).mul (hK.measurable n))
        (φ := fun x => x ^ 2) (by fun_prop)
    rw [e2, e3, e4, ih, sum_range_succ]
    ring

/-- The second moment of a predictably weighted sum. -/
theorem integral_weightedSum_sq [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hH : PredictableWeight F H) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) (n : ℕ) :
    ∫ ω, weightedSum H Y n ω ^ 2 ∂P =
      ∑ t ∈ range n, (∫ ω, H t ω ^ 2 ∂P) * ∫ ω, Y t ω ^ 2 ∂P := by
  have := integral_weightedSum_mul h hH hH hY2 hY0 n
  simpa [sq] using this

/-! ## Kolmogorov's maximal inequality -/

omit mΩ in
theorem partialSum_eq_weightedSum_one (Y : ℕ → Ω → ℝ) :
    partialSum Y = weightedSum (fun _ _ => (1 : ℝ)) Y := by
  funext n ω; simp [partialSum, weightedSum]

/-- The weight "the partial sums have stayed below `λ` up to time `t`". -/
noncomputable def belowWeight (Y : ℕ → Ω → ℝ) (lam : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if ∀ k ≤ t, |partialSum Y k ω| < lam then 1 else 0

theorem partialSum_measurable_past (h : IndepIncrements P F Y) (n : ℕ) :
    Measurable[F n] (partialSum Y n) := by
  rw [partialSum_eq_weightedSum_one]
  exact weightedSum_measurable_past h (PredictableWeight.one F) n

theorem belowWeight_predictable (h : IndepIncrements P F Y) (lam : ℝ) :
    PredictableWeight F (belowWeight Y lam) := by
  refine ⟨fun t => ?_, fun t ω => ?_⟩
  · unfold belowWeight
    refine Measurable.ite ?_ measurable_const measurable_const
    have : {ω | ∀ k ≤ t, |partialSum Y k ω| < lam} =
        ⋂ k ∈ Finset.range (t + 1), {ω | |partialSum Y k ω| < lam} := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]; exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩
    rw [this]
    refine MeasurableSet.biInter (Finset.range (t + 1)).countable_toSet fun k hk => ?_
    have hk' : k ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hm : Measurable[F t] (partialSum Y k) :=
      (partialSum_measurable_past h k).mono (F.mono hk') le_rfl
    exact measurableSet_lt (continuous_abs.measurable.comp hm : Measurable[F t] fun ω => |partialSum Y k ω|)
      measurable_const
  · unfold belowWeight; split_ifs <;> simp

/-- Kolmogorov's maximal inequality for centred square-integrable increments. -/
theorem kolmogorov_maximal [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {lam : ℝ} (hlam : 0 < lam)
    (n : ℕ) :
    lam ^ 2 * P.real {ω | ∃ k ≤ n, lam ≤ |partialSum Y k ω|} ≤
      ∫ ω, partialSum Y n ω ^ 2 ∂P := by
  set H := belowWeight Y lam with hHdef
  set K : ℕ → Ω → ℝ := fun t ω => 1 - H t ω with hKdef
  have hH : PredictableWeight F H := belowWeight_predictable h lam
  have hK : PredictableWeight F K := by
    refine ⟨fun t => measurable_const.sub (hH.measurable t), fun t ω => ?_⟩
    simp only [hKdef, hHdef, belowWeight]; split_ifs <;> simp
  have hsplit : ∀ ω, partialSum Y n ω = weightedSum H Y n ω + weightedSum K Y n ω := by
    intro ω; simp only [partialSum, weightedSum, hKdef, ← Finset.sum_add_distrib]
    congr 1; funext t; ring
  have hHK : ∀ t, ∫ ω, H t ω * K t ω ∂P = 0 := by
    intro t
    have : (fun ω => H t ω * K t ω) = fun _ => 0 := by
      funext ω; simp only [hKdef, hHdef, belowWeight]; split_ifs <;> simp
    rw [this]; simp
  have horth := integral_weightedSum_mul h hH hK hY2 hY0 n
  simp only [hHK, zero_mul, Finset.sum_const_zero] at horth
  have hA2 : MemLp (weightedSum H Y n) 2 P := memLp_weightedSum h hH hY2 n
  have hB2 : MemLp (weightedSum K Y n) 2 P := memLp_weightedSum h hK hY2 n
  have hSn : ∫ ω, partialSum Y n ω ^ 2 ∂P =
      ∫ ω, weightedSum H Y n ω ^ 2 ∂P + ∫ ω, weightedSum K Y n ω ^ 2 ∂P := by
    have hexp : (fun ω => partialSum Y n ω ^ 2) = fun ω =>
        (weightedSum H Y n ω ^ 2 + weightedSum K Y n ω ^ 2) +
          2 * (weightedSum H Y n ω * weightedSum K Y n ω) := by
      funext ω; rw [hsplit]; ring
    rw [hexp, integral_add
      (f := fun ω => weightedSum H Y n ω ^ 2 + weightedSum K Y n ω ^ 2)
      (g := fun ω => 2 * (weightedSum H Y n ω * weightedSum K Y n ω))
      (hA2.integrable_sq.add hB2.integrable_sq) ((hA2.integrable_mul hB2).const_mul 2),
      integral_const_mul, horth,
      integral_add (f := fun ω => weightedSum H Y n ω ^ 2)
        (g := fun ω => weightedSum K Y n ω ^ 2) hA2.integrable_sq hB2.integrable_sq]
    ring
  -- on the exceedance event the `H`-part equals the stopped partial sum
  have hpt : ∀ ω, (∃ k ≤ n, lam ≤ |partialSum Y k ω|) →
      lam ^ 2 ≤ weightedSum H Y n ω ^ 2 := by
    intro ω hω
    classical
    let k := Nat.find hω
    have hk : k ≤ n ∧ lam ≤ |partialSum Y k ω| := Nat.find_spec hω
    have hmin : ∀ j < k, |partialSum Y j ω| < lam := by
      intro j hj
      by_contra hc
      exact Nat.find_min hω hj ⟨by omega, not_lt.mp hc⟩
    have hHt : ∀ t < n, H t ω = if t < k then 1 else 0 := by
      intro t _
      simp only [hHdef, belowWeight]
      by_cases htk : t < k
      · rw [if_pos (fun j hj => hmin j (by omega)), if_pos htk]
      · rw [if_neg htk, if_neg]
        intro hall
        exact absurd (hall k (by omega)) (not_lt.mpr hk.2)
    have hsum : weightedSum H Y n ω = partialSum Y k ω := by
      simp only [weightedSum, partialSum]
      rw [Finset.sum_congr rfl fun t ht => by rw [hHt t (Finset.mem_range.1 ht)]]
      rw [← Finset.sum_range_add_sum_Ico _ hk.1]
      have h2 : ∑ t ∈ Finset.Ico k n, (if t < k then (1 : ℝ) else 0) * Y t ω = 0 :=
        Finset.sum_eq_zero fun t ht => by
          rw [if_neg (not_lt.mpr (Finset.mem_Ico.1 ht).1)]; ring
      rw [h2, add_zero]
      exact Finset.sum_congr rfl fun t ht => by
        rw [if_pos (Finset.mem_range.1 ht)]; ring
    rw [hsum]
    have := hk.2
    have h0 : 0 ≤ lam := hlam.le
    nlinarith [abs_nonneg (partialSum Y k ω), sq_abs (partialSum Y k ω)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg (weightedSum H Y n ω))
    hA2.integrable_sq (lam ^ 2)
  calc lam ^ 2 * P.real {ω | ∃ k ≤ n, lam ≤ |partialSum Y k ω|}
      ≤ lam ^ 2 * P.real {ω | lam ^ 2 ≤ weightedSum H Y n ω ^ 2} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono (fun ω hω => hpt ω hω))
          (sq_nonneg lam)
    _ ≤ ∫ ω, weightedSum H Y n ω ^ 2 ∂P := hmark
    _ ≤ ∫ ω, partialSum Y n ω ^ 2 ∂P := by
        rw [hSn]
        have : 0 ≤ ∫ ω, weightedSum K Y n ω ^ 2 ∂P :=
          integral_nonneg fun ω => sq_nonneg _
        linarith

/-! ## Third moments -/

private theorem abs_add_pow_three_le_of_nonneg {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    |a + b| ^ 3 ≤ |a| ^ 3 + 3 * (a * |a|) * b + 3 * |a| * b ^ 2 + |b| ^ 3 := by
  rw [abs_of_nonneg ha]
  rcases le_total 0 (a + b) with hab | hab
  · rw [abs_of_nonneg hab]
    have hb3 : b ^ 3 ≤ |b| ^ 3 := by
      rcases le_total 0 b with hb | hb
      · rw [abs_of_nonneg hb]
      · rw [abs_of_nonpos hb]; nlinarith [sq_nonneg b]
    nlinarith
  · have hb : b ≤ 0 := by linarith
    rw [abs_of_nonpos hab, abs_of_nonpos hb]
    have hq : 0 ≤ a * (a ^ 2 + 3 * a * b + 3 * b ^ 2) :=
      mul_nonneg ha (by nlinarith [sq_nonneg (2 * a + 3 * b), sq_nonneg b])
    nlinarith

/-- Taylor's formula for `|x|^3` with an explicit remainder bound. -/
theorem abs_add_pow_three_le (a b : ℝ) :
    |a + b| ^ 3 ≤ |a| ^ 3 + 3 * (a * |a|) * b + 3 * |a| * b ^ 2 + |b| ^ 3 := by
  rcases le_total 0 a with ha | ha
  · exact abs_add_pow_three_le_of_nonneg ha b
  · have := abs_add_pow_three_le_of_nonneg (neg_nonneg.2 ha) (-b)
    rw [← neg_add, abs_neg, abs_neg, abs_neg] at this
    nlinarith

theorem memLp_three_integrable_abs_cube {Z : Ω → ℝ} (hZ : MemLp Z 3 P) :
    Integrable (fun ω => |Z ω| ^ 3) P := by
  have := hZ.integrable_norm_pow (p := 3) (by norm_num)
  simpa [Real.norm_eq_abs] using this

/-- One step of the third-moment recursion for predictably weighted sums. -/
theorem integral_abs_weightedSum_cube_succ_le [IsProbabilityMeasure P]
    (h : IndepIncrements P F Y) (hH : PredictableWeight F H)
    (hY3 : ∀ t, MemLp (Y t) 3 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) (n : ℕ) :
    ∫ ω, |weightedSum H Y (n + 1) ω| ^ 3 ∂P ≤
      ∫ ω, |weightedSum H Y n ω| ^ 3 ∂P +
        3 * (∫ ω, |weightedSum H Y n ω| * H n ω ^ 2 ∂P) * (∫ ω, Y n ω ^ 2 ∂P) +
        (∫ ω, |H n ω| ^ 3 ∂P) * ∫ ω, |Y n ω| ^ 3 ∂P := by
  set A := weightedSum H Y n with hA
  have hA3 : MemLp A 3 P := memLp_weightedSum h hH hY3 n
  have hAm : Measurable[F n] A := weightedSum_measurable_past h hH n
  have hAm' : Measurable A := hAm.mono (F.le n) le_rfl
  have hYm := h.measurable' n
  have hHm := hH.measurable' n
  have iA : Integrable (fun ω => |A ω| ^ 3) P := memLp_three_integrable_abs_cube hA3
  have iY : Integrable (fun ω => |Y n ω| ^ 3) P := memLp_three_integrable_abs_cube (hY3 n)
  have iN : Integrable (fun ω => |weightedSum H Y (n + 1) ω| ^ 3) P :=
    memLp_three_integrable_abs_cube (memLp_weightedSum h hH hY3 (n + 1))
  -- domination of the mixed terms by `|A|^3 + |Y|^3`
  have hHb := hH.abs_le_one n
  have i1 : Integrable (fun ω => (A ω * |A ω| * H n ω) * Y n ω) P := by
    refine (iA.add iY).mono' ((((hAm'.mul (continuous_abs.measurable.comp hAm')).mul hHm).mul hYm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    have hx := abs_nonneg (A ω); have hy := abs_nonneg (Y n ω)
    have hh := hHb ω; have hh0 := abs_nonneg (H n ω)
    rw [abs_mul, abs_mul, abs_mul, abs_abs]
    have hxy : |A ω| * |A ω| * |Y n ω| ≤ |A ω| ^ 3 + |Y n ω| ^ 3 := by
      nlinarith [sq_nonneg (|A ω| - |Y n ω|), mul_nonneg hx hy]
    calc |A ω| * |A ω| * |H n ω| * |Y n ω| ≤ |A ω| * |A ω| * 1 * |Y n ω| := by gcongr
      _ ≤ _ := by linarith
  have i2 : Integrable (fun ω => (|A ω| * H n ω ^ 2) * Y n ω ^ 2) P := by
    refine (iA.add iY).mono' ((((continuous_abs.measurable.comp hAm').mul (hHm.pow_const 2)).mul
      (hYm.pow_const 2)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    have hx := abs_nonneg (A ω); have hy := abs_nonneg (Y n ω)
    have hh := hHb ω
    have hH2 : H n ω ^ 2 ≤ 1 := by nlinarith [abs_nonneg (H n ω), sq_abs (H n ω)]
    rw [abs_mul, abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (H n ω)),
      abs_of_nonneg (sq_nonneg (Y n ω)), ← sq_abs (Y n ω)]
    have hxy : |A ω| * |Y n ω| ^ 2 ≤ |A ω| ^ 3 + |Y n ω| ^ 3 := by
      nlinarith [sq_nonneg (|A ω| - |Y n ω|), mul_nonneg hx hy]
    calc |A ω| * H n ω ^ 2 * |Y n ω| ^ 2 ≤ |A ω| * 1 * |Y n ω| ^ 2 := by gcongr
      _ ≤ _ := by linarith
  have i3 : Integrable (fun ω => |H n ω| ^ 3 * |Y n ω| ^ 3) P := by
    refine iY.bdd_mul ((continuous_abs.measurable.comp hHm).pow_const 3).aestronglyMeasurable (c := 1)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (abs_nonneg _) (hHb ω)
  have hpt : ∀ ω, |weightedSum H Y (n + 1) ω| ^ 3 ≤
      (|A ω| ^ 3 + 3 * ((A ω * |A ω| * H n ω) * Y n ω)) +
        3 * ((|A ω| * H n ω ^ 2) * Y n ω ^ 2) + |H n ω| ^ 3 * |Y n ω| ^ 3 := by
    intro ω
    rw [weightedSum_succ]
    have := abs_add_pow_three_le (A ω) (H n ω * Y n ω)
    rw [abs_mul, mul_pow] at this
    linarith [show 3 * (A ω * |A ω|) * (H n ω * Y n ω) = 3 * ((A ω * |A ω| * H n ω) * Y n ω)
      by ring, show 3 * |A ω| * (H n ω * Y n ω) ^ 2 = 3 * ((|A ω| * H n ω ^ 2) * Y n ω ^ 2)
      by ring]
  have hint := integral_mono (g := fun ω => (|A ω| ^ 3 + 3 * ((A ω * |A ω| * H n ω) * Y n ω)) +
        3 * ((|A ω| * H n ω ^ 2) * Y n ω ^ 2) + |H n ω| ^ 3 * |Y n ω| ^ 3)
    iN (((iA.add (i1.const_mul 3)).add (i2.const_mul 3)).add i3) hpt
  refine hint.trans (le_of_eq ?_)
  rw [integral_add (f := fun ω => (|A ω| ^ 3 + 3 * ((A ω * |A ω| * H n ω) * Y n ω)) +
        3 * ((|A ω| * H n ω ^ 2) * Y n ω ^ 2))
      (g := fun ω => |H n ω| ^ 3 * |Y n ω| ^ 3)
      ((iA.add (i1.const_mul 3)).add (i2.const_mul 3)) i3,
    integral_add (f := fun ω => |A ω| ^ 3 + 3 * ((A ω * |A ω| * H n ω) * Y n ω))
      (g := fun ω => 3 * ((|A ω| * H n ω ^ 2) * Y n ω ^ 2))
      (iA.add (i1.const_mul 3)) (i2.const_mul 3),
    integral_add (f := fun ω => |A ω| ^ 3) (g := fun ω => 3 * ((A ω * |A ω| * H n ω) * Y n ω))
      iA (i1.const_mul 3),
    integral_const_mul, integral_const_mul]
  have e1 : ∫ ω, (A ω * |A ω| * H n ω) * Y n ω ∂P = 0 := by
    rw [h.integral_mul_past n (Z := fun ω => A ω * |A ω| * H n ω)
      ((hAm.mul (continuous_abs.measurable.comp hAm)).mul (hH.measurable n)) hYm, hY0 n,
      mul_zero]
  have e2 : ∫ ω, (|A ω| * H n ω ^ 2) * Y n ω ^ 2 ∂P =
      (∫ ω, |A ω| * H n ω ^ 2 ∂P) * ∫ ω, Y n ω ^ 2 ∂P :=
    h.integral_mul_past_comp n (Z := fun ω => |A ω| * H n ω ^ 2)
      ((continuous_abs.measurable.comp hAm).mul ((hH.measurable n).pow_const 2))
      (φ := fun x => x ^ 2) (by fun_prop)
  have e3 : ∫ ω, |H n ω| ^ 3 * |Y n ω| ^ 3 ∂P =
      (∫ ω, |H n ω| ^ 3 ∂P) * ∫ ω, |Y n ω| ^ 3 ∂P :=
    h.integral_mul_past_comp n (Z := fun ω => |H n ω| ^ 3)
      ((continuous_abs.measurable.comp (hH.measurable n)).pow_const 3)
      (φ := fun x => |x| ^ 3) (by fun_prop)
  rw [e1, e2, e3]
  ring

/-- Summed third-moment bound for predictably weighted sums. -/
theorem integral_abs_weightedSum_cube_le [IsProbabilityMeasure P]
    (h : IndepIncrements P F Y) (hH : PredictableWeight F H)
    (hY3 : ∀ t, MemLp (Y t) 3 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σsq κ : ℝ}
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σsq) (hκ : ∀ t, ∫ ω, |Y t ω| ^ 3 ∂P ≤ κ) :
    ∀ n, ∫ ω, |weightedSum H Y n ω| ^ 3 ∂P ≤
      ∑ t ∈ range n, (3 * σsq * ∫ ω, |weightedSum H Y t ω| * H t ω ^ 2 ∂P +
        κ * ∫ ω, |H t ω| ^ 3 ∂P)
  | 0 => by simp
  | n + 1 => by
    have ih := integral_abs_weightedSum_cube_le h hH hY3 hY0 hσ hκ n
    have step := integral_abs_weightedSum_cube_succ_le h hH hY3 hY0 n
    have h1 : 0 ≤ ∫ ω, |weightedSum H Y n ω| * H n ω ^ 2 ∂P :=
      integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ ∫ ω, |H n ω| ^ 3 ∂P := integral_nonneg fun ω => by positivity
    have h3 : (∫ ω, |weightedSum H Y n ω| * H n ω ^ 2 ∂P) * (∫ ω, Y n ω ^ 2 ∂P) ≤
        (∫ ω, |weightedSum H Y n ω| * H n ω ^ 2 ∂P) * σsq :=
      mul_le_mul_of_nonneg_left (hσ n) h1
    have h4 : (∫ ω, |H n ω| ^ 3 ∂P) * (∫ ω, |Y n ω| ^ 3 ∂P) ≤ (∫ ω, |H n ω| ^ 3 ∂P) * κ :=
      mul_le_mul_of_nonneg_left (hκ n) h2
    rw [sum_range_succ]
    nlinarith

/-- `(E|X|)^2 ≤ E[X^2]` on a probability space. -/
theorem sq_integral_abs_le_integral_sq [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) : (∫ ω, |X ω| ∂P) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂P := by
  set c := ∫ ω, |X ω| ∂P
  have hX1 : Integrable (fun ω => |X ω|) P := (hX.integrable one_le_two).abs
  have hnn : 0 ≤ ∫ ω, (|X ω| - c) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hexp : (fun ω => (|X ω| - c) ^ 2) = fun ω => X ω ^ 2 + (-(2 * c) * |X ω| + c ^ 2) := by
    funext ω; rw [← sq_abs (X ω)]; ring
  rw [hexp, integral_add (f := fun ω => X ω ^ 2) (g := fun ω => -(2 * c) * |X ω| + c ^ 2)
    hX.integrable_sq ((hX1.const_mul _).add (integrable_const _)),
    integral_add (f := fun ω => -(2 * c) * |X ω|) (g := fun _ => c ^ 2) (hX1.const_mul _)
      (integrable_const _), integral_const_mul, integral_const] at hnn
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnn
  nlinarith

theorem integral_abs_le_sqrt_integral_sq [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) : ∫ ω, |X ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) :=
  Real.le_sqrt_of_sq_le (sq_integral_abs_le_integral_sq hX)

/-- `∑_{t<n} √t ≤ (2/3) n √n`. -/
theorem sum_sqrt_le (n : ℕ) :
    ∑ t ∈ range n, Real.sqrt t ≤ 2 / 3 * n * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb := Real.sqrt_nonneg ((n : ℝ) + 1)
    have ha2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hb2 : Real.sqrt ((n : ℝ) + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
    have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    push_cast
    nlinarith [mul_nonneg ha hb, mul_nonneg (sub_nonneg.2 hab) (add_nonneg ha hb),
      mul_nonneg (sub_nonneg.2 hab) ha, mul_nonneg (sub_nonneg.2 hab) hb]

/-- Rosenthal-type third-moment bound for sums with weights of modulus one. -/
theorem integral_abs_weightedSum_cube_le_of_unit [IsProbabilityMeasure P]
    (h : IndepIncrements P F Y) (hH : PredictableWeight F H) (hunit : ∀ t ω, |H t ω| = 1)
    (hY3 : ∀ t, MemLp (Y t) 3 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σ κ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σ ^ 2) (hκ : ∀ t, ∫ ω, |Y t ω| ^ 3 ∂P ≤ κ) (n : ℕ) :
    ∫ ω, |weightedSum H Y n ω| ^ 3 ∂P ≤ 2 * σ ^ 3 * n * Real.sqrt n + n * κ := by
  have hY2 : ∀ t, MemLp (Y t) 2 P := fun t => (hY3 t).mono_exponent (by norm_num)
  have hsq : ∀ t ω, H t ω ^ 2 = 1 := fun t ω => by rw [← sq_abs, hunit]; norm_num
  have hcube : ∀ t ω, |H t ω| ^ 3 = 1 := fun t ω => by rw [hunit]; norm_num
  have hbase := integral_abs_weightedSum_cube_le h hH hY3 hY0 hσ hκ n
  simp only [hsq, hcube, mul_one, integral_const, probReal_univ, smul_eq_mul]
    at hbase
  have hfirst : ∀ t, ∫ ω, |weightedSum H Y t ω| ∂P ≤ σ * Real.sqrt t := by
    intro t
    refine (integral_abs_le_sqrt_integral_sq (memLp_weightedSum h hH hY2 t)).trans ?_
    rw [integral_weightedSum_sq h hH hY2 hY0 t]
    simp only [hsq, integral_const, probReal_univ, smul_eq_mul, one_mul]
    calc Real.sqrt (∑ x ∈ range t, ∫ ω, Y x ω ^ 2 ∂P) ≤ Real.sqrt (t * σ ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc ∑ x ∈ range t, ∫ ω, Y x ω ^ 2 ∂P ≤ ∑ _x ∈ range t, σ ^ 2 :=
                sum_le_sum fun x _ => hσ x
            _ = t * σ ^ 2 := by simp
      _ = σ * Real.sqrt t := by
          rw [Real.sqrt_mul (Nat.cast_nonneg t), Real.sqrt_sq hσ0, mul_comm]
  calc ∫ ω, |weightedSum H Y n ω| ^ 3 ∂P
      ≤ ∑ t ∈ range n, (3 * σ ^ 2 * ∫ ω, |weightedSum H Y t ω| ∂P + κ) := hbase
    _ ≤ ∑ t ∈ range n, (3 * σ ^ 2 * (σ * Real.sqrt t) + κ) := by
        refine sum_le_sum fun t _ => ?_
        have := hfirst t
        have : 0 ≤ 3 * σ ^ 2 := by positivity
        nlinarith
    _ = 3 * σ ^ 3 * ∑ t ∈ range n, Real.sqrt t + n * κ := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
        congr 1
        exact sum_congr rfl fun t _ => by ring
    _ ≤ 2 * σ ^ 3 * n * Real.sqrt n + n * κ := by
        have := sum_sqrt_le n
        have : 0 ≤ σ ^ 3 := by positivity
        nlinarith

end PGM
