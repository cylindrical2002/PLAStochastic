import PLAStochastic.Index.Model.IIDGaps
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GoodEventSplit
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform concentration of partial sums of iid `Exp(1)` variables

Let `E` be an iid real sequence (`IIDSeq P E`) whose first term has law `expMeasure 1`, and
let `expSum E a b = E a + ⋯ + E (b - 1)` be the sum of `m = b - a` consecutive terms.

* `mgf_of_hasLaw_expMeasure`, `mgf_expSum`: `E[exp(θ E i)] = (1 - θ)⁻¹` and
  `E[exp(θ Γ)] = (1 - θ)⁻¹ ^ (b - a)` for `θ < 1`, computed from the density `e^{-x}` on `[0, ∞)`.
* `expSum_upper_tail`, `expSum_lower_tail`: for `a < b` and `x ≥ 0`,
  `P(Γ ≥ m + x) ≤ exp(-x² / (4 (m + x)))` and `P(Γ ≤ m - x) ≤ exp(-x² / (4 m))`
  (Chernoff with `θ = x / (2 (m + x))`, resp. `-x / (2 m)`, and
  `(1 - θ)⁻¹ ≤ exp(θ + θ²)` for `0 ≤ θ ≤ 1/2`, `(1 + θ)⁻¹ ≤ exp(-θ + θ²)` for `θ ≥ 0`).
* `expGood E N`: every `Γ a b` with `a < b ≤ 2N` satisfies
  `|Γ a b - m| ≤ 16 (√(m log N) + log N)`; `measureReal_compl_expGood_le` gives
  `P(expGood E N)ᶜ ≤ 18 / N²` for `N ≥ 1` (each pair fails with probability `≤ 2 / N⁴`,
  union over `(2N + 1)²` pairs).
* Deterministic consequences on `expGood E N` for `a ≤ b ≤ 2N`:
  `Γ a b ≤ 2 m + 80 log N` (`expSum_le_of_mem_expGood`),
  `Γ a b ≥ m / 2 - 144 log N` (`expSum_ge_of_mem_expGood`), and
  `Γ 0 N ≥ N / 2` when `1088 log N ≤ N`, in particular for `N ≥ 160000`
  (`half_le_expSum_zero_of_mem_expGood`, `half_le_expSum_zero_of_mem_expGood_of_ge`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace PGM

/-! ## The moment generating function of `Exp(1)` -/

theorem gammaPDFReal_one_one_mul_exp (θ x : ℝ) :
    gammaPDFReal 1 1 x * exp (θ * x) =
      (Set.Ici 0).indicator (fun x => exp ((θ - 1) * x)) x := by
  unfold gammaPDFReal
  split_ifs with hx
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 hx)]
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one,
      one_mul]
    rw [← Real.exp_add]
    ring_nf
  · rw [Set.indicator_of_notMem (by simpa using hx), zero_mul]

theorem toReal_gammaPDF_smul_exp (θ : ℝ) :
    (fun x => (gammaPDF 1 1 x).toReal • exp (θ * x)) =
      (Set.Ici 0).indicator (fun x => exp ((θ - 1) * x)) := by
  funext x
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos one_pos x), smul_eq_mul,
    gammaPDFReal_one_one_mul_exp]

theorem integrable_exp_mul_expMeasure {θ : ℝ} (hθ : θ < 1) :
    Integrable (fun x => exp (θ * x)) (expMeasure 1) := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul' hf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top), toReal_gammaPDF_smul_exp,
    integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

theorem integral_exp_mul_expMeasure {θ : ℝ} (hθ : θ < 1) :
    ∫ x, exp (θ * x) ∂(expMeasure 1) = (1 - θ)⁻¹ := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top), toReal_gammaPDF_smul_exp,
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [show θ - 1 = -(1 - θ) by ring, div_neg, neg_div, neg_neg, one_div]

/-! ## Partial sums of an iid `Exp(1)` sequence -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℕ → Ω → ℝ}

/-- Every term of an iid sequence has the law of its first term. -/
theorem IIDSeq.hasLaw_expMeasure (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P)
    (i : ℕ) : HasLaw (E i) (expMeasure 1) P :=
  ⟨(hE.measurable i).aemeasurable, (hE.ident i).map_eq.trans hlaw.map_eq⟩

theorem integrable_exp_mul_of_hasLaw {X : Ω → ℝ} (hX : HasLaw X (expMeasure 1) P) {θ : ℝ}
    (hθ : θ < 1) : Integrable (fun ω => exp (θ * X ω)) P := by
  have h := integrable_exp_mul_expMeasure hθ
  rw [← hX.map_eq] at h
  exact h.comp_aemeasurable hX.aemeasurable

/-- The moment generating function of `Exp(1)`: `E[exp(θ X)] = 1/(1-θ)` for `θ < 1`. -/
theorem mgf_of_hasLaw_expMeasure {X : Ω → ℝ} (hX : HasLaw X (expMeasure 1) P) {θ : ℝ}
    (hθ : θ < 1) : mgf X P θ = (1 - θ)⁻¹ := by
  rw [mgf, ← integral_exp_mul_expMeasure hθ]
  exact hX.integral_comp (f := fun x => exp (θ * x)) (by fun_prop)

/-- The sum `E a + ⋯ + E (b - 1)` of `b - a` consecutive terms. -/
def expSum (E : ℕ → Ω → ℝ) (a b : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.Ico a b, E i ω

omit [MeasurableSpace Ω] in
theorem expSum_eq_sum (E : ℕ → Ω → ℝ) (a b : ℕ) :
    expSum E a b = ∑ i ∈ Finset.Ico a b, E i := by
  funext ω
  simp [expSum, Finset.sum_apply]

/-- `E[exp(θ Γ)] = (1-θ)^{-(b-a)}` for `θ < 1`. -/
theorem mgf_expSum (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P) (a b : ℕ) {θ : ℝ}
    (hθ : θ < 1) : mgf (expSum E a b) P θ = (1 - θ)⁻¹ ^ (b - a) := by
  rw [expSum_eq_sum, hE.indep.mgf_sum hE.measurable,
    Finset.prod_congr rfl fun i _ => mgf_of_hasLaw_expMeasure (hE.hasLaw_expMeasure hlaw i) hθ,
    Finset.prod_const, Nat.card_Ico]

theorem integrable_exp_mul_expSum [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) (a b : ℕ) {θ : ℝ} (hθ : θ < 1) :
    Integrable (fun ω => exp (θ * expSum E a b ω)) P := by
  rw [expSum_eq_sum]
  exact hE.indep.integrable_exp_mul_sum hE.measurable
    fun i _ => integrable_exp_mul_of_hasLaw (hE.hasLaw_expMeasure hlaw i) hθ

/-! ## Elementary exponential inequalities -/

theorem inv_one_sub_le_exp {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    (1 - θ)⁻¹ ≤ exp (θ + θ ^ 2) := by
  rw [inv_le_iff_one_le_mul₀' (by linarith)]
  have hy : 0 ≤ θ + θ ^ 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have hpoly : (1 - θ) * (1 + (θ + θ ^ 2) + (θ + θ ^ 2) ^ 2 / 2) - 1 =
      θ ^ 2 / 2 * (1 - θ - θ ^ 2 - θ ^ 3) := by ring
  have hθ2 : θ ^ 2 ≤ 1 / 4 := by nlinarith
  have hθ3 : θ ^ 3 ≤ 1 / 8 := by nlinarith
  have hpos : 0 ≤ θ ^ 2 / 2 * (1 - θ - θ ^ 2 - θ ^ 3) :=
    mul_nonneg (by positivity) (by linarith)
  calc (1 : ℝ) ≤ (1 - θ) * (1 + (θ + θ ^ 2) + (θ + θ ^ 2) ^ 2 / 2) := by linarith
    _ ≤ (1 - θ) * exp (θ + θ ^ 2) := mul_le_mul_of_nonneg_left hq (by linarith)

theorem inv_one_add_le_exp {θ : ℝ} (h0 : 0 ≤ θ) : (1 + θ)⁻¹ ≤ exp (-θ + θ ^ 2) := by
  have hpos : 0 < 1 + θ := by linarith
  have h1 : (1 + θ)⁻¹ = -θ / (1 + θ) + 1 := by field_simp; ring
  have h2 : -θ / (1 + θ) ≤ -θ + θ ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [pow_nonneg h0 3]
  rw [h1]
  exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.2 h2)

/-! ## Chernoff bounds -/

/-- Upper tail: `P(Γ ≥ m + x) ≤ exp(-x²/(4(m + x)))` for `m = b - a ≥ 1`, `x ≥ 0`. -/
theorem expSum_upper_tail [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) {a b : ℕ} (hab : a < b) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ((b - a : ℕ) : ℝ) + x ≤ expSum E a b ω} ≤
      exp (-(x ^ 2 / (4 * (((b - a : ℕ) : ℝ) + x)))) := by
  set m : ℝ := ((b - a : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast (by omega : 1 ≤ b - a)
  have hs : 0 < m + x := by linarith
  set θ := x / (2 * (m + x)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_iff₀ (by positivity)]
    linarith
  have hθlt : θ < 1 := by linarith
  refine (measure_ge_le_exp_mul_mgf (m + x) hθ0
    (integrable_exp_mul_expSum hE hlaw a b hθlt)).trans ?_
  rw [mgf_expSum hE hlaw a b hθlt]
  have hinv : 0 ≤ (1 - θ)⁻¹ := inv_nonneg.2 (by linarith)
  calc exp (-θ * (m + x)) * (1 - θ)⁻¹ ^ (b - a)
      ≤ exp (-θ * (m + x)) * exp (θ + θ ^ 2) ^ (b - a) := by
        gcongr
        exact inv_one_sub_le_exp hθ0 hθ1
    _ = exp (-θ * x + m * θ ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← hm]
        congr 1
        ring
    _ ≤ exp (-(x ^ 2 / (4 * (m + x)))) := by
        apply Real.exp_le_exp.2
        have key : -θ * x + m * θ ^ 2 =
            -(x ^ 2 / (4 * (m + x))) - x ^ 3 / (4 * (m + x) ^ 2) := by
          rw [hθ]
          field_simp
          ring
        rw [key]
        have : 0 ≤ x ^ 3 / (4 * (m + x) ^ 2) := by positivity
        linarith

/-- Lower tail: `P(Γ ≤ m - x) ≤ exp(-x²/(4m))` for `m = b - a ≥ 1`, `x ≥ 0`. -/
theorem expSum_lower_tail [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) {a b : ℕ} (hab : a < b) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | expSum E a b ω ≤ ((b - a : ℕ) : ℝ) - x} ≤
      exp (-(x ^ 2 / (4 * ((b - a : ℕ) : ℝ)))) := by
  set m : ℝ := ((b - a : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast (by omega : 1 ≤ b - a)
  have hm0 : 0 < m := by linarith
  set θ := x / (2 * m) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hlt : -θ < 1 := by linarith
  refine (measure_le_le_exp_mul_mgf (m - x) (by linarith : -θ ≤ 0)
    (integrable_exp_mul_expSum hE hlaw a b hlt)).trans ?_
  rw [mgf_expSum hE hlaw a b hlt, sub_neg_eq_add]
  have hinv : 0 ≤ (1 + θ)⁻¹ := inv_nonneg.2 (by linarith)
  calc exp (-(-θ) * (m - x)) * (1 + θ)⁻¹ ^ (b - a)
      ≤ exp (-(-θ) * (m - x)) * exp (-θ + θ ^ 2) ^ (b - a) := by
        gcongr
        exact inv_one_add_le_exp hθ0
    _ = exp (-θ * x + m * θ ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← hm]
        congr 1
        ring
    _ = exp (-(x ^ 2 / (4 * m))) := by
        congr 1
        rw [hθ]
        field_simp
        ring

/-! ## The uniform good event -/

/-- On `expGood E N`, every block sum `Γ a b` with `a < b ≤ 2N` is within
`16 (√(m log N) + log N)` of its mean `m = b - a`. -/
def expGood (E : ℕ → Ω → ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ a b : ℕ, a < b → b ≤ 2 * N →
    |expSum E a b ω - ((b - a : ℕ) : ℝ)| ≤
      16 * (Real.sqrt (((b - a : ℕ) : ℝ) * Real.log N) + Real.log N)}

theorem exp_neg_four_mul_log {N : ℕ} (hN : 1 ≤ N) :
    exp (-(4 * Real.log N)) = 1 / (N : ℝ) ^ 4 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.exp_neg, show (4 : ℝ) * Real.log N = ((4 : ℕ) : ℝ) * Real.log N by norm_num,
    Real.exp_nat_mul, Real.exp_log hpos, one_div]

theorem four_mul_le_upper_exponent {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L) :
    4 * L ≤ (16 * (√(m * L) + L)) ^ 2 / (4 * (m + 16 * (√(m * L) + L))) := by
  have hr := Real.sqrt_nonneg (m * L)
  have hr2 := Real.sq_sqrt (mul_nonneg hm.le hL)
  set r := √(m * L)
  rw [le_div_iff₀ (by positivity)]
  have key : (16 * (r + L)) ^ 2 - 4 * L * (4 * (m + 16 * (r + L))) =
      240 * r ^ 2 + 256 * (r * L) := by
    linear_combination 16 * hr2
  have : 0 ≤ 240 * r ^ 2 + 256 * (r * L) := by positivity
  linarith

theorem four_mul_le_lower_exponent {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L) :
    4 * L ≤ (16 * (√(m * L) + L)) ^ 2 / (4 * m) := by
  have hr := Real.sqrt_nonneg (m * L)
  have hr2 := Real.sq_sqrt (mul_nonneg hm.le hL)
  set r := √(m * L)
  rw [le_div_iff₀ (by positivity)]
  have key : (16 * (r + L)) ^ 2 - 4 * L * (4 * m) =
      240 * r ^ 2 + 512 * (r * L) + 256 * L ^ 2 := by
    linear_combination 16 * hr2
  have : 0 ≤ 240 * r ^ 2 + 512 * (r * L) + 256 * L ^ 2 := by positivity
  linarith

/-- One pair `(a, b)` violates the good event with probability at most `2 / N⁴`. -/
theorem measureReal_expBad_le [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) {N : ℕ} (hN : 1 ≤ N) (a b : ℕ) :
    P.real {ω | a < b ∧
      (((b - a : ℕ) : ℝ) + 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N) ≤
          expSum E a b ω ∨
        expSum E a b ω ≤
          ((b - a : ℕ) : ℝ) - 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N))} ≤
      2 / (N : ℝ) ^ 4 := by
  by_cases hab : a < b
  · have hm0 : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < b - a)
    have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hx0 : 0 ≤ 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N) := by positivity
    calc _ ≤ P.real ({ω | ((b - a : ℕ) : ℝ) +
            16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N) ≤ expSum E a b ω} ∪
          {ω | expSum E a b ω ≤
            ((b - a : ℕ) : ℝ) - 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N)}) :=
          measureReal_mono fun ω h => h.2
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ exp (-(4 * Real.log N)) + exp (-(4 * Real.log N)) := by
          refine add_le_add ((expSum_upper_tail hE hlaw hab hx0).trans ?_)
            ((expSum_lower_tail hE hlaw hab hx0).trans ?_)
          · exact Real.exp_le_exp.2 (neg_le_neg (four_mul_le_upper_exponent hm0 hL))
          · exact Real.exp_le_exp.2 (neg_le_neg (four_mul_le_lower_exponent hm0 hL))
      _ = 2 / (N : ℝ) ^ 4 := by
          rw [exp_neg_four_mul_log hN]
          ring
  · have hempty : {ω | a < b ∧
        (((b - a : ℕ) : ℝ) + 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N) ≤
            expSum E a b ω ∨
          expSum E a b ω ≤
            ((b - a : ℕ) : ℝ) - 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N))} = ∅ := by
      ext ω
      simp [hab]
    rw [hempty, measureReal_empty]
    positivity

/-- The good event fails with probability at most `18 / N²`. -/
theorem measureReal_compl_expGood_le [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) {N : ℕ} (hN : 1 ≤ N) :
    P.real (expGood E N)ᶜ ≤ 18 / (N : ℝ) ^ 2 := by
  let bad : ℕ → ℕ → Set Ω := fun a b => {ω | a < b ∧
      (((b - a : ℕ) : ℝ) + 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N) ≤
          expSum E a b ω ∨
        expSum E a b ω ≤
          ((b - a : ℕ) : ℝ) - 16 * (√(((b - a : ℕ) : ℝ) * Real.log N) + Real.log N))}
  have hsub : (expGood E N)ᶜ ⊆
      ⋃ a ∈ Finset.range (2 * N + 1), ⋃ b ∈ Finset.range (2 * N + 1), bad a b := by
    intro ω hω
    simp only [expGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨a, b, hab, hb, hlt⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨a, by omega, b, by omega, hab, ?_⟩
    rcases lt_abs.1 hlt with h | h
    · left
      linarith
    · right
      linarith
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h9 : ((2 * N + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc P.real (expGood E N)ᶜ ≤ P.real
        (⋃ a ∈ Finset.range (2 * N + 1), ⋃ b ∈ Finset.range (2 * N + 1), bad a b) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) ^ 2 * (2 / (N : ℝ) ^ 4) :=
        measureReal_biUnion_pairs_le N bad fun a b _ _ => measureReal_expBad_le hE hlaw hN a b
    _ ≤ 9 * (N : ℝ) ^ 2 * (2 / (N : ℝ) ^ 4) := by gcongr
    _ = 18 / (N : ℝ) ^ 2 := by
        field_simp
        ring

/-! ## Deterministic consequences of the good event -/

theorem sixteen_mul_sqrt_mul_le {m L c d : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) (hc : 0 < c)
    (hcd : c * d = 64) : 16 * √(m * L) ≤ c * m + d * L := by
  have hd : d = 64 / c := by rw [← hcd]; field_simp
  rw [hd, Real.sqrt_mul hm]
  have hu := Real.sq_sqrt hm
  have hv := Real.sq_sqrt hL
  set u := √m
  set v := √L
  rw [← hu, ← hv]
  have key : c * u ^ 2 + 64 / c * v ^ 2 - 16 * (u * v) = (c * u - 8 * v) ^ 2 / c := by
    field_simp
    ring
  have : 0 ≤ (c * u - 8 * v) ^ 2 / c := by positivity
  linarith

omit [MeasurableSpace Ω] in
/-- On the good event, `Γ a b ≤ 2 (b - a) + 80 log N` for all `a ≤ b ≤ 2N`. -/
theorem expSum_le_of_mem_expGood {N : ℕ} {ω : Ω} (hω : ω ∈ expGood E N) (hN : 1 ≤ N)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 2 * N) :
    expSum E a b ω ≤ 2 * ((b - a : ℕ) : ℝ) + 80 * Real.log N := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [expSum, Finset.Ico_self, Finset.sum_empty, Nat.sub_self, Nat.cast_zero, mul_zero,
      zero_add]
    positivity
  · have h := (abs_le.1 (hω a b hlt hb)).2
    have hs := sixteen_mul_sqrt_mul_le (Nat.cast_nonneg (b - a)) hL one_pos (d := 64)
      (by norm_num)
    linarith

omit [MeasurableSpace Ω] in
/-- On the good event, `Γ a b ≥ (b - a) / 2 - 144 log N` for all `a ≤ b ≤ 2N`. -/
theorem expSum_ge_of_mem_expGood {N : ℕ} {ω : Ω} (hω : ω ∈ expGood E N) (hN : 1 ≤ N)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 2 * N) :
    ((b - a : ℕ) : ℝ) / 2 - 144 * Real.log N ≤ expSum E a b ω := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [expSum, Finset.Ico_self, Finset.sum_empty, Nat.sub_self, Nat.cast_zero, zero_div,
      zero_sub, neg_nonpos]
    positivity
  · have h := (abs_le.1 (hω a b hlt hb)).1
    have hs := sixteen_mul_sqrt_mul_le (Nat.cast_nonneg (b - a)) hL
      (by norm_num : (0 : ℝ) < 1 / 2) (d := 128) (by norm_num)
    linarith

omit [MeasurableSpace Ω] in
/-- On the good event, `Γ 0 N ≥ N / 2` as soon as `1088 log N ≤ N`. -/
theorem half_le_expSum_zero_of_mem_expGood {N : ℕ} {ω : Ω} (hω : ω ∈ expGood E N)
    (hN : 1 ≤ N) (hlog : 1088 * Real.log N ≤ N) : (N : ℝ) / 2 ≤ expSum E 0 N ω := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h := (abs_le.1 (hω 0 N (by omega) (by omega))).1
  simp only [Nat.sub_zero] at h
  have hs := sixteen_mul_sqrt_mul_le (Nat.cast_nonneg N) hL (by norm_num : (0 : ℝ) < 1 / 4)
    (d := 256) (by norm_num)
  linarith

/-- `1088 log N ≤ N` for `N ≥ 160000 = 20⁴`. -/
theorem mul_log_le_self_of_ge {N : ℕ} (hN : 160000 ≤ N) : 1088 * Real.log N ≤ N := by
  have hN' : (160000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h400 : (400 : ℝ) ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  set s := √(√(N : ℝ)) with hs
  have hs2 : s ^ 2 = √(N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = N := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hN0]
  have h20 : (20 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hspos : 0 < s := by linarith
  have hlog : Real.log N = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]
    norm_num
  have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have h3 : (20 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) h20 3
  have h4 : s * 20 ^ 3 ≤ s * s ^ 3 := mul_le_mul_of_nonneg_left h3 hspos.le
  rw [hlog, ← hs4]
  nlinarith

omit [MeasurableSpace Ω] in
/-- On the good event, `Γ 0 N ≥ N / 2` for `N ≥ 160000`. -/
theorem half_le_expSum_zero_of_mem_expGood_of_ge {N : ℕ} {ω : Ω} (hω : ω ∈ expGood E N)
    (hN : 160000 ≤ N) : (N : ℝ) / 2 ≤ expSum E 0 N ω :=
  half_le_expSum_zero_of_mem_expGood hω (by omega) (mul_log_le_self_of_ge hN)

end PGM
