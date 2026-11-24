import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Paley–Zygmund and moment anti-concentration

Cauchy–Schwarz-based lower bounds on tail probabilities from second and third
moments.
-/

namespace PGM

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Cauchy–Schwarz for real `L²` functions, via the discriminant of a nonnegative quadratic. -/
private lemma pz_cauchy_schwarz {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * (∫ ω, g ω ^ 2 ∂P) := by
  have hf2 := hf.integrable_sq
  have hg2 := hg.integrable_sq
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have key : ∀ x : ℝ, 0 ≤ (∫ ω, g ω ^ 2 ∂P) * (x * x) + (2 * ∫ ω, f ω * g ω ∂P) * x
      + ∫ ω, f ω ^ 2 ∂P := by
    intro x
    have h1 : ∫ ω, (x * g ω + f ω) ^ 2 ∂P = (∫ ω, g ω ^ 2 ∂P) * (x * x)
        + (2 * ∫ ω, f ω * g ω ∂P) * x + ∫ ω, f ω ^ 2 ∂P := by
      have : (fun ω => (x * g ω + f ω) ^ 2)
          = fun ω => (x * x) * g ω ^ 2 + (2 * x) * (f ω * g ω) + f ω ^ 2 := by
        ext ω; ring
      rw [this, integral_add, integral_add, integral_const_mul, integral_const_mul]
      · ring
      · exact hg2.const_mul _
      · exact hfg.const_mul _
      · exact (hg2.const_mul _).add (hfg.const_mul _)
      · exact hf2
    rw [← h1]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

variable [IsProbabilityMeasure P]

/-- **Paley–Zygmund inequality.** For a nonnegative square-integrable `W` and `0 ≤ θ ≤ 1`,
`(1 - θ)² (E W)² ≤ E[W²] · P(W > θ E W)`. -/
theorem paley_zygmund {W : Ω → ℝ} (hWm : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hW2 : MemLp W 2 P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, W ω ∂P) ^ 2 ≤
      (∫ ω, W ω ^ 2 ∂P) * P.real {ω | θ * ∫ ω, W ω ∂P < W ω} := by
  set μ := ∫ ω, W ω ∂P with hμ
  set S := {ω | θ * μ < W ω} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hWm
  have hμ0 : 0 ≤ μ := integral_nonneg hW0
  have hW1 : Integrable W P := hW2.integrable one_le_two
  have hg2 : MemLp (S.indicator 1) 2 P := (memLp_const (1 : ℝ)).indicator hSm
  have hfg : ∀ ω, W ω * S.indicator 1 ω = S.indicator W ω := by
    intro ω; by_cases h : ω ∈ S <;> simp [h]
  have hgg : ∀ ω, S.indicator (1 : Ω → ℝ) ω ^ 2 = S.indicator 1 ω := by
    intro ω; by_cases h : ω ∈ S <;> simp [h]
  have hpt : ∀ ω, W ω ≤ θ * μ + S.indicator W ω := by
    intro ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h]
      nlinarith [mul_nonneg hθ0 hμ0]
    · rw [Set.indicator_of_notMem h, add_zero]
      exact not_lt.mp h
  have hmean : (1 - θ) * μ ≤ ∫ ω, S.indicator W ω ∂P := by
    have hi : ∫ ω, (θ * μ + S.indicator W ω) ∂P = θ * μ + ∫ ω, S.indicator W ω ∂P := by
      rw [integral_add (integrable_const _) (hW1.indicator hSm), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    have := integral_mono (f := W) (g := fun ω => θ * μ + S.indicator W ω) hW1
      ((integrable_const _).add (hW1.indicator hSm)) hpt
    rw [hi] at this
    linarith
  have hcs := pz_cauchy_schwarz hW2 hg2
  simp_rw [hfg, hgg] at hcs
  rw [integral_indicator_one hSm] at hcs
  have h1 : 0 ≤ (1 - θ) * μ := mul_nonneg (by linarith) hμ0
  calc (1 - θ) ^ 2 * μ ^ 2 = ((1 - θ) * μ) ^ 2 := by ring
    _ ≤ (∫ ω, S.indicator W ω ∂P) ^ 2 := pow_le_pow_left₀ h1 hmean 2
    _ ≤ _ := hcs

/-- Second moment squared is at most first times third absolute moment:
`(E M²)² ≤ E|M| · E|M|³` (Cauchy–Schwarz with `|M|² = |M|^{1/2} |M|^{3/2}`). -/
theorem sq_integral_sq_le {M : Ω → ℝ} (hMm : Measurable M) (hM3 : MemLp M 3 P) :
    (∫ ω, M ω ^ 2 ∂P) ^ 2 ≤ (∫ ω, |M ω| ∂P) * (∫ ω, |M ω| ^ 3 ∂P) := by
  have h1 : Integrable (fun ω => |M ω|) P := (hM3.integrable (by norm_num)).abs
  have h3 : Integrable (fun ω => |M ω| ^ 3) P := by
    have := hM3.integrable_norm_pow (p := 3) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  set f : Ω → ℝ := fun ω => Real.sqrt |M ω| with hf
  set g : Ω → ℝ := fun ω => |M ω| * Real.sqrt |M ω| with hg
  have hMa : Measurable (fun ω => |M ω|) := continuous_abs.measurable.comp hMm
  have hfm : Measurable f := Real.continuous_sqrt.measurable.comp hMa
  have hgm : Measurable g := hMa.mul hfm
  have hff : ∀ ω, f ω ^ 2 = |M ω| := fun ω => Real.sq_sqrt (abs_nonneg _)
  have hgg : ∀ ω, g ω ^ 2 = |M ω| ^ 3 := by
    intro ω
    simp only [g, mul_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  have hfg : ∀ ω, f ω * g ω = M ω ^ 2 := by
    intro ω
    have := Real.mul_self_sqrt (abs_nonneg (M ω))
    rw [← sq_abs]
    simp only [f, g]
    linear_combination |M ω| * this
  have hf2 : MemLp f 2 P :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 (by simp_rw [hff]; exact h1)
  have hg2 : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 (by simp_rw [hgg]; exact h3)
  have := pz_cauchy_schwarz hf2 hg2
  simp_rw [hfg, hff, hgg] at this
  exact this

omit [IsProbabilityMeasure P] in
/-- From `s² ≤ a`, `a² ≤ b c` and `c ≤ 3 s³` we get `s / 3 ≤ b`. -/
private lemma pz_mean_lower {s a b c : ℝ} (hs : 0 < s) (h2 : s ^ 2 ≤ a) (hab : a ^ 2 ≤ b * c)
    (h3 : c ≤ 3 * s ^ 3) (hb : 0 ≤ b) : s / 3 ≤ b := by
  have hs2 : 0 ≤ s ^ 2 := by positivity
  have ha2 : s ^ 4 ≤ a ^ 2 := by
    have := pow_le_pow_left₀ hs2 h2 2
    nlinarith
  have hbc : b * c ≤ b * (3 * s ^ 3) := mul_le_mul_of_nonneg_left h3 hb
  have hs3 : 0 < s ^ 3 := by positivity
  nlinarith

omit [IsProbabilityMeasure P] in
/-- The arithmetic core of the anti-concentration bounds. -/
private lemma pz_arith {s a b c p : ℝ} (hs : 0 < s) (h2 : s ^ 2 ≤ a) (hab : a ^ 2 ≤ b * c)
    (h3 : c ≤ 3 * s ^ 3) (hb : 0 ≤ b) (hp : b ^ 2 / 4 ≤ a * p) : 1 / 36 ≤ p := by
  have hs2 : 0 < s ^ 2 := by positivity
  have ha : 0 < a := lt_of_lt_of_le hs2 h2
  have hbc : b * c ≤ b * (3 * s ^ 3) := mul_le_mul_of_nonneg_left h3 hb
  have hA : a ^ 2 ≤ 3 * s ^ 3 * b := by nlinarith
  have hA2 : (a ^ 2) ^ 2 ≤ (3 * s ^ 3 * b) ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
  have hs6 : 0 < s ^ 6 := by positivity
  have hB : (a ^ 2) ^ 2 ≤ 36 * s ^ 6 * (a * p) := by
    have : (3 * s ^ 3 * b) ^ 2 = 36 * s ^ 6 * (b ^ 2 / 4) := by ring
    rw [this] at hA2
    exact hA2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hC : a ^ 3 ≤ 36 * s ^ 6 * p := by
    have h : a * a ^ 3 ≤ a * (36 * s ^ 6 * p) := by
      calc a * a ^ 3 = (a ^ 2) ^ 2 := by ring
        _ ≤ 36 * s ^ 6 * (a * p) := hB
        _ = a * (36 * s ^ 6 * p) := by ring
    exact le_of_mul_le_mul_left h ha
  have hD : s ^ 6 ≤ a ^ 3 := by
    have := pow_le_pow_left₀ hs2.le h2 3
    calc s ^ 6 = (s ^ 2) ^ 3 := by ring
      _ ≤ a ^ 3 := this
  nlinarith

/-- **Anti-concentration from second and third moments.** If `s² ≤ E M²` and
`E|M|³ ≤ 3 s³`, then `P(|M| > s/6) ≥ 1/36`. -/
theorem anticoncentration_of_moments {s : ℝ} (hs : 0 < s) {M : Ω → ℝ} (hMm : Measurable M)
    (hM3 : MemLp M 3 P) (h2 : s ^ 2 ≤ ∫ ω, M ω ^ 2 ∂P)
    (h3 : ∫ ω, |M ω| ^ 3 ∂P ≤ 3 * s ^ 3) :
    1 / 36 ≤ P.real {ω | s / 6 < |M ω|} := by
  have hM2 : MemLp M 2 P := hM3.mono_exponent (by norm_num)
  have hab := sq_integral_sq_le hMm hM3
  have hb0 : 0 ≤ ∫ ω, |M ω| ∂P := integral_nonneg fun ω => abs_nonneg _
  have hbs := pz_mean_lower hs h2 hab h3 hb0
  have hMa : Measurable (fun ω => |M ω|) := continuous_abs.measurable.comp hMm
  have hpz := paley_zygmund (W := fun ω => |M ω|) hMa (fun ω => abs_nonneg _) hM2.abs
    (θ := 1 / 2) (by norm_num) (by norm_num)
  simp only [sq_abs] at hpz
  have hsub : {ω | 1 / 2 * ∫ ω, |M ω| ∂P < |M ω|} ⊆ {ω | s / 6 < |M ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  have hmono : P.real {ω | 1 / 2 * ∫ ω, |M ω| ∂P < |M ω|} ≤ P.real {ω | s / 6 < |M ω|} :=
    measureReal_mono hsub
  have ha0 : 0 ≤ ∫ ω, M ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  refine pz_arith hs h2 hab h3 hb0 ?_
  calc (∫ ω, |M ω| ∂P) ^ 2 / 4 = (1 - 1 / 2) ^ 2 * (∫ ω, |M ω| ∂P) ^ 2 := by ring
    _ ≤ _ := hpz
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono ha0

/-- The lower-tail half of `anticoncentration_sign_of_moments`. -/
private lemma pz_neg_side {s : ℝ} (hs : 0 < s) {M : Ω → ℝ} (hMm : Measurable M)
    (hM3 : MemLp M 3 P) (h2 : s ^ 2 ≤ ∫ ω, M ω ^ 2 ∂P)
    (h3 : ∫ ω, |M ω| ^ 3 ∂P ≤ 3 * s ^ 3) (h0 : ∫ ω, M ω ∂P = 0) :
    1 / 36 ≤ P.real {ω | M ω < 0} := by
  have hM2 : MemLp M 2 P := hM3.mono_exponent (by norm_num)
  have hM1 : Integrable M P := hM3.integrable (by norm_num)
  have hMa : Measurable (fun ω => |M ω|) := continuous_abs.measurable.comp hMm
  -- the negative part `M⁻ = (|M| - M) / 2`
  set W : Ω → ℝ := fun ω => 1 / 2 * (|M ω| - M ω) with hW
  have hWm : Measurable W := measurable_const.mul (hMa.sub hMm)
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by
    simp only [W]
    linarith [le_abs_self (M ω)]
  have hW2 : MemLp W 2 P := (hM2.abs.sub hM2).const_mul (1 / 2)
  have hWmean : ∫ ω, W ω ∂P = 1 / 2 * ∫ ω, |M ω| ∂P := by
    simp only [W]
    rw [integral_const_mul, integral_sub hM1.abs hM1, h0, sub_zero]
  have hWsq : ∫ ω, W ω ^ 2 ∂P ≤ ∫ ω, M ω ^ 2 ∂P := by
    refine integral_mono hW2.integrable_sq hM2.integrable_sq fun ω => ?_
    simp only [W]
    rcases le_or_gt 0 (M ω) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  have hset : {ω | 0 * ∫ ω, W ω ∂P < W ω} = {ω | M ω < 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, zero_mul, W]
    constructor
    · intro h
      by_contra hc
      rw [abs_of_nonneg (not_lt.mp hc)] at h
      simp at h
    · intro h
      rw [abs_of_neg h]
      linarith
  have hpz := paley_zygmund hWm hW0 hW2 le_rfl zero_le_one
  rw [hset, hWmean] at hpz
  have hab := sq_integral_sq_le hMm hM3
  have hb0 : 0 ≤ ∫ ω, |M ω| ∂P := integral_nonneg fun ω => abs_nonneg _
  have hp0 : 0 ≤ P.real {ω | M ω < 0} := measureReal_nonneg
  refine pz_arith hs h2 hab h3 hb0 ?_
  calc (∫ ω, |M ω| ∂P) ^ 2 / 4 = (1 - 0) ^ 2 * (1 / 2 * ∫ ω, |M ω| ∂P) ^ 2 := by ring
    _ ≤ _ := hpz
    _ ≤ _ := mul_le_mul_of_nonneg_right hWsq hp0

/-- **Two-sided anti-concentration for centred variables.** If moreover `E M = 0`, then each
sign occurs with probability at least `1/36`. -/
theorem anticoncentration_sign_of_moments {s : ℝ} (hs : 0 < s) {M : Ω → ℝ}
    (hMm : Measurable M) (hM3 : MemLp M 3 P) (h2 : s ^ 2 ≤ ∫ ω, M ω ^ 2 ∂P)
    (h3 : ∫ ω, |M ω| ^ 3 ∂P ≤ 3 * s ^ 3) (h0 : ∫ ω, M ω ∂P = 0) :
    1 / 36 ≤ P.real {ω | M ω < 0} ∧ 1 / 36 ≤ P.real {ω | 0 < M ω} := by
  refine ⟨pz_neg_side hs hMm hM3 h2 h3 h0, ?_⟩
  have h := pz_neg_side (M := fun ω => -M ω) hs hMm.neg hM3.neg
    (by simpa only [neg_sq] using h2) (by simpa only [abs_neg] using h3)
    (by rw [integral_neg, h0, neg_zero])
  simpa only [neg_lt_zero] using h

end PGM
