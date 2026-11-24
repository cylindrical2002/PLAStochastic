import PLAStochastic.Index.GEP.Additive.HeightOfLogSpan
import PLAStochastic.Index.Algorithm.EndpointTop
import PLAStochastic.ForMathlib.Probability.NatExpectation.TruncatedTail

/-!
# Actual endpoint height from layer counts and early-termination tails

This is the probability-to-height reduction of the KEP conditional assembly.
The layer sizes and height are those of the existing actual endpoint algorithm.
The hypotheses are explicit analytic inputs; this theorem does not claim that
the Model K bounds have already been supplied.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

/-- A sequence growing at least by a factor two has a bounded backward sum. -/
theorem kep_sum_span_le_twice_last {m : ℕ → ℝ}
    (hpos : ∀ j, 0 ≤ m j) (hstep : ∀ j, 2 * m j ≤ m (j + 1)) (L : ℕ) :
    ∑ j ∈ range (L + 1), m j ≤ 2 * m L := by
  induction L with
  | zero => simp only [zero_add, sum_range_one]; linarith [hpos 0]
  | succ L ih =>
    rw [sum_range_succ]
    linarith [hstep L]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Quantitative pointwise reduction, valid for every input size.

`A n / m L + D` is a layer-count upper bound. Below the cutoff `R m L < n`,
the early-termination probability is at most `K m L / n`. When `D` and `R`
grow polynomially in `eps`, the displayed error is bounded uniformly in `eps`
because `c` and `log q` are of order `log eps`.
-/
theorem integral_epHeight_additive_of_count_tail
    {eps : ℝ} (heps : 1 ≤ eps) {keys : Ω → ℕ → ℝ} (hkeys : Measurable keys)
    {n : ℕ} (hn : 2 ≤ n) {m : ℕ → ℝ}
    (hm0 : m 0 = 1) (hpos : ∀ j, 0 < m j)
    (hstep : ∀ j, 2 * m j ≤ m (j + 1))
    {c B A D R K : ℝ} (hc : 0 < c)
    (hlog : ∀ j : ℕ, |Real.log (m j) - j * c| ≤ B)
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hcount : ∀ L, (∫ ω, ((epLayer eps (keys ω) n L).2 : ℝ) ∂P) ≤
      A * (n : ℝ) / m L + D)
    (htail : ∀ L, R * m L < n →
      P.real {ω | epHeight eps (keys ω) n ≤ L} ≤ K * m L / n) :
    |(∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P) - Real.log n / c| ≤
      2 + B / c + Real.log (A + D) / Real.log (⌊2 * eps⌋₊ + 1) +
        Real.log R / c + 2 * K / R := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hRpos : 0 < R := by linarith
  have hAD : 1 ≤ A + D := by linarith
  have hB : 0 ≤ B := by simpa [hm0] using hlog 0
  have hqpos : 0 < Real.log (⌊2 * eps⌋₊ + 1) := by
    apply Real.log_pos
    exact_mod_cast one_lt_floor_add_one heps
  have hratio : ∀ j, (2 : ℝ) / 1 ≤ m (j + 1) / m j := by
    intro j
    rw [div_one, le_div_iff₀ (hpos j)]
    exact hstep j
  have hex : ∀ x : ℝ, ∃ j, x ≤ m j :=
    geometric_exists_ge (Γ := 2) (c := 1) (by norm_num) hm0 hratio
  have hInt : Integrable (fun ω => (epHeight eps (keys ω) n : ℝ)) P := by
    refine Integrable.of_bound
      (measurable_from_nat.comp (measurable_epHeight_comp eps n hkeys)).aestronglyMeasurable
      (Nat.log (⌊2 * eps⌋₊ + 1) n + 1) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_natCast]
    have hh : epHeight eps (keys ω) n ≤ Nat.log (⌊2 * eps⌋₊ + 1) n + 1 := by
      simpa only [epLayer, zero_add] using epHeight_le_add_log heps (keys ω) hn1 0
    exact_mod_cast hh
  have hEH0 : 0 ≤ ∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P :=
    integral_nonneg fun _ => Nat.cast_nonneg _
  have hupper : (∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P) - Real.log n / c ≤
      2 + B / c + Real.log (A + D) / Real.log (⌊2 * eps⌋₊ + 1) := by
    let J := firstPassage m n
    have hhit : (n : ℝ) ≤ m J := firstPassage_hit (hex n)
    have hcnt : (∫ ω, ((epLayer eps (keys ω) n J).2 : ℝ) ∂P) ≤ A + D := by
      have hdiv : A * (n : ℝ) / m J ≤ A := by
        rw [div_le_iff₀ (hpos J)]
        exact mul_le_mul_of_nonneg_left hhit (by linarith)
      linarith [hcount J]
    have hcntpos : 0 < ∫ ω, ((epLayer eps (keys ω) n J).2 : ℝ) ∂P := by
      have hint : Integrable (fun ω => ((epLayer eps (keys ω) n J).2 : ℝ)) P := by
        refine Integrable.of_bound
          (measurable_from_nat.comp (measurable_snd.comp
            ((measurable_epLayer eps n J).comp hkeys))).aestronglyMeasurable n
          (ae_of_all _ fun ω => ?_)
        rw [Real.norm_natCast]
        exact_mod_cast epLayer_snd_le heps (keys ω) n J
      have hh : (1 : ℝ) ≤ ∫ ω, ((epLayer eps (keys ω) n J).2 : ℝ) ∂P := by
        calc
          1 = ∫ _ : Ω, (1 : ℝ) ∂P := by simp
          _ ≤ _ := integral_mono (integrable_const _) hint
            (fun ω => by
              have hh : ((1 : ℕ) : ℝ) ≤ ((epLayer eps (keys ω) n J).2 : ℝ) :=
                Nat.cast_le.mpr (one_le_epLayer_snd (eps := eps) (keys ω) hn1 J)
              simpa only [Nat.cast_one] using hh)
      linarith
    have hheight := integral_epHeight_le (P := P) heps hkeys hn1 J
    have hclog := Real.log_le_log hcntpos hcnt
    have hdiv := div_le_div_of_nonneg_right hclog hqpos.le
    have hJ := (abs_le.mp (firstPassage_log_bound (x := (n : ℝ)) hm0 hpos hex hc hlog
      (by exact_mod_cast hn1))).2
    change (J : ℝ) - Real.log n / c ≤ 1 + B / c at hJ
    linarith
  have hlower : Real.log n / c - (∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P) ≤
      1 + B / c + Real.log R / c + 2 * K / R := by
    by_cases hRn : R ≤ (n : ℝ)
    · let x : ℝ := (n : ℝ) / R
      have hx : 1 ≤ x := (le_div_iff₀ hRpos).mpr (by simpa using hRn)
      let J := firstPassage m x
      have ht (l : ℕ) (hl : l ∈ range J) :
          P.real {ω | epHeight eps (keys ω) n ≤ l} ≤ K * m l / n := by
        apply htail l
        have hml : m l < x := lt_of_lt_firstPassage (mem_range.mp hl)
        change m l < (n : ℝ) / R at hml
        simpa only [mul_comm] using (lt_div_iff₀ hRpos).mp hml
      have hsum : ∑ l ∈ range J, P.real {ω | epHeight eps (keys ω) n ≤ l} ≤
          2 * K / R := by
        calc
          ∑ l ∈ range J, P.real {ω | epHeight eps (keys ω) n ≤ l} ≤
              ∑ l ∈ range J, K * m l / n := sum_le_sum ht
          _ = K * (∑ l ∈ range J, m l) / n := by rw [← sum_div, ← mul_sum]
          _ ≤ 2 * K / R := by
            rcases Nat.eq_zero_or_pos J with hJ | hJ
            · simp [hJ]; positivity
            · obtain ⟨j, hj⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
              have hs := kep_sum_span_le_twice_last (fun l => (hpos l).le) hstep j
              have hmj : m j < x := lt_of_lt_firstPassage (by change j < J; omega)
              rw [hj]
              have hs' : ∑ l ∈ range (j + 1), m l ≤ 2 * x := by linarith
              calc
                K * (∑ l ∈ range (j + 1), m l) / n ≤ K * (2 * x) / n := by gcongr
                _ = 2 * K / R := by dsimp [x]; field_simp
      have hlow := nat_sub_sum_early_le_integral
        (measurable_epHeight_comp eps n hkeys) hInt J
      have hJ := (abs_le.mp (firstPassage_log_bound hm0 hpos hex hc hlog hx)).1
      change -(1 + B / c) ≤ (J : ℝ) - Real.log x / c at hJ
      have hxlog : Real.log x / c = Real.log n / c - Real.log R / c := by
        dsimp [x]
        rw [Real.log_div hnpos.ne' hRpos.ne', sub_div]
      rw [hxlog] at hJ
      linarith
    · have hnl : Real.log n / c ≤ Real.log R / c :=
        div_le_div_of_nonneg_right (Real.log_le_log hnpos (le_of_not_ge hRn)) hc.le
      have hBc : 0 ≤ B / c := div_nonneg hB hc.le
      have hKR : 0 ≤ 2 * K / R := by positivity
      linarith
  have hlogAD : 0 ≤ Real.log (A + D) / Real.log (⌊2 * eps⌋₊ + 1) :=
    div_nonneg (Real.log_nonneg hAD) hqpos.le
  have hlogR : 0 ≤ Real.log R / c := div_nonneg (Real.log_nonneg hR) hc.le
  have hKR : 0 ≤ 2 * K / R := by positivity
  rw [abs_le]
  constructor <;> linarith

end

end PGM
