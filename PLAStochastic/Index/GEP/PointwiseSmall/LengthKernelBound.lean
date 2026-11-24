import PLAStochastic.Index.GEP.DirectTerm.CoarseBound
import PLAStochastic.Index.GEP.RawDisc.ProductLaws

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: the coarse bound of `J_C`

`J_C(x) = ∑_k ∑_{i<k} P(k < T(g with g_i := x))` (`lawJC`).  For `i < k` the event
`{k < T(g')}`, `g' = update g i x`, implies both windows that avoid the inserted coordinate
(`pw_left_of_lt`, `pw_window_of_lt`): the left one `{i < T(g)}` and the right one
`{k-1-i < T(g_{i+1+·})}`.  Taking the smaller probability (as in `PLAStochastic/Index/GEP/DirectTerm/CoarseBound.lean`) and the
geometric stopping tail `P(m < T) ≤ (72/71) q^{4m}` gives `P ≤ (72/71) q^{2(k-1)}`
(`pwQ_le`), uniformly in `x`, so the double series has the summable majorant
`m_k = (72/71) k ρ^k / ρ`, `ρ = q²`, with `∑ m_k ≤ K ε⁴` (`pw_lawJC_facts`).

Consequences, for the regular class and `ε` large:
* `0 ≤ J_C(x) ≤ K ε⁴` for every real `x`, and `J_C` is measurable (`pw_lawJC_bound`);
* for every probability law `ρ`, `∫ J_C dρ = ∑_k ∑_{i<k} P_{ν^{(i → ρ)}}(k < T)`, where
  `ν^{(i → ρ)}` is the product law with `ρ` at coordinate `i` (`pw_hasSum_integral_lawJC`).
No `WSummable` bookkeeping is needed.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-! ## The two windows -/

/-- The right window of an inserted survival event. -/
theorem pw_window_of_lt {eps x : ℝ} {g : ℕ → ℝ} {i k : ℕ} (hik : i < k)
    (h : (k : ℕ∞) < gapSegLen eps (Function.update g i x)) :
    ((k - 1 - i : ℕ) : ℕ∞) < gapSegLen eps (fun s => g (i + 1 + s)) := by
  set g' := Function.update g i x with hg'
  rw [gapSegLen, lt_segLen_iff] at h
  have hw := prefixAffineFeasible_window (r := i + 1) (w := k - 1 - i + 1) h (by omega)
  have hs : ((k - 1 - i : ℕ) : ℕ∞) < segLen eps (fun j => gapKeys g' (i + 1 + j)) :=
    (lt_segLen_iff _).2 hw
  rw [segLen_gapKeys_shift, hg', update_shift_eq] at hs
  exact hs

/-- The left window of an inserted survival event. -/
theorem pw_left_of_lt {eps x : ℝ} {g : ℕ → ℝ} {i k : ℕ} (hik : i < k)
    (h : (k : ℕ∞) < gapSegLen eps (Function.update g i x)) :
    (i : ℕ∞) < gapSegLen eps g := by
  refine lt_gapSegLen_update_iff.1 (lt_of_le_of_lt ?_ h)
  exact_mod_cast hik.le

/-! ## One inserted survival probability -/

/-- `P(k < T(g with g_i := x))`. -/
def pwQ (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i : ℕ) (x : ℝ) : ℝ :=
  (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}

theorem lawJC_eq_pwQ (eps : ℝ) (ν : ProbabilityMeasure ℝ) (x : ℝ) :
    lawJC eps ν x = ∑' k : ℕ, ∑ i ∈ Finset.range k, pwQ eps ν k i x := rfl

theorem pwQ_nonneg (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i : ℕ) (x : ℝ) :
    0 ≤ pwQ eps ν k i x := measureReal_nonneg

theorem pwQ_eq_integral (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i : ℕ) (x : ℝ) :
    pwQ eps ν k i x = ∫ g, (survSet eps k).indicator (fun _ => (1 : ℝ))
      (Function.update g i x) ∂(iidLaw ν) := by
  have hm : Measurable fun g : ℕ → ℝ => Function.update g i x :=
    (measurable_update_pair i).comp (measurable_const.prodMk measurable_id)
  have e : (fun g : ℕ → ℝ => (survSet eps k).indicator (fun _ => (1 : ℝ))
      (Function.update g i x)) =
      ((fun g : ℕ → ℝ => Function.update g i x) ⁻¹' survSet eps k).indicator (fun _ => 1) := by
    funext g
    rfl
  rw [e, integral_indicator_const _ ((measurableSet_survSet eps k).preimage hm), smul_eq_mul,
    mul_one]
  rfl

theorem measurable_pwQ (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i : ℕ) :
    Measurable (pwQ eps ν k i) := by
  have h := measurable_integral_update ν i
    (G := (survSet eps k).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator (measurableSet_survSet eps k))
  have e : pwQ eps ν k i = fun y => ∫ g, (survSet eps k).indicator (fun _ => (1 : ℝ))
      (Function.update g i y) ∂(iidLaw ν) := funext (pwQ_eq_integral eps ν k i)
  rw [e]
  exact h

/-- **The window bound** for one inserted survival probability. -/
theorem pwQ_le {ν : ProbabilityMeasure ℝ} {eps q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) {i k : ℕ} (hik : i < k) (x : ℝ) :
    pwQ eps ν k i x ≤ 72 / 71 * q ^ (2 * (k - 1)) := by
  have hmono : ∀ {m n : ℕ}, n ≤ m → 72 / 71 * q ^ m ≤ 72 / 71 * q ^ n := fun hnm =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hnm) (by norm_num)
  set E := {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} with hE
  have hL : pwQ eps ν k i x ≤ 72 / 71 * q ^ (4 * i) := by
    have hsub : E ⊆ {g | (i : ℕ∞) < gapSegLen eps g} := fun g hg => pw_left_of_lt hik hg
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (measure_mono hsub).trans ((htail i).trans (le_of_eq ?_))
    rw [← pow_mul]
  have hR : pwQ eps ν k i x ≤ 72 / 71 * q ^ (4 * (k - 1 - i)) := by
    have hsub : E ⊆ {g | ((k - 1 - i : ℕ) : ℕ∞) < gapSegLen eps (fun s => g (i + 1 + s))} :=
      fun g hg => pw_window_of_lt hik hg
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (measure_mono hsub).trans ?_
    rw [measure_lt_gapSegLen_shift, pow_mul]
    exact htail _
  by_cases hc : k - 1 - i ≤ i
  · exact hL.trans (hmono (by omega))
  · exact hR.trans (hmono (by omega))

/-! ## The majorant of the double series -/

/-- **Coarse facts for `J_C`** on the class: a summable majorant `m_k` of the inner sums, with
`∑ m ≤ K ε⁴`, uniform in the inserted value. -/
theorem pw_lawJC_facts (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ KJ e0 : ℝ, 0 ≤ KJ ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ m : ℕ → ℝ, (∀ k, 0 ≤ m k) ∧ Summable m ∧
        ∑' k, m k ≤ KJ * eps ^ 4 ∧
        ∀ k x, ∑ i ∈ Finset.range k, pwQ eps ν k i x ≤ m k := by
  obtain ⟨e₀, he₀1, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  set c := tailRate * regV vlo with hc
  have hcpos : 0 < c := mul_pos tailRate_pos (regV_pos hvlo)
  refine ⟨72 / 71 * (1 + 2 / c) ^ 2, e₀, by positivity, he₀1, fun eps heps ν hν => ?_⟩
  obtain ⟨-, -, htail, -⟩ := hfacts eps heps ν hν
  have heps1 : 1 ≤ eps := he₀1.trans heps
  have heps0 : 0 < eps := by linarith
  have he2p : 0 < eps ^ 2 := by positivity
  set q := Real.exp (-c / (4 * eps ^ 2)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by positivity))
  have hq4 : q ^ 4 = tailA vlo eps := by
    rw [hq, ← Real.exp_nat_mul, tailA]
    congr 1
    rw [hc]
    field_simp
    push_cast
    ring
  have htail' : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m) := by rw [hq4]; exact htail
  set ρ := q ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρe : ρ = Real.exp (-(c / (2 * eps ^ 2))) := by
    rw [hρ, hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    ring
  have hρ1 : ρ < 1 := by
    rw [hρe, Real.exp_lt_one_iff]
    have : 0 < c / (2 * eps ^ 2) := by positivity
    linarith
  have hρn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1
  set m : ℕ → ℝ := fun k => 72 / 71 / ρ * ((k : ℝ) * ρ ^ k) with hm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by positivity
  have hms : Summable m := (hasSum_coe_mul_geometric_of_norm_lt_one hρn).summable.mul_left _
  refine ⟨m, hm0, hms, ?_, fun k x => ?_⟩
  · have hsum : ∑' k, m k = 72 / 71 / (1 - ρ) ^ 2 := by
      rw [hm, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hρn]
      field_simp
    rw [hsum]
    have h1ρ : 0 < 1 - ρ := by linarith
    have hw : 1 / (1 - ρ) ≤ (1 + 2 / c) * eps ^ 2 := by
      have h := one_div_one_sub_exp_neg_le (u := c / (2 * eps ^ 2)) (by positivity)
      rw [← hρe] at h
      refine h.trans ?_
      rw [one_div_div, show 2 * eps ^ 2 / c = 2 / c * eps ^ 2 by ring]
      have : 0 ≤ 2 / c := by positivity
      nlinarith
    have hw0 : 0 ≤ 1 / (1 - ρ) := by positivity
    calc 72 / 71 / (1 - ρ) ^ 2 = 72 / 71 * (1 / (1 - ρ)) ^ 2 := by
          rw [one_div_pow]; ring
      _ ≤ 72 / 71 * ((1 + 2 / c) * eps ^ 2) ^ 2 := by gcongr
      _ = 72 / 71 * (1 + 2 / c) ^ 2 * eps ^ 4 := by ring
  · have hterm : ∀ i ∈ Finset.range k, pwQ eps ν k i x ≤ 72 / 71 * q ^ (2 * (k - 1)) :=
      fun i hi => pwQ_le hq0.le hq1 htail' (Finset.mem_range.1 hi) x
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [hm]
    · have e : q ^ (2 * (k - 1)) = ρ ^ k / ρ := by
        rw [hρ, ← pow_mul, eq_div_iff (by positivity), ← pow_add]
        congr 1
        omega
      rw [e, hm]
      apply le_of_eq
      ring

/-! ## Consequences -/

/-- **`J_C` is bounded and measurable** on the class: `0 ≤ J_C(x) ≤ K ε⁴` for every real `x`,
with the inner sums absolutely summable. -/
theorem pw_lawJC_bound (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ KJ e0 : ℝ, 0 ≤ KJ ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν →
        Measurable (lawJC eps ν) ∧ ∀ x, 0 ≤ lawJC eps ν x ∧ lawJC eps ν x ≤ KJ * eps ^ 4 := by
  obtain ⟨KJ, e0, hKJ, he0, hf⟩ := pw_lawJC_facts hD hθ hvlo hv
  refine ⟨KJ, e0, hKJ, he0, fun eps heps ν hν => ?_⟩
  obtain ⟨m, hm0, hms, hmsum, hle⟩ := hf eps heps ν hν
  have hnn : ∀ k x, 0 ≤ ∑ i ∈ Finset.range k, pwQ eps ν k i x := fun k x =>
    Finset.sum_nonneg fun i _ => pwQ_nonneg eps ν k i x
  have hs : ∀ x, Summable fun k => ∑ i ∈ Finset.range k, pwQ eps ν k i x := fun x =>
    Summable.of_nonneg_of_le (fun k => hnn k x) (fun k => hle k x) hms
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have h : lawJC eps ν = fun x => ∑' k : ℕ, ∑ i ∈ Finset.range k, pwQ eps ν k i x :=
      funext (lawJC_eq_pwQ eps ν)
    rw [h]
    exact Measurable.tsum fun k => Finset.measurable_sum _ fun i _ => measurable_pwQ eps ν k i
  · rw [lawJC_eq_pwQ]; exact tsum_nonneg fun k => hnn k x
  · rw [lawJC_eq_pwQ]
    exact ((hs x).tsum_le_tsum (fun k => hle k x) hms).trans hmsum

/-- The product law with `ρ` at coordinate `i` and `ν` elsewhere. -/
def pwLaw (ν ρ : ProbabilityMeasure ℝ) (i : ℕ) : Measure (ℕ → ℝ) :=
  piLaw (Function.update (fun _ => ν) i ρ)

instance (ν ρ : ProbabilityMeasure ℝ) (i : ℕ) : IsProbabilityMeasure (pwLaw ν ρ i) := by
  unfold pwLaw; infer_instance

theorem pwLaw_self (ν : ProbabilityMeasure ℝ) (i : ℕ) : pwLaw ν ν i = iidLaw ν := by
  rw [pwLaw, show Function.update (fun _ : ℕ => ν) i ν = fun _ => ν from
    Function.update_eq_self i _]
  rfl

theorem pwLaw_sigma (ν σ : ProbabilityMeasure ℝ) (i : ℕ) : pwLaw ν σ i = wordLaw ν σ {i} := by
  rw [pwLaw, wordLaw_eq_piLaw]
  refine piLaw_congr fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [h]

/-- The integral of one inserted survival probability is the survival probability under the
product law with `ρ` at the inserted coordinate. -/
theorem integral_pwQ (eps : ℝ) (ν ρ : ProbabilityMeasure ℝ) (k i : ℕ) :
    ∫ x, pwQ eps ν k i x ∂(ρ : Measure ℝ) = (pwLaw ν ρ i).real (survSet eps k) := by
  have hH : Measurable ((survSet eps k).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_survSet eps k)
  have hl := lintegral_piLaw_update (fun _ => ν) i ρ hH
  rw [lintegral_indicator_const (measurableSet_survSet eps k), one_mul] at hl
  have hq : ∀ y, ENNReal.ofReal (pwQ eps ν k i y) =
      ∫⁻ g, (survSet eps k).indicator (fun _ => (1 : ℝ≥0∞)) (Function.update g i y)
        ∂(piLaw fun _ => ν) := by
    intro y
    rw [pwQ, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hm : Measurable fun g : ℕ → ℝ => Function.update g i y :=
      (measurable_update_pair i).comp (measurable_const.prodMk measurable_id)
    have e : (fun g : ℕ → ℝ => (survSet eps k).indicator (fun _ => (1 : ℝ≥0∞))
        (Function.update g i y)) =
        ((fun g : ℕ → ℝ => Function.update g i y) ⁻¹' survSet eps k).indicator (fun _ => 1) := by
      funext g
      rfl
    rw [e, lintegral_indicator_const ((measurableSet_survSet eps k).preimage hm), one_mul]
    rfl
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => pwQ_nonneg eps ν k i y)
    (measurable_pwQ eps ν k i).aestronglyMeasurable]
  simp_rw [hq]
  rw [← hl, measureReal_def]
  rfl

/-- **The integral of `J_C`** against any probability law `ρ`:
`∫ J_C dρ = ∑_k ∑_{i<k} P_{ν^{(i → ρ)}}(k < T)`, as a `HasSum`. -/
theorem pw_hasSum_integral_lawJC (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ ρ : ProbabilityMeasure ℝ,
        HasSum (fun k : ℕ => ∑ i ∈ Finset.range k, (pwLaw ν ρ i).real (survSet eps k))
          (∫ x, lawJC eps ν x ∂(ρ : Measure ℝ)) := by
  obtain ⟨KJ, e0, hKJ, he0, hf⟩ := pw_lawJC_facts hD hθ hvlo hv
  refine ⟨e0, he0, fun eps heps ν hν ρ => ?_⟩
  obtain ⟨m, hm0, hms, -, hle⟩ := hf eps heps ν hν
  set F : ℕ → ℝ → ℝ := fun k x => ∑ i ∈ Finset.range k, pwQ eps ν k i x with hF
  have hFm : ∀ k, Measurable (F k) := fun k =>
    Finset.measurable_sum _ fun i _ => measurable_pwQ eps ν k i
  have hFnn : ∀ k x, 0 ≤ F k x := fun k x => Finset.sum_nonneg fun i _ => pwQ_nonneg eps ν k i x
  have hFi : ∀ k, Integrable (F k) (ρ : Measure ℝ) := fun k =>
    Integrable.of_bound (hFm k).aestronglyMeasurable (m k) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn k x)]; exact hle k x)
  have hnorm : ∀ k, ∫ x, ‖F k x‖ ∂(ρ : Measure ℝ) ≤ m k := by
    intro k
    have h := integral_mono (hFi k).norm (integrable_const (m k)) fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn k x)]; exact hle k x
    simpa using h
  have hsum : Summable fun k => ∫ x, ‖F k x‖ ∂(ρ : Measure ℝ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hnorm hms
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have e1 : ∀ k, ∫ x, F k x ∂(ρ : Measure ℝ) =
      ∑ i ∈ Finset.range k, (pwLaw ν ρ i).real (survSet eps k) := by
    intro k
    rw [hF, integral_finsetSum _ fun i _ => Integrable.of_bound
      (measurable_pwQ eps ν k i).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pwQ_nonneg eps ν k i x)]
        exact measureReal_le_one)]
    exact Finset.sum_congr rfl fun i _ => integral_pwQ eps ν ρ k i
  simp_rw [e1] at h
  have e2 : (fun x => ∑' k, F k x) = lawJC eps ν := funext fun x => (lawJC_eq_pwQ eps ν x).symm
  rwa [e2] at h

end

end PGM
