import PLAStochastic.Index.GEP.RawDisc.OccupationDerivative

/-!
# WP4 `RawDisc` assembly, part 8: the column sums of the exponential test

The derivative identity needs `WSummable ε l ν ν` and `WSummable ε l ν σ`:

* `wSummable_self`: under `ν^∞` the column sums are `(k+1) E_ν[e^{l S_k} 1{k<T}]`, and
  `∑_k (k+1) e^{l S_k} 1{k<T} ≤ T² e^{l S_T} ≤ κ⁻² (e^{2κT} + e^{2l S_T})`, so they are summable
  once `T` and `S_T` have exponential moments (stopping tail and `lawPhi_expMom`);
* `wSummable_sigma`: the one-letter survival values `β_{k,i} = E_{wordLaw ν σ {i}}[e^{l S_k} 1{k<T}]`
  are controlled by the survival bound itself: the linear coefficient of the survival polynomial
  of the positive test `e^{l y}` is `∑_{i<k} β_{k,i} - k α_k`, bounded by `2 B_k / r` on a disc
  of radius `r` (Cauchy, `abs_survLin_le`).  No deleted-mark window argument is needed.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

theorem sq_mul_exp_le {κ m s : ℝ} (hκ : 0 < κ) (hm : 0 ≤ m) :
    m ^ 2 * Real.exp s ≤ (Real.exp (2 * κ * m) + Real.exp (2 * s)) / κ ^ 2 := by
  have h1 := Real.pow_div_factorial_le_exp (x := κ * m) (by positivity) 2
  have h2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h2, div_le_iff₀ (by norm_num), mul_pow] at h1
  have e1 : Real.exp (2 * κ * m) = Real.exp (κ * m) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e2 : Real.exp (2 * s) = Real.exp s ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e1, e2, le_div_iff₀ (by positivity)]
  have hs := Real.exp_pos s
  have hk := Real.exp_pos (κ * m)
  nlinarith [sq_nonneg (Real.exp (κ * m) - Real.exp s), mul_le_mul_of_nonneg_right h1 hs.le]

theorem summable_of_tsum_ofReal_ne_top {a : ℕ → ℝ} (h0 : ∀ k, 0 ≤ a k)
    (h : ∑' k, ENNReal.ofReal (a k) ≠ ⊤) : Summable a :=
  (ENNReal.summable_toReal h).congr fun k => ENNReal.toReal_ofReal (h0 k)

variable {eps l : ℝ} {ν σ : ProbabilityMeasure ℝ}

/-- **Column sums under `ν^∞`.** -/
theorem wSummable_self (hl : 0 ≤ l) (hν : SmallMgf l ν) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    {κ : ℝ} (hκ : 0 < κ)
    (hT : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * κ * (gapSegLen eps g).toNat)) ∂(iidLaw ν) ≠ ⊤)
    (hS : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * (l * stopSum eps g))) ∂(iidLaw ν) ≠ ⊤) :
    WSummable eps l ν ν := by
  have e : ∀ k, ∑ i ∈ Finset.range (k + 1), sW eps l ν ν i k =
      ((k : ℝ) + 1) * sW eps l ν ν 0 k := by
    intro k
    simp only [sW, wLaw_self]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  unfold WSummable
  simp_rw [e]
  refine summable_of_tsum_ofReal_ne_top (fun k => mul_nonneg (by positivity)
    (sW_nonneg eps l ν ν 0 k)) ?_
  have hL : ∀ k : ℕ, ENNReal.ofReal (((k : ℝ) + 1) * sW eps l ν ν 0 k) =
      ∫⁻ g, ((k : ℝ≥0∞) + 1) * expIndL eps l k g ∂(iidLaw ν) := by
    intro k
    rw [ENNReal.ofReal_mul (by positivity), ofReal_sW hν hν 0 k, wLaw_self,
      lintegral_const_mul _ (measurable_expIndL eps l k)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  simp_rw [hL]
  rw [← lintegral_tsum fun k => ((measurable_expIndL eps l k).const_mul _).aemeasurable]
  have hpos : ∀ᵐ g ∂(iidLaw ν), ∀ j, 0 ≤ g j := by
    filter_upwards [ae_pos_piLaw (ρ := fun _ => ν) fun _ => hν.pos] with g hg j
    exact (hg j).le
  have hpt : ∀ᵐ g ∂(iidLaw ν), ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * expIndL eps l k g ≤
      ENNReal.ofReal (1 / κ ^ 2) *
        (ENNReal.ofReal (Real.exp (2 * κ * (gapSegLen eps g).toNat)) +
          ENNReal.ofReal (Real.exp (2 * (l * stopSum eps g)))) := by
    filter_upwards [hpos, hfin] with g hg hT
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    rw [tsum_eq_sum (s := Finset.range m) fun k hk => by
      rw [Finset.mem_range] at hk
      rw [expIndL, Set.indicator_of_notMem
        (fun h => hk ((mem_survSet_iff_of_eq hm.symm k).1 h))]
      simp]
    have hSm : stopSum eps g = gapKeys g m := stopSum_of_eq hm.symm
    have hTm : (gapSegLen eps g).toNat = m := by rw [← hm, ENat.toNat_natCast]
    rw [hSm, hTm]
    calc ∑ k ∈ Finset.range m, ((k : ℝ≥0∞) + 1) * expIndL eps l k g
        ≤ ∑ _k ∈ Finset.range m, (m : ℝ≥0∞) * ENNReal.ofReal (Real.exp (l * gapKeys g m)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_range] at hk
          rw [expIndL, Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm k).2 hk)]
          refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (gapKeys_mono hg hk.le) hl)))
          exact_mod_cast hk
      _ = ENNReal.ofReal ((m : ℝ) ^ 2 * Real.exp (l * gapKeys g m)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            ENNReal.ofReal_mul (by positivity), sq, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((Real.exp (2 * κ * m) + Real.exp (2 * (l * gapKeys g m))) / κ ^ 2) :=
          ENNReal.ofReal_le_ofReal (sq_mul_exp_le hκ (Nat.cast_nonneg m))
      _ = ENNReal.ofReal (1 / κ ^ 2) * (ENNReal.ofReal (Real.exp (2 * κ * m)) +
            ENNReal.ofReal (Real.exp (2 * (l * gapKeys g m)))) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [lintegral_add_left]
  · exact ENNReal.add_ne_top.2 ⟨hT, hS⟩
  · exact ((measurable_const.mul
      ((Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp
        (isStoppingRule_gapSegLen eps).measurable)).exp).ennreal_ofReal

theorem sum_sW_self (eps l : ℝ) (ν : ProbabilityMeasure ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), sW eps l ν ν i k =
      ((k : ℝ) + 1) * survInt eps (iidLaw ν) k (expTest l) := by
  simp only [sW, wLaw_self]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Column sums under the one-letter laws**, from a bound of the survival polynomial of the
exponential test on a disc. -/
theorem wSummable_sigma (hWν : WSummable eps l ν ν) {r : ℝ} (hr : 0 < r) {B : ℕ → ℝ}
    (hBs : Summable B)
    (hB : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ k, ‖cSurv eps ν σ z k (expTest l)‖ ≤ B k) :
    WSummable eps l ν σ := by
  have hbound : ∀ k, ∑ i ∈ Finset.range (k + 1), sW eps l ν σ i k ≤
      2 / r * B k + ∑ i ∈ Finset.range (k + 1), sW eps l ν ν i k := by
    intro k
    have hlin := abs_survLin_le eps ν σ k (expTest l) hr fun z hz => hB z hz k
    have hkk : sW eps l ν σ k k = survInt eps (iidLaw ν) k (expTest l) :=
      survInt_wLaw_self (measurable_expTest l) k
    have hi : ∀ i ∈ Finset.range k, sW eps l ν σ i k =
        survInt eps (wordLaw ν σ {i}) k (expTest l) := fun i _ => by
      rw [sW, wLaw_sigma]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hi, hkk, sum_sW_self]
    have h1 := (le_abs_self _).trans hlin
    unfold survLin at h1
    have h2 : 2 * B k / r = 2 / r * B k := by ring
    linarith
  refine Summable.of_nonneg_of_le (fun k => Finset.sum_nonneg fun i _ =>
    sW_nonneg eps l ν σ i k) hbound ((hBs.mul_left (2 / r)).add hWν)

end

end PGM
