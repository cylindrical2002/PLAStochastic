import PLAStochastic.Index.CEPS.Output.Input
import PLAStochastic.Index.CEPS.Output.UStat
import PLAStochastic.ForMathlib.MeasureTheory.Integral.ThreeFactorHolder
import PLAStochastic.ForMathlib.Analysis.SpecificLimits.TwoScaleSum

/-!
# Track O: the bound for one stopping length

`output-closure.md` (O11)–(O12). Fix `n` and the cone `A = {z : Fin n → ℝ | T(z) = n}`. For
each insertion order `i ≤ r` and high part `β`, Hölder with exponents `(4, 4, 2)`
(`lintegral_indicator_mul_le`) splits the grouped term into

* the negative moment `∫ (∑ x)^{-4r} ≤ M_H |Hᶜ|^{-4r} e^{32Er}` (AM–GM on the uninserted
  coordinates, `lintegral_sum_rpow_neg_le`);
* the stopping probability `μ(A) ≤ W^{|H|} Q` (a hypothesis here, paid by `Tails`);
* the centred sum `∫ V² ≤ M_H n^k i^{2i} J^k`, `k = i - ∑ β` (`lintegral_sq_outCentred_le`).

Since a realisable high part has `β_l ≥ 2` on `H`, `W^{|H|} n^{k/2} ≤ n^{i/2} (W/n)^{|H|}`
(`lintegral_term_le`), and the sum over high parts factorises,
`∑_β (W/n)^{|H|} = (1 + iW/n)^n ≤ e^{iW}` (`sum_outBox_le`). The result is
`|τ|^r |Φ_n(τ)| ≤ K n^{-r/2} Q^{1/4}` (`perLength_bound`).
-/

noncomputable section

open MeasureTheory Set Finset Filter
open scoped ENNReal

namespace PGM

variable {r : ℕ} {E κ : ℝ} {f : ℝ → ℝ} {ν : ProbabilityMeasure ℝ}

/-- The constant of one grouped term. -/
def outTermConst (r : ℕ) (E κ : ℝ) (i : ℕ) : ℝ :=
  2 ^ r * Real.exp (8 * E * r) * (i : ℝ) ^ i * (max 1 (outFisher E κ)) ^ r

/-- The constant of one stopping length. -/
def outLengthConst (r : ℕ) (E κ : ℝ) : ℝ :=
  ∑ i ∈ range (r + 1), |outCoeff r i| * outTermConst r E κ i * Real.exp (i * outWeightBound E κ)

/-- The cone of a stop at `n`. -/
theorem stopsAt_smul {eps : ℝ} {n : ℕ} {c : ℝ} (hc : 0 < c) (z : Fin n → ℝ) :
    stopsAt eps (c • z) ↔ stopsAt eps z := by
  have hk : vkeys (c • z) = fun j => c * vkeys z j + 0 := by
    funext j
    simp only [vkeys, gapKeys, vext, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  simp only [stopsAt, hk, prefixAffineFeasible_affine_iff hc.ne']

theorem outCentred_indep {n : ℕ} (i : ℕ) (β : Fin n → ℕ) (x y : Fin n → ℝ)
    (hxy : ∀ l ∉ outSupp β, x l = y l) : outCentred f i β x = outCentred f i β y := by
  refine Finset.sum_congr rfl fun c hc => Finset.prod_congr rfl fun l hl => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  have hl1 : outCount c l = 1 := by simpa [outSingles] using hl
  have hβ : β l = 0 := by rw [← hc]; simp [outHigh, hl1]
  rw [hxy l (by simp [outSupp, hβ])]

/-- The sum over high parts factorises. -/
theorem sum_outBox_le {n i : ℕ} (hn : 1 ≤ n) {W : ℝ} (hW : 0 ≤ W) :
    ∑ β ∈ outBox n i, (W / n) ^ #(outSupp β) ≤ Real.exp (i * W) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : ∀ β : Fin n → ℕ, (W / n) ^ #(outSupp β) =
      ∏ l, (if β l = 0 then (1 : ℝ) else W / n) := by
    intro β
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    rfl
  simp_rw [hprod]
  rw [outBox, sum_prod_piFinset (range (i + 1)) (fun _ a => if a = 0 then (1 : ℝ) else W / n)]
  have hsum : ∑ a ∈ range (i + 1), (if a = 0 then (1 : ℝ) else W / n) ≤ 1 + i * W / n := by
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, if_true, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [mul_div_assoc]
    linarith
  calc ∏ _l : Fin n, ∑ a ∈ range (i + 1), (if a = 0 then (1 : ℝ) else W / n)
      ≤ ∏ _l : Fin n, (1 + i * W / n) :=
        Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun a _ => by
          split_ifs <;> positivity) fun l _ => hsum
    _ = (1 + i * W / n) ^ n := by simp
    _ ≤ Real.exp (i * W / n) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (i * W / n)]) n
    _ = Real.exp (i * W) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

/-- The masses of the inserted factors are bounded by the weighted mass bound. -/
theorem OutInput.prod_outMass_le (h : OutInput r E κ f ν) {n i : ℕ} (hi : i ≤ r)
    {β : Fin n → ℕ} (hβ : ∀ l, β l ≤ i) :
    ∏ l ∈ outSupp β, outMass f (β l) ≤ ENNReal.ofReal (outWeightBound E κ ^ #(outSupp β)) := by
  rw [ENNReal.ofReal_pow h.outWeightBound_nonneg, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun l _ => ?_
  have hκ : 0 ≤ κ / 2 := by have := h.κpos; positivity
  exact (outMass_le_outWeight f hκ _).trans
    (h.outWeight_le (((hβ l).trans hi).trans (le_max_left r 1)))

theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  have : x ^ k = (Real.sqrt x ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]
  rw [this, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]

/-- **The real algebra of one grouped term.** -/
theorem term_real_le {n i k H N : ℕ} {W Q J : ℝ} (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hJ : 0 ≤ J)
    (hn : 1 ≤ n) (hN : (n : ℝ) / 2 ≤ N) (hk : k ≤ r) (hH : n ^ H * Real.sqrt n ^ k ≤ Real.sqrt n ^ i)
    (Eb : ℝ) :
    (W ^ H * ((N : ℝ) ^ (-(4 * r : ℝ)) * Real.exp (8 * Eb * (4 * r)))) ^ (1 / 4 : ℝ) *
        (W ^ H * Q) ^ (1 / 4 : ℝ) *
        (W ^ H * ((n : ℝ) ^ k * (i : ℝ) ^ i * (i : ℝ) ^ i * J ^ k)) ^ (1 / 2 : ℝ) ≤
      2 ^ r * Real.exp (8 * Eb * r) * (i : ℝ) ^ i * (max 1 J) ^ r *
        (Real.sqrt n ^ i / (n : ℝ) ^ r) * Q ^ (1 / 4 : ℝ) * (W / n) ^ H := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by linarith
  set w := W ^ H with hw
  have hw0 : 0 ≤ w := pow_nonneg hW H
  have hx0 : 0 ≤ (N : ℝ) ^ (-(4 * r : ℝ)) * Real.exp (8 * Eb * (4 * r)) := by positivity
  have hz0 : 0 ≤ (n : ℝ) ^ k * (i : ℝ) ^ i * (i : ℝ) ^ i * J ^ k := by positivity
  rw [Real.mul_rpow hw0 hx0, Real.mul_rpow hw0 hQ, Real.mul_rpow hw0 hz0]
  have hww : w ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ) * w ^ (1 / 2 : ℝ) = w := by
    rw [← Real.rpow_add' hw0 (by norm_num), ← Real.rpow_add' hw0 (by norm_num)]
    norm_num
  have hx : ((N : ℝ) ^ (-(4 * r : ℝ)) * Real.exp (8 * Eb * (4 * r))) ^ (1 / 4 : ℝ) =
      ((N : ℝ) ^ r)⁻¹ * Real.exp (8 * Eb * r) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN0.le,
      ← Real.exp_mul]
    congr 1
    · rw [show -(4 * (r : ℝ)) * (1 / 4) = -(r : ℝ) by ring, Real.rpow_neg hN0.le,
        Real.rpow_natCast]
    · ring_nf
  have hz : ((n : ℝ) ^ k * (i : ℝ) ^ i * (i : ℝ) ^ i * J ^ k) ^ (1 / 2 : ℝ) =
      Real.sqrt n ^ k * (i : ℝ) ^ i * Real.sqrt J ^ k := by
    have e : (n : ℝ) ^ k * (i : ℝ) ^ i * (i : ℝ) ^ i * J ^ k =
        ((n : ℝ) ^ k * J ^ k) * ((i : ℝ) ^ i * (i : ℝ) ^ i) := by ring
    rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity),
      Real.sqrt_mul (by positivity), sqrt_pow_eq hn0.le, sqrt_pow_eq hJ]
    ring
  rw [hx, hz]
  -- the three elementary bounds
  have hNr : ((N : ℝ) ^ r)⁻¹ ≤ 2 ^ r / (n : ℝ) ^ r := by
    rw [div_eq_mul_inv, ← inv_pow, ← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ r
    rw [inv_le_comm₀ hN0 (by positivity), mul_inv, inv_inv]
    linarith
  have hJr : Real.sqrt J ^ k ≤ (max 1 J) ^ r := by
    have h1 : Real.sqrt J ≤ max 1 J := by
      rcases le_total J 1 with hJ1 | hJ1
      · exact (Real.sqrt_le_one.mpr hJ1).trans (le_max_left _ _)
      · exact (Real.sqrt_le_self_iff.mpr (Or.inr hJ1)).trans (le_max_right _ _)
    calc Real.sqrt J ^ k ≤ (max 1 J) ^ k := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 k
      _ ≤ (max 1 J) ^ r := pow_le_pow_right₀ (le_max_left _ _) hk
  have hwn : w * Real.sqrt n ^ k ≤ Real.sqrt n ^ i * (W / n) ^ H := by
    rw [hw, div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    calc W ^ H * Real.sqrt n ^ k * (n : ℝ) ^ H = W ^ H * ((n : ℝ) ^ H * Real.sqrt n ^ k) := by ring
      _ ≤ W ^ H * Real.sqrt n ^ i := mul_le_mul_of_nonneg_left hH (pow_nonneg hW H)
      _ = Real.sqrt n ^ i * W ^ H := by ring
  have hQ4 : 0 ≤ Q ^ (1 / 4 : ℝ) := Real.rpow_nonneg hQ _
  have hexp : 0 ≤ Real.exp (8 * Eb * r) := (Real.exp_pos _).le
  calc w ^ (1 / 4 : ℝ) * (((N : ℝ) ^ r)⁻¹ * Real.exp (8 * Eb * r)) *
        (w ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ)) *
        (w ^ (1 / 2 : ℝ) * (Real.sqrt n ^ k * (i : ℝ) ^ i * Real.sqrt J ^ k))
      = (w ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ) * w ^ (1 / 2 : ℝ)) * ((N : ℝ) ^ r)⁻¹ *
          Real.exp (8 * Eb * r) * Q ^ (1 / 4 : ℝ) * Real.sqrt n ^ k * (i : ℝ) ^ i *
          Real.sqrt J ^ k := by ring
    _ = (w * Real.sqrt n ^ k) * ((N : ℝ) ^ r)⁻¹ * Real.exp (8 * Eb * r) * Q ^ (1 / 4 : ℝ) *
          (i : ℝ) ^ i * Real.sqrt J ^ k := by rw [hww]; ring
    _ ≤ (Real.sqrt n ^ i * (W / n) ^ H) * (2 ^ r / (n : ℝ) ^ r) * Real.exp (8 * Eb * r) *
          Q ^ (1 / 4 : ℝ) * (i : ℝ) ^ i * (max 1 J) ^ r := by
        gcongr
    _ = _ := by ring

theorem outFisher_nonneg {E κ : ℝ} (hE : 0 ≤ E) : 0 ≤ outFisher E κ :=
  mul_nonneg hE (setIntegral_nonneg measurableSet_Ioi fun x _ => by positivity)

/-- **The bound on one grouped term** (`output-closure.md` (O11)). -/
theorem lintegral_term_le (h : OutInput r E κ f ν) {n i : ℕ} (hi : i ≤ r)
    (hn : 17 * r + 1 ≤ n) (β : Fin n → ℕ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hY : #(outSupp β) ≤ r → outMeasure f β A ≤
      ENNReal.ofReal (outWeightBound E κ ^ #(outSupp β) * Q)) :
    ∫⁻ x, A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x
        ∂(outMeasure f β) ≤
      ENNReal.ofReal (outTermConst r E κ i * (Real.sqrt n ^ i / (n : ℝ) ^ r) * Q ^ (1 / 4 : ℝ) *
        (outWeightBound E κ / n) ^ #(outSupp β)) := by
  classical
  set H := outSupp β with hHdef
  set Wb := outWeightBound E κ with hWbdef
  have hWb : 0 ≤ Wb := h.outWeightBound_nonneg
  by_cases hreal : ∃ c : Fin i → Fin n, outHigh c = β
  swap
  · have hz : ∀ x, outCentred f i β x = 0 := by
      intro x
      refine Finset.sum_eq_zero fun c hc => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact absurd ⟨c, hc⟩ hreal
    have hz' : (fun x => A.indicator (fun x =>
        ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x) = fun _ => 0 := by
      funext x
      simp [hz]
    rw [hz', lintegral_zero]
    exact bot_le
  obtain ⟨c₀, hc₀⟩ := hreal
  have hsumβ : ∑ l, β l ≤ i := sum_high_le hc₀
  have hβle : ∀ l, β l ≤ i := fun l =>
    (Finset.single_le_sum (f := β) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans hsumβ
  have hne1 : ∀ l, β l ≠ 1 := by
    intro l
    rw [← hc₀]
    simp only [outHigh]
    split_ifs with h1 <;> omega
  have h2H : 2 * #H ≤ ∑ l, β l := by
    calc 2 * #H = ∑ _l ∈ H, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ l ∈ H, β l := Finset.sum_le_sum fun l hl => by
          have h0 : β l ≠ 0 := by simpa [hHdef, outSupp] using hl
          have := hne1 l
          omega
      _ ≤ ∑ l, β l := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => Nat.zero_le _
  have hHr : #H ≤ r := by omega
  have hcard : #Hᶜ = n - #H := by rw [Finset.card_compl, Fintype.card_fin]
  have hHc : Hᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hE : 0 ≤ E := h.E_nonneg
  set J := outFisher E κ with hJdef
  have hJ0 : 0 ≤ J := outFisher_nonneg hE
  obtain ⟨hρm, hρ2, hρ0, hρJ⟩ := h.fisher
  have hM := h.prod_outMass_le hi hβle
  -- the three factors
  set a : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (((∑ l, x l) ^ r)⁻¹) with ha
  set b : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal |outCentred f i β x| with hb
  have hsum_meas : Measurable fun x : Fin n → ℝ => ∑ l, x l :=
    Finset.measurable_sum _ fun l _ => measurable_pi_apply l
  have ham : Measurable a := ((hsum_meas.pow_const r).inv).ennreal_ofReal
  have hVm : Measurable (outCentred f i β) :=
    outCentred_measurable h.measurable_f h.measurable_iterate i β
  have hbm : Measurable b := (continuous_abs.measurable.comp hVm).ennreal_ofReal
  have hpt : ∀ x, A.indicator (fun x =>
      ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x ≤ A.indicator a x * b x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, ha, hb, div_eq_inv_mul,
        ENNReal.ofReal_mul' (abs_nonneg _)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hHolder := lintegral_indicator_mul_le (outMeasure f β) hA ham.aemeasurable hbm.aemeasurable
  -- negative moment
  have hR_meas : Measurable fun x : Fin n → ℝ =>
      ENNReal.ofReal ((∑ l ∈ Hᶜ, x l) ^ (-(4 * r : ℝ))) :=
    ((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).pow_const _).ennreal_ofReal
  have hX : ∫⁻ x, a x ^ (4 : ℝ) ∂(outMeasure f β) ≤
      ENNReal.ofReal (Wb ^ #H * (((#Hᶜ : ℕ) : ℝ) ^ (-(4 * r : ℝ)) *
        Real.exp (8 * E * (4 * r)))) := by
    calc ∫⁻ x, a x ^ (4 : ℝ) ∂(outMeasure f β)
        ≤ ∫⁻ x, ENNReal.ofReal ((∑ l ∈ Hᶜ, x l) ^ (-(4 * r : ℝ))) ∂(outMeasure f β) := by
          refine lintegral_mono_ae ((h.ae_pos β).mono fun x hx => ?_)
          have hR : 0 < ∑ l ∈ Hᶜ, x l := Finset.sum_pos (fun l _ => hx l) hHc
          have hRS : ∑ l ∈ Hᶜ, x l ≤ ∑ l, x l :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun l _ _ => (hx l).le
          have hS : 0 < ∑ l, x l := hR.trans_le hRS
          rw [ha]
          simp only
          rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (pow_nonneg hS.le r)) (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (((∑ l, x l) ^ r)⁻¹) ^ (4 : ℝ) = (∑ l, x l) ^ (-(4 * r : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_neg hS.le, ← Real.rpow_mul hS.le]
            ring_nf
          rw [e]
          exact Real.rpow_le_rpow_of_nonpos hR hRS
            (by have : (0 : ℝ) ≤ 4 * r := by positivity
                linarith)
      _ = (∏ l ∈ H, outMass f (β l)) * ∫⁻ x, ENNReal.ofReal ((∑ l ∈ Hᶜ, x l) ^ (-(4 * r : ℝ)))
            ∂(Measure.pi fun _ => (ν : Measure ℝ)) := by
          refine lintegral_outMeasure_eq_mul h.pos h.density β hR_meas fun x y hxy => ?_
          congr 2
          exact Finset.sum_congr rfl fun l hl => hxy l (Finset.mem_compl.mp hl)
      _ ≤ ENNReal.ofReal (Wb ^ #H) * ENNReal.ofReal ((((#Hᶜ : ℕ) : ℝ) ^ (-(4 * r : ℝ)) *
            Real.exp (8 * E * (4 * r)))) := by
          refine mul_le_mul' hM ?_
          exact lintegral_sum_rpow_neg_le h.measure_Iic (B := 8 * E) (by positivity)
            (fun q hq0 hq => by
              have := h.negMoment hq0 hq
              rwa [show 1 + 8 * E * q = 1 + 8 * E * q from rfl] at this)
            Hᶜ hHc (a := 4 * r) (by positivity) (by
              rw [hcard]
              have : (17 * r + 1 : ℕ) ≤ n := hn
              have h1 : ((n - #H : ℕ) : ℝ) = n - #H := by rw [Nat.cast_sub (by omega)]
              rw [h1]
              have h2 : (#H : ℝ) ≤ r := by exact_mod_cast hHr
              have h3 : ((17 * r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
              push_cast at h3
              linarith)
      _ = _ := (ENNReal.ofReal_mul (pow_nonneg hWb _)).symm
  -- centred sum
  have hV2 : ∀ x, b x ^ (2 : ℝ) = ENNReal.ofReal (outCentred f i β x ^ 2) := by
    intro x
    rw [hb]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
  have hZ : ∫⁻ x, b x ^ (2 : ℝ) ∂(outMeasure f β) ≤
      ENNReal.ofReal (Wb ^ #H * ((n : ℝ) ^ (i - ∑ l, β l) * (i : ℝ) ^ i * (i : ℝ) ^ i *
        J ^ (i - ∑ l, β l))) := by
    simp_rw [hV2]
    rw [lintegral_outMeasure_eq_mul h.pos h.density β ((hVm.pow_const 2).ennreal_ofReal)
      fun x y hxy => by rw [outCentred_indep i β x y hxy], ENNReal.ofReal_mul (pow_nonneg hWb _)]
    exact mul_le_mul' hM (lintegral_sq_outCentred_le hρm hρ2 hρ0 hρJ i β)
  have hYb := hY hHr
  -- combine
  have hx0 : 0 ≤ Wb ^ #H * (((#Hᶜ : ℕ) : ℝ) ^ (-(4 * r : ℝ)) * Real.exp (8 * E * (4 * r))) := by
    positivity
  have hy0 : 0 ≤ Wb ^ #H * Q := by positivity
  have hz0 : 0 ≤ Wb ^ #H * ((n : ℝ) ^ (i - ∑ l, β l) * (i : ℝ) ^ i * (i : ℝ) ^ i *
      J ^ (i - ∑ l, β l)) := by positivity
  have hcomb : ∫⁻ x, A.indicator (fun x =>
      ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x ∂(outMeasure f β) ≤
      ENNReal.ofReal ((Wb ^ #H * (((#Hᶜ : ℕ) : ℝ) ^ (-(4 * r : ℝ)) *
          Real.exp (8 * E * (4 * r)))) ^ (1 / 4 : ℝ) * (Wb ^ #H * Q) ^ (1 / 4 : ℝ) *
        (Wb ^ #H * ((n : ℝ) ^ (i - ∑ l, β l) * (i : ℝ) ^ i * (i : ℝ) ^ i *
          J ^ (i - ∑ l, β l))) ^ (1 / 2 : ℝ)) := by
    refine (lintegral_mono hpt).trans (hHolder.trans ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg hx0 (by norm_num),
      ← ENNReal.ofReal_rpow_of_nonneg hy0 (by norm_num),
      ← ENNReal.ofReal_rpow_of_nonneg hz0 (by norm_num)]
    gcongr
  refine hcomb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hn1 : 1 ≤ n := by omega
  have hNn : (n : ℝ) / 2 ≤ ((#Hᶜ : ℕ) : ℝ) := by
    rw [hcard, Nat.cast_sub (by omega)]
    have h2 : (#H : ℝ) ≤ r := by exact_mod_cast hHr
    have h3 : ((17 * r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h3
    linarith
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hHk : (n : ℝ) ^ #H * Real.sqrt n ^ (i - ∑ l, β l) ≤ Real.sqrt n ^ i := by
    have e1 : (n : ℝ) ^ #H = Real.sqrt n ^ (2 * #H) := by
      rw [pow_mul, Real.sq_sqrt (by positivity)]
    rw [e1, ← pow_add]
    exact pow_le_pow_right₀ hsq1 (by omega)
  have := term_real_le (r := r) (n := n) (i := i) (k := i - ∑ l, β l) (H := #H) (N := #Hᶜ)
    hWb hQ hJ0 hn1 hNn (by omega) hHk E
  simpa [outTermConst, hJdef] using this

theorem outTermConst_nonneg (r : ℕ) {E κ : ℝ} (i : ℕ) : 0 ≤ outTermConst r E κ i := by
  unfold outTermConst
  have : 0 ≤ max 1 (outFisher E κ) := le_trans zero_le_one (le_max_left _ _)
  positivity

theorem outLengthConst_nonneg (r : ℕ) (E κ : ℝ) : 0 ≤ outLengthConst r E κ :=
  Finset.sum_nonneg fun i _ => by
    have := outTermConst_nonneg r (E := E) (κ := κ) i
    positivity

/-- **The bound for one stopping length** (`output-closure.md` (O12)). -/
theorem perLength_bound (h : OutInput r E κ f ν) {n : ℕ} (hn : 17 * r + 1 ≤ n)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ c : ℝ, 0 < c → ∀ x, c • x ∈ A ↔ x ∈ A) {Q : ℝ} (hQ : 0 ≤ Q)
    (hY : ∀ β : Fin n → ℕ, (∀ l, β l ≤ r) → #(outSupp β) ≤ r → outMeasure f β A ≤
      ENNReal.ofReal (outWeightBound E κ ^ #(outSupp β) * Q)) (τ : ℝ) :
    |τ| ^ r * ‖∫ x, coneIntegrand A f τ x‖ ≤
      outLengthConst r E κ * (Real.sqrt n ^ r)⁻¹ * Q ^ (1 / 4 : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set Wb := outWeightBound E κ with hWbdef
  have hWb : 0 ≤ Wb := h.outWeightBound_nonneg
  have hn1 : 1 ≤ m + 1 := by omega
  have hrm : r ≤ m := by omega
  have henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|) :=
    fun a ha => h.env a (ha.trans (le_max_left r 1))
  have h1 := ofReal_cone_integral_le h.E_nonneg h.κpos hrm h.measurable_f h.zero h.continuous
    h.differentiable henv hA hcone τ
  have h2 := lintegral_coneWeight_le h.pos h.zero h.measurable_f h.measurable_iterate r hA
  have hQ4 : 0 ≤ Q ^ (1 / 4 : ℝ) := Real.rpow_nonneg hQ _
  have hsq1 : 1 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hsqpos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := by linarith
  have hfac : ∀ i ∈ range (r + 1), Real.sqrt ((m + 1 : ℕ) : ℝ) ^ i / ((m + 1 : ℕ) : ℝ) ^ r ≤ (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r)⁻¹ := by
    intro i hi
    have hi' : i ≤ r := by rw [Finset.mem_range] at hi; omega
    have e : ((m + 1 : ℕ) : ℝ) ^ r = Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r * Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    rw [e, div_le_iff₀ (by positivity), inv_mul_cancel_left₀ (by positivity)]
    exact pow_le_pow_right₀ hsq1 hi'
  set bnd : ℕ → (Fin (m + 1) → ℕ) → ℝ := fun i β => outTermConst r E κ i *
    (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ i / ((m + 1 : ℕ) : ℝ) ^ r) * Q ^ (1 / 4 : ℝ) * (Wb / ((m + 1 : ℕ) : ℝ)) ^ #(outSupp β) with hbnd
  have hbnd0 : ∀ i β, 0 ≤ bnd i β := fun i β => by
    have := outTermConst_nonneg r (E := E) (κ := κ) i
    simp only [hbnd]
    positivity
  have h3 : ∫⁻ x, coneWeight A f r x ≤ ENNReal.ofReal (∑ i ∈ range (r + 1), |outCoeff r i| *
      ∑ β ∈ outBox (m + 1) i, bnd i β) := by
    calc ∫⁻ x, coneWeight A f r x
        ≤ ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
            ∑ β ∈ outBox (m + 1) i, ∫⁻ x, A.indicator (fun x =>
              ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x ∂(outMeasure f β) := h2
      _ ≤ ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
            ∑ β ∈ outBox (m + 1) i, ENNReal.ofReal (bnd i β) := by
          refine Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (Finset.sum_le_sum fun β hβ => ?_)
          have hir : i ≤ r := by rw [Finset.mem_range] at hi; omega
          have hβr : ∀ l, β l ≤ r := by
            intro l
            have := (Fintype.mem_piFinset.mp hβ) l
            rw [Finset.mem_range] at this
            omega
          exact lintegral_term_le h hir hn β hA hQ (hY β hβr)
      _ = ENNReal.ofReal (∑ i ∈ range (r + 1), |outCoeff r i| * ∑ β ∈ outBox (m + 1) i, bnd i β) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun β _ => hbnd0 i β)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_sum_of_nonneg fun β _ => hbnd0 i β]
  have h4 : ∑ i ∈ range (r + 1), |outCoeff r i| * ∑ β ∈ outBox (m + 1) i, bnd i β ≤
      outLengthConst r E κ * (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r)⁻¹ * Q ^ (1 / 4 : ℝ) := by
    rw [outLengthConst, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hC := outTermConst_nonneg r (E := E) (κ := κ) i
    have hsum : ∑ β ∈ outBox (m + 1) i, bnd i β = outTermConst r E κ i *
        (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ i / ((m + 1 : ℕ) : ℝ) ^ r) * Q ^ (1 / 4 : ℝ) *
          ∑ β ∈ outBox (m + 1) i, (Wb / ((m + 1 : ℕ) : ℝ)) ^ #(outSupp β) := by
      rw [Finset.mul_sum]
    rw [hsum]
    have hbox := sum_outBox_le (n := m + 1) (i := i) hn1 hWb
    have hf := hfac i hi
    have hsn : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) ^ i / ((m + 1 : ℕ) : ℝ) ^ r := by positivity
    calc |outCoeff r i| * (outTermConst r E κ i * (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ i / ((m + 1 : ℕ) : ℝ) ^ r) *
          Q ^ (1 / 4 : ℝ) * ∑ β ∈ outBox (m + 1) i, (Wb / ((m + 1 : ℕ) : ℝ)) ^ #(outSupp β))
        ≤ |outCoeff r i| * (outTermConst r E κ i * (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r)⁻¹ *
            Q ^ (1 / 4 : ℝ) * Real.exp (i * Wb)) := by
          gcongr
      _ = _ := by ring
  have hfin := h1.trans (h3.trans (ENNReal.ofReal_le_ofReal h4))
  have hR0 : 0 ≤ outLengthConst r E κ * (Real.sqrt ((m + 1 : ℕ) : ℝ) ^ r)⁻¹ * Q ^ (1 / 4 : ℝ) := by
    have := outLengthConst_nonneg r E κ
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp hfin

end PGM
