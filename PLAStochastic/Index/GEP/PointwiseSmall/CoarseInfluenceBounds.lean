import PLAStochastic.Index.GEP.PointwiseSmall.SegmentFacts
import PLAStochastic.Index.GEP.PointwiseSmall.LebesguePoints

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: coarse bounds of the influences

* `pw_outJ_bound`: for output weights `η ≤ ηJ`, `J_φ = outJ` is measurable and
  `|J_φ x| ≤ M K ε⁴ e^{κ₀ x}` on `x ≥ 0` (kernel coarse bound, `KappaBound`, `J_C ≤ K ε⁴`,
  `C ≥ ε²/b₀`), homogeneous in `M`;
* `pw_lawJA_bound`: `J_A = J_C/C + (x-1)²/v` is measurable and `|J_A x| ≤ K ε⁴ e^{2x}`;
* `pw_rate_convert`: `ε^{-βU} (1 + log ε)² ≤ K ε^{-β}` with `β = (βU + 1/2)/2 < βU`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {D θ vlo vhi : ℝ}

/-- **The coarse bound of the output influence**, homogeneous in the size `M` of the test. -/
theorem pw_outJ_bound (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηJ κ₀ KJ' e0 : ℝ, 0 < ηJ ∧ 0 ≤ κ₀ ∧ 0 ≤ KJ' ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → ∀ M ψ, OutTest ηJ M ψ →
        Measurable (outJ eps ν ψ) ∧
          ∀ x, 0 ≤ x → |outJ eps ν ψ x| ≤ M * KJ' * eps ^ 4 * Real.exp (κ₀ * x) := by
  have hb0 : 0 < regB vhi := (regV_pos hvlo).trans_le (regV_le_regB hv)
  set b₀ : ℝ := 128 * regB vhi with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hker⟩ := pw_kernel_facts hD hθ hvlo hv
  obtain ⟨KJ, eJ, hKJ, -, hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  obtain ⟨ηk, hηk, Kk, ek, hkap⟩ := kappaBound D θ vlo vhi hD hθ hvlo hv
  set ηJ : ℝ := min (κ₁ / (2 * b₀)) ηk with hηJ
  have hηJ0 : 0 < ηJ := by positivity
  have hηJ1 : 2 * ηJ * b₀ ≤ κ₁ := by
    have h : ηJ ≤ κ₁ / (2 * b₀) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hηJk : ηJ ≤ ηk := min_le_right _ _
  set κ₀ : ℝ := 2 * ηJ * b₀ with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  set KJ' : ℝ := K₁ / ηJ + |Kk| * b₀ * KJ with hKJ'
  have hKJ'0 : 0 ≤ KJ' := by positivity
  refine ⟨ηJ, κ₀, KJ', max (max e₁ eJ) (max ek (epsZero (regB vhi) (regBeta D θ vlo))), hηJ0,
    hκ₀0, hKJ'0, he₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro eps heps ν hν
  have he₁' : e₁ ≤ eps := ((le_max_left _ _).trans (le_max_left _ _)).trans heps
  have heJ' : eJ ≤ eps := ((le_max_right _ _).trans (le_max_left _ _)).trans heps
  have hek' : ek ≤ eps := ((le_max_left _ _).trans (le_max_right _ _)).trans heps
  have hez : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans heps
  have heps1 : 1 ≤ eps := he₁.trans he₁'
  have heps0 : 0 < eps := by linarith
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  have he2 : (1 : ℝ) ≤ eps ^ 2 := one_le_pow₀ heps1
  obtain ⟨-, hCm, -⟩ := momClass_oneLayer (regV_pos hvlo) hez (hν.momClass hθ hvlo)
  rw [← hb₀] at hCm
  set C₀ := lawC eps ν with hC₀
  have hC0 : 0 < C₀ := lt_of_lt_of_le (by positivity) hCm
  obtain ⟨hJm, hJb, -⟩ := hJC eps heJ' ν hν
  -- the positive case
  have hpos : ∀ M ψ, 0 < M → OutTest ηJ M ψ → Measurable (outJ eps ν ψ) ∧
      ∀ x, 0 ≤ x → |outJ eps ν ψ x| ≤ M * KJ' * eps ^ 4 * Real.exp (κ₀ * x) := by
    intro M ψ hM hψ
    obtain ⟨hFm, hFκ⟩ := pw_normTest hψ hηJ0 hM hb₀0 heps0 hCm
    set Fh : ℝ → ℝ := fun y => testFn ψ (y / C₀) / (M / ηJ) with hFh
    set κ : ℝ := 2 * ηJ * b₀ / eps ^ 2 with hκ
    have hκ0 : 0 ≤ κ := by positivity
    have hκγ : κ * eps ^ 2 ≤ κ₁ := by
      rw [hκ, div_mul_cancel₀ _ heps2.ne']; exact hηJ1
    have hκκ₀ : κ ≤ κ₀ := by
      rw [hκ, hκ₀, div_le_iff₀ heps2]
      have : 0 ≤ 2 * ηJ * b₀ := by positivity
      nlinarith
    obtain ⟨hIm, hIb, -⟩ := hker eps he₁' ν hν κ hκ0 hκγ Fh hFm hFκ
    have hk0 : (0 : ℝ) < M / ηJ := by positivity
    have houtIns : outIns eps ν ψ =
        fun x => M / ηJ * insKernel eps ν (fun g => Fh (stopSum eps g)) x := by
      funext x
      exact pw_outIns_eq_mul eps ν ψ hk0.ne' x
    have hκb : |outKappa eps ν ψ| ≤ M * |Kk| := by
      have h := hkap eps hek' ν hν M ψ (hψ.mono_eta hηJk)
      exact h.trans (by gcongr; exact le_abs_self _)
    refine ⟨?_, fun x hx => ?_⟩
    · show Measurable fun x => outIns eps ν ψ x - outKappa eps ν ψ * (lawJC eps ν x / lawC eps ν)
      rw [houtIns]
      exact (hIm.const_mul _).sub ((hJm.div_const _).const_mul _)
    · have hex1 : 1 ≤ Real.exp (κ₀ * x) := Real.one_le_exp (by positivity)
      have hexκ : Real.exp (κ * x) ≤ Real.exp (κ₀ * x) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκκ₀ hx)
      have h1 : |outIns eps ν ψ x| ≤ M / ηJ * (K₁ * eps ^ 4 * Real.exp (κ₀ * x)) := by
        rw [houtIns]
        simp only
        rw [abs_mul, abs_of_pos hk0]
        gcongr
        exact (hIb x hx).trans (by gcongr)
      have h2 : |lawJC eps ν x / C₀| ≤ b₀ * KJ * eps ^ 4 := by
        rw [abs_div, abs_of_pos hC0, abs_of_nonneg (hJb x).1, div_le_iff₀ hC0]
        have h3 : eps ^ 2 ≤ b₀ * C₀ := by rw [div_le_iff₀ hb₀0] at hCm; linarith
        calc lawJC eps ν x ≤ KJ * eps ^ 4 := (hJb x).2
          _ = KJ * eps ^ 4 * 1 := (mul_one _).symm
          _ ≤ KJ * eps ^ 4 * (b₀ * C₀) := by gcongr; linarith
          _ = b₀ * KJ * eps ^ 4 * C₀ := by ring
      show |outIns eps ν ψ x - outKappa eps ν ψ * (lawJC eps ν x / C₀)| ≤ _
      calc |outIns eps ν ψ x - outKappa eps ν ψ * (lawJC eps ν x / C₀)|
          ≤ |outIns eps ν ψ x| + |outKappa eps ν ψ| * |lawJC eps ν x / C₀| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul]
        _ ≤ M / ηJ * (K₁ * eps ^ 4 * Real.exp (κ₀ * x)) + M * |Kk| * (b₀ * KJ * eps ^ 4) := by
            gcongr
        _ ≤ M / ηJ * (K₁ * eps ^ 4 * Real.exp (κ₀ * x)) +
            M * |Kk| * (b₀ * KJ * eps ^ 4) * Real.exp (κ₀ * x) := by
            have : 0 ≤ M * |Kk| * (b₀ * KJ * eps ^ 4) := by positivity
            have := mul_le_mul_of_nonneg_left hex1 this
            linarith
        _ = M * KJ' * eps ^ 4 * Real.exp (κ₀ * x) := by rw [hKJ']; ring
  intro M ψ hψ
  have hM := hψ.nonneg'
  rcases hM.eq_or_lt with hM0 | hMpos
  · subst hM0
    refine ⟨(hpos 1 ψ one_pos ⟨hψ.1, fun x hx => (hψ.2 x hx).trans (by
      rw [zero_mul]; positivity)⟩).1, fun x hx => ?_⟩
    rw [zero_mul, zero_mul, zero_mul]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set c : ℝ := KJ' * eps ^ 4 * Real.exp (κ₀ * x) with hc
    have hc0 : 0 ≤ c := by positivity
    have hε' : 0 < ε / (c + 1) := by positivity
    have hb := (hpos _ ψ hε' ⟨hψ.1, fun y hy => (hψ.2 y hy).trans (by
      rw [zero_mul]; positivity)⟩).2 x hx
    refine hb.trans ?_
    rw [zero_add, show ε / (c + 1) * KJ' * eps ^ 4 * Real.exp (κ₀ * x) = ε * c / (c + 1) by
      rw [hc]; ring, div_le_iff₀ (by positivity)]
    linarith only [hε]
  · exact hpos M ψ hMpos hψ

/-- **The coarse bound of `J_A`**: `|J_A x| ≤ K ε⁴ e^{2x}`. -/
theorem pw_lawJA_bound (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ KA' e0 : ℝ, 0 ≤ KA' ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        Measurable (lawJA eps ν) ∧
          ∀ x, 0 ≤ x → |lawJA eps ν x| ≤ KA' * eps ^ 4 * Real.exp (2 * x) := by
  have hb0 : 0 < regB vhi := (regV_pos hvlo).trans_le (regV_le_regB hv)
  set b₀ : ℝ := 128 * regB vhi with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  obtain ⟨KJ, eJ, hKJ, heJ, hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  refine ⟨KJ * b₀ + 1 / vlo, max eJ (epsZero (regB vhi) (regBeta D θ vlo)), by positivity,
    heJ.trans (le_max_left _ _), ?_⟩
  intro eps heps ν hν
  have heJ' : eJ ≤ eps := (le_max_left _ _).trans heps
  have hez : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps := (le_max_right _ _).trans heps
  have heps1 : 1 ≤ eps := heJ.trans heJ'
  have heps0 : 0 < eps := by linarith
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  obtain ⟨-, hCm, -⟩ := momClass_oneLayer (regV_pos hvlo) hez (hν.momClass hθ hvlo)
  rw [← hb₀] at hCm
  have hC0 : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hCm
  have hv0 : 0 < lawVar ν := hvlo.trans_le hν.var_ge
  obtain ⟨hJm, hJb, -⟩ := hJC eps heJ' ν hν
  refine ⟨?_, fun x hx => ?_⟩
  · show Measurable fun x => lawJC eps ν x / lawC eps ν + (x - 1) ^ 2 / lawVar ν
    exact (hJm.div_const _).add (((measurable_id.sub measurable_const).pow_const 2).div_const _)
  · have hex : (1 + x) ^ 2 ≤ Real.exp (2 * x) := by
      have h := Real.add_one_le_exp x
      have e : Real.exp (2 * x) = Real.exp x ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hex1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    have h1 : |lawJC eps ν x / lawC eps ν| ≤ KJ * b₀ * eps ^ 4 := by
      rw [abs_div, abs_of_pos hC0, abs_of_nonneg (hJb x).1, div_le_iff₀ hC0]
      have h3 : eps ^ 2 ≤ b₀ * lawC eps ν := by rw [div_le_iff₀ hb₀0] at hCm; linarith
      have he2 : (1 : ℝ) ≤ eps ^ 2 := one_le_pow₀ heps1
      calc lawJC eps ν x ≤ KJ * eps ^ 4 := (hJb x).2
        _ = KJ * eps ^ 4 * 1 := (mul_one _).symm
        _ ≤ KJ * eps ^ 4 * (b₀ * lawC eps ν) := by gcongr; linarith
        _ = KJ * b₀ * eps ^ 4 * lawC eps ν := by ring
    have h2 : |(x - 1) ^ 2 / lawVar ν| ≤ 1 / vlo * Real.exp (2 * x) := by
      rw [abs_div, abs_of_pos hv0, abs_of_nonneg (sq_nonneg _), div_le_iff₀ hv0]
      have h4 : (x - 1) ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
      calc (x - 1) ^ 2 ≤ Real.exp (2 * x) := h4.trans hex
        _ = 1 / vlo * Real.exp (2 * x) * vlo := by field_simp
        _ ≤ 1 / vlo * Real.exp (2 * x) * lawVar ν := by gcongr; exact hν.var_ge
    have he4 : (1 : ℝ) ≤ eps ^ 4 := one_le_pow₀ heps1
    show |lawJC eps ν x / lawC eps ν + (x - 1) ^ 2 / lawVar ν| ≤ _
    calc |lawJC eps ν x / lawC eps ν + (x - 1) ^ 2 / lawVar ν|
        ≤ |lawJC eps ν x / lawC eps ν| + |(x - 1) ^ 2 / lawVar ν| := abs_add_le _ _
      _ ≤ KJ * b₀ * eps ^ 4 + 1 / vlo * Real.exp (2 * x) := add_le_add h1 h2
      _ ≤ KJ * b₀ * eps ^ 4 * Real.exp (2 * x) + 1 / vlo * eps ^ 4 * Real.exp (2 * x) := by
          have a1 : KJ * b₀ * eps ^ 4 ≤ KJ * b₀ * eps ^ 4 * Real.exp (2 * x) := by
            have : 0 ≤ KJ * b₀ * eps ^ 4 := by positivity
            nlinarith
          have a2 : 1 / vlo * Real.exp (2 * x) ≤ 1 / vlo * eps ^ 4 * Real.exp (2 * x) := by
            have : 0 ≤ 1 / vlo * Real.exp (2 * x) := by positivity
            nlinarith
          linarith
      _ = (KJ * b₀ + 1 / vlo) * eps ^ 4 * Real.exp (2 * x) := by ring

/-- **The rate conversion**: `ε^{-βU} (1 + log ε)² ≤ K ε^{-β}`, `β = (βU + 1/2)/2`. -/
theorem pw_rate_convert {βU : ℝ} (hβU : 1 / 2 < βU) :
    ∃ Kr : ℝ, 0 ≤ Kr ∧ ∀ eps : ℝ, 1 ≤ eps →
      eps ^ (-βU) * (1 + Real.log eps) ^ 2 ≤ Kr * eps ^ (-((βU + 1 / 2) / 2)) := by
  set a : ℝ := (βU - 1 / 2) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  refine ⟨4 * max 1 (2 / a) ^ 2, by positivity, fun eps heps => ?_⟩
  have heps0 : 0 < eps := by linarith
  have h := pw_log_sq_le_rpow ha0 heps
  have e : eps ^ (-βU) * eps ^ a = eps ^ (-((βU + 1 / 2) / 2)) := by
    rw [← Real.rpow_add heps0]
    congr 1
    rw [ha]; ring
  calc eps ^ (-βU) * (1 + Real.log eps) ^ 2 ≤ eps ^ (-βU) * (4 * max 1 (2 / a) ^ 2 * eps ^ a) := by
        gcongr
    _ = 4 * max 1 (2 / a) ^ 2 * (eps ^ (-βU) * eps ^ a) := by ring
    _ = 4 * max 1 (2 / a) ^ 2 * eps ^ (-((βU + 1 / 2) / 2)) := by rw [e]

end

end PGM
