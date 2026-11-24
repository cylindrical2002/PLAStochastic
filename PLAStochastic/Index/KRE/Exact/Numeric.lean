import PLAStochastic.Index.KRE.Exact.Window

/-! # HEIGHT supplies all numerical conditions for the exact formula -/

namespace PGM
noncomputable section
open Filter Topology

structure KRENumeric (A : ℝ) (n : ℕ) (eps : ℝ) : Prop where
  n_two : 2 ≤ n
  eps_one : 1 < eps
  log_n_one : 1 ≤ Real.log n
  rho : A ≤ 2 * Real.log eps
  growth : 3 * Real.log eps + 2 * Real.log (Real.log n) ≤ Real.log n
  big : 102400 * Real.log n ≤ (n : ℝ)
  q_one : 1 < Real.log n / (6 * Real.log eps) + 1 / 2
  window_one : greW (1000 * A) n eps ≤ 1
  separation : 10 * A ≤ greW (1000 * A) n eps / 16 * (2 * Real.log eps)
  margin : A * (2 : ℝ) ^ Nat.ceil (kreZ n eps) + 4 / 3 * Real.log (Real.log n) ≤
    greW (1000 * A) n eps / 16 * (2 * Real.log eps) * (2 : ℝ) ^ Nat.ceil (kreZ n eps)

theorem kre_q_identity {n : ℕ} {eps : ℝ} (he : 1 < eps) :
    Real.log n + 3 * Real.log eps = 3 * (2 * Real.log eps) *
      (Real.log n / (6 * Real.log eps) + 1 / 2) := by
  have h : Real.log eps ≠ 0 := (Real.log_pos he).ne'
  field_simp
  ring

theorem eventually_KRENumeric {A : ℝ} (hA : 1 ≤ A) {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεN : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, KRENumeric A (N k) (ε k) := by
  have hL := Real.tendsto_log_atTop.comp hN
  have hE := Real.tendsto_log_atTop.comp hε
  have hw := tendsto_greW (1000 * A) hN hε
  filter_upwards [hN.eventually_ge_atTop 2, hε.eventually_gt_atTop 1,
    hL.eventually_ge_atTop 1, hE.eventually_ge_atTop A,
    hεN.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12)),
    hL.eventually (eventually_mul_log_pow_le_rpow 8 1 one_pos),
    hN.eventually (eventually_mul_log_pow_le_rpow 102400 1 one_pos),
    hw.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hn he hY hEA hratio hlogY hbig hw1
  rw [pow_one, Real.rpow_one] at hlogY hbig
  let n := N k
  let eps := ε k
  let Y := Real.log n
  let e := Real.log eps
  let q := Y / (6 * e) + 1 / 2
  let u := (2 : ℝ) ^ Nat.ceil (Real.logb 2 q)
  let w := greW (1000 * A) n eps
  change 1 ≤ Y at hY
  change A ≤ e at hEA
  change 8 * Real.log Y ≤ Y at hlogY
  have hAp : 0 < A := by linarith
  have hYp : 0 < Y := by linarith
  have hep : 0 < e := Real.log_pos he
  have hle : e ≤ Y / 12 := by
    change e / Y ≤ 1 / 12 at hratio
    rw [div_le_iff₀ hYp] at hratio
    linarith
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hq : 1 < q := by
    dsimp [q]
    have h2 : 2 ≤ Y / (6 * e) := (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith
  have hqp : 0 < q := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hqu : q ≤ u := by
    apply (Real.logb_le_logb one_lt_two hqp hu).mp
    dsimp [u]
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
    exact Nat.le_ceil _
  have hqeq : Y + 3 * e = 3 * (2 * e) * q := kre_q_identity he
  have hw0 : 0 ≤ w := by dsimp [w, greW]; positivity
  have hwe : 1000 * A ≤ w * e := by
    have heq : w * e = 1000 * A + 1000 * A * (Real.log Y / Y) * e := by
      change (1000 * A) * (1 / e + Real.log Y / Y) * e = _
      field_simp [hep.ne', hYp.ne']
    rw [heq]
    have : 0 ≤ 1000 * A * (Real.log Y / Y) * e := by positivity
    linarith
  have hwY : 1000 * A * Real.log Y ≤ w * Y := by
    have heq : w * Y = 1000 * A * (Y / e) + 1000 * A * Real.log Y := by
      change (1000 * A) * (1 / e + Real.log Y / Y) * Y = _
      field_simp [hep.ne', hYp.ne']
    rw [heq]
    have : 0 ≤ 1000 * A * (Y / e) := by positivity
    linarith
  have hsep : 10 * A ≤ w / 16 * (2 * e) := by nlinarith
  have hsep2 : 2 * A ≤ w / 16 * (2 * e) := by nlinarith
  have hpart1 := mul_le_mul_of_nonneg_right hsep2 hu.le
  have hYu : Y ≤ 3 * (2 * e) * u := by
    have := mul_le_mul_of_nonneg_left hqu (show 0 ≤ 3 * (2 * e) by positivity)
    linarith
  have hmult := mul_le_mul_of_nonneg_left hYu hw0
  have hAlog := mul_le_mul_of_nonneg_right hA hlogY0
  have hpart2 : 8 / 3 * Real.log Y ≤ w / 16 * (2 * e) * u := by
    nlinarith
  refine ⟨by exact_mod_cast hn, he, hY, by change A ≤ 2 * e; linarith,
    ?_, hbig, hq, hw1, hsep, ?_⟩
  · change 3 * e + 2 * Real.log Y ≤ Y
    change 8 * Real.log Y ≤ Y at hlogY
    linarith
  · change A * u + 4 / 3 * Real.log Y ≤ w / 16 * (2 * e) * u
    nlinarith

end
end PGM
