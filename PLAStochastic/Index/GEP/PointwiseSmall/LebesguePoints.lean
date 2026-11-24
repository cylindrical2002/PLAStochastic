import PLAStochastic.Index.GEP.DirectTerm.OfRawDisc

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: Lebesgue points and the two-bump directions

* `pw_lebesgue_point`: if the averages of a locally bounded kernel `J` over `[x-h, x+h]` are within
  `E(x)` of a compensation `L(x,h)` with `L(x,h) → L₀(x)` as `h → 0⁺`, then `|J x - L₀ x| ≤ E x`
  for a.e. `x > 0` (Lebesgue differentiation, as in `affine_core`).
* `pw_affine_of_dir`: a kernel whose responses to all direction laws `SigmaLaw (1 + e^{5θσ/2}) θσ`
  are at most `δ` is a.e. affine up to `2δ / c(x)`, `c = dirC θσ`, with slope bounded by the size
  of the kernel on `[1/4, 5/2]` (the two-bump directions `exists_sigmaPair`).
* `pw_one_div_dirC_le`, `pw_log_sq_le_rpow`: the exponential form of `1/c(x)` and the absorption
  of `(1 + log ε)²` into a power `ε^a`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## Elementary bounds -/

/-- `(1 + log ε)² ≤ K_a ε^a` for `ε ≥ 1`, `a > 0`. -/
theorem pw_log_sq_le_rpow {a : ℝ} (ha : 0 < a) {eps : ℝ} (heps : 1 ≤ eps) :
    (1 + Real.log eps) ^ 2 ≤ 4 * max 1 (2 / a) ^ 2 * eps ^ a := by
  have heps0 : 0 < eps := by linarith
  set e' := eps ^ (a / 2) with he'
  have he'1 : 1 ≤ e' := Real.one_le_rpow heps (by positivity)
  have hlog : Real.log e' = a / 2 * Real.log eps := Real.log_rpow heps0 _
  have hl0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have h1 := one_add_log_sq_le he'1
  rw [hlog] at h1
  set m := max 1 (2 / a) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hma : 2 / a ≤ m := le_max_right _ _
  have hm0 : 0 < m := by linarith
  have h2 : 1 + Real.log eps ≤ m * (1 + a / 2 * Real.log eps) := by
    have : Real.log eps = 2 / a * (a / 2 * Real.log eps) := by field_simp
    have h3 : 2 / a * (a / 2 * Real.log eps) ≤ m * (a / 2 * Real.log eps) := by
      gcongr
    nlinarith
  have h4 : (1 + Real.log eps) ^ 2 ≤ m ^ 2 * (1 + a / 2 * Real.log eps) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : e' ≤ eps ^ a := by
    rw [he']
    exact Real.rpow_le_rpow_of_exponent_le heps (by linarith)
  calc (1 + Real.log eps) ^ 2 ≤ m ^ 2 * (1 + a / 2 * Real.log eps) ^ 2 := h4
    _ ≤ m ^ 2 * (4 * e') := by gcongr
    _ ≤ m ^ 2 * (4 * eps ^ a) := by gcongr
    _ = 4 * m ^ 2 * eps ^ a := by ring

/-- `1 / c(x) ≤ 2 e^{θσ} (1 + 1/θσ) e^{2 θσ x}`. -/
theorem pw_one_div_dirC_le {θσ x : ℝ} (hθσ : 0 < θσ) (hx : 0 < x) :
    1 / dirC θσ x ≤ 2 * Real.exp θσ * (1 + 1 / θσ) * Real.exp (2 * θσ * x) := by
  rw [one_div_dirC θσ hx, show θσ * (x + 1) = θσ * x + θσ by ring, Real.exp_add]
  have h := one_add_mul_exp_le hθσ hx.le
  calc 2 * (1 + x) * (Real.exp (θσ * x) * Real.exp θσ) =
        2 * Real.exp θσ * ((1 + x) * Real.exp (θσ * x)) := by ring
    _ ≤ 2 * Real.exp θσ * ((1 + 1 / θσ) * Real.exp (2 * θσ * x)) := by gcongr
    _ = 2 * Real.exp θσ * (1 + 1 / θσ) * Real.exp (2 * θσ * x) := by ring

/-- `(1 + x)² e^{θσ x} ≤ (1 + 1/θσ)² e^{4 θσ x}`. -/
theorem pw_sq_mul_exp_le {θσ x : ℝ} (hθσ : 0 < θσ) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (θσ * x) ≤ (1 + 1 / θσ) ^ 2 * Real.exp (4 * θσ * x) := by
  have h := one_add_mul_exp_le hθσ hx
  have h1 : Real.exp (θσ * x) ≤ Real.exp (θσ * x) ^ 2 := by
    have : 1 ≤ Real.exp (θσ * x) := Real.one_le_exp (by positivity)
    nlinarith
  have h2 : ((1 + x) * Real.exp (θσ * x)) ^ 2 ≤ ((1 + 1 / θσ) * Real.exp (2 * θσ * x)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have e : ((1 + 1 / θσ) * Real.exp (2 * θσ * x)) ^ 2 =
      (1 + 1 / θσ) ^ 2 * Real.exp (4 * θσ * x) := by
    rw [mul_pow, sq (Real.exp (2 * θσ * x)), ← Real.exp_add]
    ring_nf
  calc (1 + x) ^ 2 * Real.exp (θσ * x) ≤ (1 + x) ^ 2 * Real.exp (θσ * x) ^ 2 := by gcongr
    _ = ((1 + x) * Real.exp (θσ * x)) ^ 2 := by ring
    _ ≤ (1 + 1 / θσ) ^ 2 * Real.exp (4 * θσ * x) := by rw [← e]; exact h2

/-- The average of a bounded function is bounded. -/
theorem pw_abs_average_le {a b : ℝ} (hab : a < b) {J : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Icc a b, |J y| ≤ C) : |⨍ y in Icc a b, J y| ≤ C := by
  have := isProbabilityMeasure_unifM hab
  rw [← integral_unifM, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := unifM (Icc a b)) (f := J) (C := C)
    (by
      filter_upwards [ae_unifM_mem measurableSet_Icc] with y hy
      rw [Real.norm_eq_abs]; exact hC y hy)
  rwa [probReal_univ, mul_one] at h

/-! ## Lebesgue points -/

/-- **Lebesgue points**: from bounds on the averages over small balls to a.e. bounds. -/
theorem pw_lebesgue_point {J : ℝ → ℝ} (hJ : Measurable J) {B κ : ℝ}
    (hb : ∀ y, 0 ≤ y → |J y| ≤ B * Real.exp (κ * y)) {L : ℝ → ℝ → ℝ} {L₀ E : ℝ → ℝ}
    (hL : ∀ x, 0 < x → Tendsto (fun h => L x h) (𝓝[>] 0) (𝓝 (L₀ x)))
    (hloc : ∀ x, 0 < x → ∀ h, 0 < h → h < x → h ≤ 1 →
      |(⨍ y in Metric.closedBall x h, J y) - L x h| ≤ E x) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |J x - L₀ x| ≤ E x := by
  have hJl := locallyIntegrable_indicator_Ioi hJ hb
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) hJl 1
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hleb] with x hx hx0
  have hx0' : 0 < x := hx0
  have ht := hx (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id
    (eventually_nhdsWithin_of_forall fun j hj =>
      Metric.mem_closedBall_self (by rw [one_mul]; exact le_of_lt hj))
  have hJx : (Ioi (0 : ℝ)).indicator J x = J x := indicator_of_mem hx0 _
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |(⨍ y in Metric.closedBall x (id h),
      (Ioi (0 : ℝ)).indicator J y) - L x h| ≤ E x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (x / 2) 1 by positivity)] with h hh
    have hhx : h < x := lt_of_lt_of_le hh.2 ((min_le_left _ _).trans (by linarith))
    have hh1 : h ≤ 1 := hh.2.le.trans (min_le_right _ _)
    have hJI : (⨍ y in Metric.closedBall x (id h), (Ioi (0 : ℝ)).indicator J y) =
        ⨍ y in Metric.closedBall x h, J y := by
      refine setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
        (Eventually.of_forall fun y hy => ?_)
      have hy' : x - h ≤ y := by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
        simp only [id] at hy
        linarith [hy.1]
      exact indicator_of_mem (show y ∈ Ioi (0 : ℝ) from by
        show 0 < y; linarith) _
    rw [hJI]
    exact hloc x hx0' h hh.1 hhx hh1
  have hlim : Tendsto (fun h => |(⨍ y in Metric.closedBall x (id h),
      (Ioi (0 : ℝ)).indicator J y) - L x h|) (𝓝[>] (0 : ℝ))
      (𝓝 |(Ioi (0 : ℝ)).indicator J x - L₀ x|) := (ht.sub (hL x hx0')).abs
  rw [← hJx]
  exact le_of_tendsto hlim hev

/-! ## The two-bump directions -/

/-- **A.e. affine from the two-bump directions**: if the response of `J` to every direction law
`SigmaLaw (1 + e^{5θσ/2}) θσ` is at most `δ`, then `J` is a.e. affine up to `2δ / c(x)`. -/
theorem pw_affine_of_dir {θσ : ℝ} (hθσ : 0 < θσ) {J : ℝ → ℝ} (hJ : Measurable J) {B κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ y, 0 ≤ y → |J y| ≤ B * Real.exp (κ * y)) {ν : ProbabilityMeasure ℝ}
    {δ : ℝ}
    (hdir : ∀ σ : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * (5 / 2))) θσ σ →
      |∫ y, J y ∂(σ : Measure ℝ) - ∫ y, J y ∂(ν : Measure ℝ)| ≤ δ) :
    ∃ a' b' : ℝ, |b'| ≤ 2 * (|B| * Real.exp (κ * (5 / 2))) ∧
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |J x - (a' + b' * x)| ≤ 2 * δ / dirC θσ x := by
  set i₀ := ⨍ y in Icc (1 / 4 : ℝ) (3 / 4), J y with hi₀
  set i₁ := ⨍ y in Icc (3 / 2 : ℝ) (5 / 2), J y with hi₁
  set a' := (4 * i₀ - i₁) / 3 with ha'
  set b' := 2 * (i₁ - i₀) / 3 with hb'
  have hℓ : ∀ x, dirA x * i₀ + dirB x * i₁ = a' + b' * x := by
    intro x; simp only [dirA, dirB, ha', hb']; ring
  -- the size of the averages
  have hbd : ∀ y ∈ Icc (0 : ℝ) (5 / 2), |J y| ≤ |B| * Real.exp (κ * (5 / 2)) := by
    intro y hy
    refine (hb y hy.1).trans ?_
    calc B * Real.exp (κ * y) ≤ |B| * Real.exp (κ * y) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
      _ ≤ |B| * Real.exp (κ * (5 / 2)) := by
          gcongr
          exact hy.2
  have hi₀b : |i₀| ≤ |B| * Real.exp (κ * (5 / 2)) :=
    pw_abs_average_le (by norm_num) fun y hy => hbd y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hi₁b : |i₁| ≤ |B| * Real.exp (κ * (5 / 2)) :=
    pw_abs_average_le (by norm_num) fun y hy => hbd y ⟨by linarith [hy.1], hy.2⟩
  have hb'b : |b'| ≤ 2 * (|B| * Real.exp (κ * (5 / 2))) := by
    rw [hb']
    calc |2 * (i₁ - i₀) / 3| = 2 / 3 * |i₁ - i₀| := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (by norm_num : (0 : ℝ) < 3)]; ring
      _ ≤ 2 / 3 * (|i₁| + |i₀|) := by gcongr; exact abs_sub _ _
      _ ≤ 2 * (|B| * Real.exp (κ * (5 / 2))) := by linarith [abs_nonneg i₀, abs_nonneg i₁]
  refine ⟨a', b', hb'b, ?_⟩
  -- the averaged bound for small bumps
  have hloc : ∀ x, 0 < x → ∀ h, 0 < h → h < x → h ≤ 1 →
      |(⨍ y in Metric.closedBall x h, J y) - (a' + b' * x)| ≤ 2 * δ / dirC θσ x := by
    intro x hx h hh hhx hh1
    obtain ⟨σp, σm, hσp, hσm, hdiff⟩ := exists_sigmaPair hθσ hx hh hhx hh1
    obtain ⟨-, -, heq⟩ := hdiff J (integrableOn_Icc_of_exp hJ hκ hb (by linarith))
      (integrableOn_Icc_of_exp hJ hκ hb (by norm_num))
      (integrableOn_Icc_of_exp hJ hκ hb (by norm_num))
    have h1 := hdir σp hσp
    have h2 := hdir σm hσm
    have hc := dirC_pos θσ hx
    have h3 : |∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(σm : Measure ℝ)| ≤ 2 * δ := by
      calc |∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(σm : Measure ℝ)|
          = |(∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(ν : Measure ℝ)) -
              (∫ y, J y ∂(σm : Measure ℝ) - ∫ y, J y ∂(ν : Measure ℝ))| := by ring_nf
        _ ≤ |∫ y, J y ∂(σp : Measure ℝ) - ∫ y, J y ∂(ν : Measure ℝ)| +
              |∫ y, J y ∂(σm : Measure ℝ) - ∫ y, J y ∂(ν : Measure ℝ)| := abs_sub _ _
        _ ≤ 2 * δ := by linarith
    rw [heq, abs_mul, abs_of_pos hc] at h3
    rw [le_div_iff₀ hc]
    calc |(⨍ y in Metric.closedBall x h, J y) - (a' + b' * x)| * dirC θσ x
        = dirC θσ x * |(⨍ y in Metric.closedBall x h, J y) - dirA x * i₀ - dirB x * i₁| := by
          rw [← hℓ x, mul_comm]; ring_nf
      _ ≤ 2 * δ := h3
  exact pw_lebesgue_point hJ hb (L := fun x _ => a' + b' * x) (L₀ := fun x => a' + b' * x)
    (fun x _ => tendsto_const_nhds) hloc

end

end PGM
