import PLAStochastic.Swing.Entrance.Brownian.PinchStructure

/-!
# Tent-bump invariance of the entrance pinch (E24)

The tent bump is `h_r(t) = min(t, r - t)_+`; it vanishes outside `(0, r)` and is bounded by
`r / 2`. Let `f` be a continuous path with `f 0 = 0` whose first pinch `σ` is finite and
positive, with slope `m_*` and sign `s`. If `0 < r < σ` and `|f t - m_* t| < 1/2` on `[0, r]`,
then for every `|z| < 1/r` the path `f + z h_r` has the same pinch, slope and sign, and its signed
area moves affinely: `I(f + z h_r) = I(f) + s z c_r` with `c_r = ∫_0^r t h_r(t) dt > 0`.

The proof is deterministic. The perturbed and the original path agree on `[r, ∞)`, and on `[0, r]`
both keep the slope `m_*` strictly inside the band. Uniqueness of a feasible slope therefore
transfers between the two paths on every horizon, by mixing slopes with `m_*`.
-/

open MeasureTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

/-- The tent bump `h_r(t) = min(t, r - t)_+`. -/
def tentBump (r : ℝ) : C(ℝ, ℝ) := ⟨fun t => max 0 (min t (r - t)), by fun_prop⟩

@[simp] theorem tentBump_apply (r t : ℝ) : tentBump r t = max 0 (min t (r - t)) := rfl

theorem tentBump_nonneg (r t : ℝ) : 0 ≤ tentBump r t := le_max_left _ _

theorem tentBump_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : tentBump r t ≤ r / 2 := by
  rw [tentBump_apply]
  apply max_le (by linarith)
  rcases le_total t (r / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem tentBump_of_le {r t : ℝ} (h : r ≤ t) : tentBump r t = 0 := by
  rw [tentBump_apply]
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem tentBump_of_nonpos (r : ℝ) {t : ℝ} (h : t ≤ 0) : tentBump r t = 0 := by
  rw [tentBump_apply]
  exact max_eq_left ((min_le_left _ _).trans h)

theorem tentBump_pos {r t : ℝ} (h0 : 0 < t) (hr : t < r) : 0 < tentBump r t := by
  rw [tentBump_apply]
  exact lt_max_of_lt_right (lt_min h0 (by linarith))

/-- The first moment `c_r = ∫_0^r t h_r(t) dt` of the tent bump. -/
def tentArea (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, t * tentBump r t

theorem tentArea_pos {r : ℝ} (hr : 0 < r) : 0 < tentArea r :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_id.mul (tentBump r).continuous).intervalIntegrable _ _)
    (fun _ ht => mul_pos ht.1 (tentBump_pos ht.1 ht.2)) hr

/-- **E24.** Under the small-start condition at a time `r` before the pinch, a tent bump of
amplitude `|z| < 1/r` leaves the pinch, slope and sign unchanged and moves the signed area
affinely, with slope `s c_r`. -/
theorem entrance_tent_invariance {f : C(ℝ, ℝ)} (hf : f 0 = 0) {r : ℝ} (hr : 0 < r)
    (hrσ : r < entrancePinch f)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) r, |f t - entranceSlope f * t| < 1 / 2)
    {z : ℝ} (hz : |z| < 1 / r) :
    entrancePinch (f + z • tentBump r) = entrancePinch f ∧
      entranceSlope (f + z • tentBump r) = entranceSlope f ∧
      entranceSign (f + z • tentBump r) = entranceSign f ∧
      entranceArea (f + z • tentBump r) =
        entranceArea f + entranceSign f * z * tentArea r := by
  set g := f + z • tentBump r with hgdef
  set σ := entrancePinch f with hσdef
  set m := entranceSlope f with hmdef
  have hσ : 0 < σ := hr.trans hrσ
  have hf' : |f 0| < 1 := by rw [hf, abs_zero]; exact one_pos
  have hgapp : ∀ t, g t = f t + z * tentBump r t := fun t => rfl
  have hg0 : g 0 = 0 := by rw [hgapp, hf, tentBump_of_nonpos r le_rfl]; ring
  have hg' : |g 0| < 1 := by rw [hg0, abs_zero]; exact one_pos
  have hgfar : ∀ t, r ≤ t → g t = f t := by
    intro t ht
    rw [hgapp, tentBump_of_le ht]
    ring
  obtain ⟨-, hbefore, hfeas, huniq⟩ := entrancePinch_spec hf' hσ
  -- a uniform bound `ρ < 1/2` on `[0, r]`
  obtain ⟨ρ, hρ, hρbound⟩ : ∃ ρ < 1 / 2, ∀ t ∈ Icc (0 : ℝ) r, |f t - m * t| ≤ ρ := by
    obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hr.le)
      (by fun_prop : Continuous (fun t => |f t - m * t|)).continuousOn
    exact ⟨_, hsmall t₀ ht₀, fun t ht => hmax ht⟩
  set ρ' := ρ + |z| * (r / 2) with hρ'def
  have hzr : |z| * r < 1 := by rwa [lt_div_iff₀ hr] at hz
  have hρ' : ρ' < 1 := by rw [hρ'def]; linarith
  have hgbound : ∀ t ∈ Icc (0 : ℝ) r, |g t - m * t| ≤ ρ' := by
    intro t ht
    rw [hgapp]
    calc |f t + z * tentBump r t - m * t| = |(f t - m * t) + z * tentBump r t| := by
          congr 1
          ring
      _ ≤ |f t - m * t| + |z * tentBump r t| := abs_add_le _ _
      _ ≤ ρ + |z| * (r / 2) := by
          rw [abs_mul, abs_of_nonneg (tentBump_nonneg r t)]
          exact add_le_add (hρbound t ht)
            (mul_le_mul_of_nonneg_left (tentBump_le hr.le t) (abs_nonneg z))
  -- `m` stays feasible for the perturbed path on `[0, σ]`
  have hgfeas : continuousSlopeFeasible g 0 1 σ m := by
    intro t
    by_cases htr : (t : ℝ) ≤ r
    · have h1 := hgbound t ⟨t.property.1, htr⟩
      rw [sub_zero]
      linarith
    · rw [hgfar t (le_of_not_ge htr)]
      exact hfeas t
  -- every slope feasible for the perturbed path on `[0, σ]` is `m`
  have hguniq : ∀ b, continuousSlopeFeasible g 0 1 σ b → b = m := by
    intro b hb
    refine eq_of_mix_unique (by linarith : ρ < 1) (fun t => t ≤ r) hfeas huniq ?_ ?_
    · intro t ht
      rw [sub_zero]
      exact hρbound t ⟨t.property.1, ht⟩
    · intro t ht
      rw [← hgfar t (le_of_not_ge ht)]
      exact hb t
  set σN := σ.toNNReal with hσNdef
  have hσN : (σN : ℝ) = σ := Real.coe_toNNReal _ hσ.le
  have hreach_le : entranceReach g ≤ σN := by
    apply (entranceReach_le_iff g σN).mpr
    by_contra hlt
    push Not at hlt
    obtain ⟨a, ham, ha⟩ := exists_ne_feasible_of_error_lt g hlt m
    rw [hσN] at ha
    exact ham (hguniq a ha)
  have hreach_ge : (σN : ℝ≥0∞) ≤ entranceReach g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T', hT'⟩ : ∃ T' : ℝ≥0, (T' : ℝ≥0∞) = entranceReach g :=
      ⟨(entranceReach g).toNNReal, ENNReal.coe_toNNReal (ne_top_of_lt hlt)⟩
    have hT'σN : T' < σN := by
      rw [← hT'] at hlt
      exact_mod_cast hlt
    have hT'σ : (T' : ℝ) < σ := by
      rw [← hσN]
      exact_mod_cast hT'σN
    have hD0 : (fun t : ℝ≥0 => anchoredTimeError g t) 0 < 1 := by
      simpa [anchoredTimeError_zero] using hg'
    have herrg : anchoredTimeError g T' = 1 :=
      error_at_firstReach (anchoredTimeError_nnreal_monotone g)
        ((continuous_anchoredTimeError g).comp continuous_subtype_val) hD0 hT'.symm
    have hgfeasT : continuousSlopeFeasible g 0 1 T' m :=
      fun t => hgfeas ⟨t, t.property.1, t.property.2.trans hT'σ.le⟩
    have herrI : anchoredError (intervalPath g T') = 1 :=
      (anchoredTimeError_eq_interval T'.property g).symm.trans herrg
    have hzeroI : |intervalPath g T' ⟨0, le_rfl, T'.property⟩| < 1 := hg'
    have hguniqT : ∀ b, continuousSlopeFeasible g 0 1 T' b → b = m := by
      intro b hb
      have h1 := anchored_feasible_slope_unique T'.property one_pos (intervalPath g T') hzeroI
        herrI (a := b) (b := m) (fun t => by have h2 := hb t; rwa [sub_zero] at h2)
        (fun t => by have h2 := hgfeasT t; rwa [sub_zero] at h2)
      exact h1
    have hfuniqT : ∀ b, continuousSlopeFeasible f 0 1 T' b → b = m := by
      intro b hb
      refine eq_of_mix_unique hρ' (fun t => t ≤ r) hgfeasT hguniqT ?_ ?_
      · intro t ht
        rw [sub_zero]
        exact hgbound t ⟨t.property.1, ht⟩
      · intro t ht
        rw [hgfar t (le_of_not_ge ht)]
        exact hb t
    obtain ⟨a, ham, ha⟩ := exists_ne_feasible_of_error_lt f (hbefore T' hT'σ) m
    exact ham (hfuniqT a ha)
  have hreach : entranceReach g = σN := le_antisymm hreach_le hreach_ge
  have hpinch : entrancePinch g = σ := by
    rw [entrancePinch, firstContinuousConePinch_eq_entranceReach hg', hreach,
      ENNReal.coe_toReal, hσN]
  have hslope : entranceSlope g = m := by
    rw [entranceSlope, hpinch]
    exact (continuousCone_eq_of_unique hσ hgfeas hguniq).1
  have hsign : entranceSign g = entranceSign f := by
    rw [entranceSign, entranceSign, hpinch, hslope, hgfar σ hrσ.le]
  refine ⟨hpinch, hslope, hsign, ?_⟩
  have hint : ∫ t in (0 : ℝ)..σ, t * (g t - m * t) =
      (∫ t in (0 : ℝ)..σ, t * (f t - m * t)) + z * tentArea r := by
    have h1 : ∀ t, t * (g t - m * t) = t * (f t - m * t) + z * (t * tentBump r t) := by
      intro t
      rw [hgapp]
      ring
    simp_rw [h1]
    have hc1 : Continuous (fun t => t * (f t - m * t)) := by fun_prop
    have hc2 : Continuous (fun t => t * tentBump r t) := by fun_prop
    rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
      ((hc2.const_mul z).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    congr 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r)
      (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    have hzero : ∫ t in r..σ, t * tentBump r t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · exact intervalIntegral.integral_zero
      · intro t ht
        rw [uIcc_of_le hrσ.le] at ht
        simp only [tentBump_of_le ht.1, mul_zero]
    rw [hzero, add_zero]
    rfl
  rw [entranceArea, entranceArea, hpinch, hslope, hsign, hint]
  ring

end

end SwingRepair
