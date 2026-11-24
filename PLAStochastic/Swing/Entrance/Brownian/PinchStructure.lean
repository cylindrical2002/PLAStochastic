import PLAStochastic.Swing.Entrance.Defs

/-!
# Deterministic structure of the entrance pinch

For a continuous path `f` with `|f 0| < 1`, the literal first cone pinch with tolerance `1`
equals the first time the anchored fitting error reaches `1`. When this pinch `σ` is finite and
positive, the error equals `1` at `σ` and is below `1` before it, the lower cone endpoint
`m_* = entranceSlope f` is the unique feasible slope on `[0, σ]`, and the terminal residual
`f σ - m_* σ` equals `1` or `-1`.

All arguments are deterministic. They rest on one convexity device: a slope that is feasible
outside a region where `m_*` keeps a uniform slack can be mixed with `m_*` into a feasible slope
different from `m_*`.
-/

open MeasureTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

theorem offsetPath_zero (f : C(ℝ, ℝ)) : offsetPath f 0 = f := by
  ext t
  simp

/-- The first time the anchored fitting error of `f` reaches the tolerance `1`. -/
def entranceReach (f : C(ℝ, ℝ)) : ℝ≥0∞ :=
  firstReach (fun t : ℝ≥0 => anchoredTimeError f t) 1

theorem entranceReach_le_iff (f : C(ℝ, ℝ)) (T : ℝ≥0) :
    entranceReach f ≤ (T : ℝ≥0∞) ↔ 1 ≤ anchoredTimeError f T :=
  firstReach_le_iff (anchoredTimeError_nnreal_monotone f)
    ((continuous_anchoredTimeError f).comp continuous_subtype_val) T

theorem entranceReach_pos {f : C(ℝ, ℝ)} (hf : |f 0| < 1) : 0 < entranceReach f := by
  apply lt_of_not_ge
  intro h
  have h0 : entranceReach f ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simpa using h
  have h1 := (entranceReach_le_iff f 0).mp h0
  rw [NNReal.coe_zero, anchoredTimeError_zero] at h1
  linarith

/-- The literal first cone pinch is the first time the anchored error reaches `1`. -/
theorem firstContinuousConePinch_eq_entranceReach {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    firstContinuousConePinch f 0 1 = entranceReach f := by
  apply le_antisymm
  · rcases eq_top_or_lt_top (entranceReach f) with h | h
    · rw [h]
      exact le_top
    · obtain ⟨σ, hσ⟩ : ∃ σ : ℝ≥0, (σ : ℝ≥0∞) = entranceReach f :=
        ⟨(entranceReach f).toNNReal, ENNReal.coe_toNNReal h.ne⟩
      have hpos : 0 < σ := by
        have h1 := entranceReach_pos hf
        rw [← hσ] at h1
        exact ENNReal.coe_pos.mp h1
      have h' : firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath f 0) t) 1 = σ := by
        rw [offsetPath_zero]
        exact hσ.symm
      rw [firstContinuousConePinch_eq_firstReach f (by simpa using hf) hpos h', hσ]
  · apply le_iInf
    intro T
    split_ifs with hT
    · apply (entranceReach_le_iff f T).mpr
      by_contra hlt
      push Not at hlt
      have hlt' : anchoredTimeError (offsetPath f 0) T < 1 := by rwa [offsetPath_zero]
      exact (continuousCone_lt_of_error_lt f 0 hT.1 hlt').ne hT.2
    · exact le_top

/-! ## Mixing slopes -/

/-- If `m` is feasible and has slack `ρ < 1` on the region `P`, and `a` is feasible off `P`,
then a proper convex mixture of `m` and `a` is feasible. -/
theorem exists_mix_feasible {f : ℝ → ℝ} {T m a ρ : ℝ} (hρ : ρ < 1) (P : ℝ → Prop)
    (hm : continuousSlopeFeasible f 0 1 T m)
    (hslack : ∀ t : Icc (0 : ℝ) T, P t → |f t - 0 - m * t| ≤ ρ)
    (ha : ∀ t : Icc (0 : ℝ) T, ¬ P t → |f t - 0 - a * t| ≤ 1) :
    ∃ l : ℝ, 0 < l ∧ continuousSlopeFeasible f 0 1 T (m + l * (a - m)) := by
  set K := |a - m| * |T| + 1 with hK
  have hKpos : 0 < K := by positivity
  set l := min 1 ((1 - ρ) / K) with hl
  have hlpos : 0 < l := lt_min one_pos (div_pos (by linarith) hKpos)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hlK : l * K ≤ 1 - ρ := by
    calc l * K ≤ (1 - ρ) / K * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hKpos.le
      _ = 1 - ρ := div_mul_cancel₀ _ hKpos.ne'
  refine ⟨l, hlpos, fun t => ?_⟩
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have htT : (t : ℝ) ≤ |T| := t.property.2.trans (le_abs_self T)
  by_cases hP : P t
  · have h1 := hslack t hP
    have h2 : |l * (a - m) * t| ≤ l * K := by
      rw [abs_mul, abs_mul, abs_of_pos hlpos, abs_of_nonneg ht0, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hlpos.le
      have := mul_le_mul_of_nonneg_left htT (abs_nonneg (a - m))
      linarith
    calc |f t - 0 - (m + l * (a - m)) * t| = |(f t - 0 - m * t) - l * (a - m) * t| := by
          congr 1
          ring
      _ ≤ |f t - 0 - m * t| + |l * (a - m) * t| := abs_sub _ _
      _ ≤ ρ + l * K := add_le_add h1 h2
      _ ≤ 1 := by linarith
  · have h1 := hm t
    have h2 := ha t hP
    calc |f t - 0 - (m + l * (a - m)) * t| =
          |(1 - l) * (f t - 0 - m * t) + l * (f t - 0 - a * t)| := by
          congr 1
          ring
      _ ≤ |(1 - l) * (f t - 0 - m * t)| + |l * (f t - 0 - a * t)| := abs_add_le _ _
      _ = (1 - l) * |f t - 0 - m * t| + l * |f t - 0 - a * t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - l), abs_of_pos hlpos]
      _ ≤ (1 - l) * 1 + l * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h1 (by linarith)
          · exact mul_le_mul_of_nonneg_left h2 hlpos.le
      _ = 1 := by ring

/-- A slope feasible off a slack region of the unique feasible slope `m` equals `m`. -/
theorem eq_of_mix_unique {f : ℝ → ℝ} {T m a ρ : ℝ} (hρ : ρ < 1) (P : ℝ → Prop)
    (hm : continuousSlopeFeasible f 0 1 T m)
    (huniq : ∀ b, continuousSlopeFeasible f 0 1 T b → b = m)
    (hslack : ∀ t : Icc (0 : ℝ) T, P t → |f t - 0 - m * t| ≤ ρ)
    (ha : ∀ t : Icc (0 : ℝ) T, ¬ P t → |f t - 0 - a * t| ≤ 1) : a = m := by
  obtain ⟨l, hl, hfeas⟩ := exists_mix_feasible hρ P hm hslack ha
  have h := huniq _ hfeas
  have h0 : l * (a - m) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hl.ne'
  · linarith

/-- An anchored error below `1` leaves a feasible slope different from any given one. -/
theorem exists_ne_feasible_of_error_lt (f : C(ℝ, ℝ)) {T : ℝ≥0}
    (h : anchoredTimeError f T < 1) (m : ℝ) :
    ∃ a, a ≠ m ∧ continuousSlopeFeasible f 0 1 T a := by
  rcases eq_zero_or_pos T with hT | hT
  · subst hT
    refine ⟨m + 1, by linarith, fun t => ?_⟩
    have ht : (t : ℝ) = 0 := le_antisymm (by simpa using t.property.2) t.property.1
    rw [NNReal.coe_zero, anchoredTimeError_zero] at h
    rw [ht]
    simpa using h.le
  · have hlt := continuousCone_lt_of_error_lt f 0 hT (by rwa [offsetPath_zero])
    obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit T.property (intervalPath f T)).mp
      ((anchoredTimeError_eq_interval T.property f).symm.trans_le h.le)
    have hex : ∃ b, continuousSlopeFeasible f 0 1 T b :=
      ⟨a, fun t => by rw [sub_zero]; exact ha t⟩
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hL := (continuousSlopeFeasible_iff_mem_Icc hTr hex _).mpr ⟨le_rfl, hlt.le⟩
    have hU := (continuousSlopeFeasible_iff_mem_Icc hTr hex _).mpr ⟨hlt.le, le_rfl⟩
    by_cases hLm : continuousLowerSlope f 0 1 T = m
    · exact ⟨_, fun h' => hlt.ne (hLm.trans h'.symm), hU⟩
    · exact ⟨_, hLm, hL⟩

/-! ## The pinch time and its slope -/

theorem entranceReach_eq_ofReal_pinch {f : C(ℝ, ℝ)} (hf : |f 0| < 1)
    (hσ : 0 < entrancePinch f) :
    entranceReach f = ((entrancePinch f).toNNReal : ℝ≥0∞) := by
  have hpinch := firstContinuousConePinch_eq_entranceReach hf
  have hne : entranceReach f ≠ ⊤ := by
    intro h
    simp [entrancePinch, hpinch, h] at hσ
  have h1 : ENNReal.ofReal (entrancePinch f) = entranceReach f := by
    rw [entrancePinch, hpinch, ENNReal.ofReal_toReal hne]
  rw [← h1]
  rfl

/-- At a finite positive pinch the error equals `1`, it is below `1` before, and
`entranceSlope f` is the unique feasible slope on `[0, σ]`. -/
theorem entrancePinch_spec {f : C(ℝ, ℝ)} (hf : |f 0| < 1) (hσ : 0 < entrancePinch f) :
    anchoredTimeError f (entrancePinch f) = 1 ∧
      (∀ T : ℝ≥0, (T : ℝ) < entrancePinch f → anchoredTimeError f T < 1) ∧
      continuousSlopeFeasible f 0 1 (entrancePinch f) (entranceSlope f) ∧
      (∀ b, continuousSlopeFeasible f 0 1 (entrancePinch f) b → b = entranceSlope f) := by
  set σN := (entrancePinch f).toNNReal with hσNdef
  have hσN : (σN : ℝ) = entrancePinch f := Real.coe_toNNReal _ hσ.le
  have hreach := entranceReach_eq_ofReal_pinch hf hσ
  rw [← hσNdef] at hreach
  have hD0 : (fun t : ℝ≥0 => anchoredTimeError f t) 0 < 1 := by
    simpa [anchoredTimeError_zero] using hf
  have herrN : anchoredTimeError f σN = 1 :=
    error_at_firstReach (anchoredTimeError_nnreal_monotone f)
      ((continuous_anchoredTimeError f).comp continuous_subtype_val) hD0 hreach
  have herr : anchoredTimeError f (entrancePinch f) = 1 := by rwa [hσN] at herrN
  have hbefore : ∀ T : ℝ≥0, (T : ℝ) < entrancePinch f → anchoredTimeError f T < 1 := by
    intro T hT
    by_contra h
    push Not at h
    have hle := (entranceReach_le_iff f T).mpr h
    rw [hreach] at hle
    have : σN ≤ T := by exact_mod_cast hle
    have : (σN : ℝ) ≤ T := by exact_mod_cast this
    linarith
  have herrI : anchoredError (intervalPath f (entrancePinch f)) = 1 :=
    (anchoredTimeError_eq_interval hσ.le f).symm.trans herr
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit hσ.le
    (intervalPath f (entrancePinch f))).mp herrI.le
  have hzeroI : |intervalPath f (entrancePinch f) ⟨0, le_rfl, hσ.le⟩| < 1 := by
    simpa [intervalPath, ContinuousMap.restrict_apply] using hf
  have ha' : continuousSlopeFeasible f 0 1 (entrancePinch f) a :=
    fun t => by simpa [intervalPath, ContinuousMap.restrict_apply] using ha t
  have hu : ∀ b, continuousSlopeFeasible f 0 1 (entrancePinch f) b → b = a := by
    intro b hb
    exact anchored_feasible_slope_unique hσ.le one_pos _ hzeroI herrI
      (fun t => by simpa [intervalPath, ContinuousMap.restrict_apply] using hb t) ha
  have hslope : entranceSlope f = a := (continuousCone_eq_of_unique hσ ha' hu).1
  refine ⟨herr, hbefore, hslope ▸ ha', fun b hb => (hu b hb).trans hslope.symm⟩

/-- The terminal residual at a finite positive pinch lies on the boundary of the band. -/
theorem abs_entranceSign_eq_one {f : C(ℝ, ℝ)} (hf : |f 0| < 1) (hσ : 0 < entrancePinch f) :
    |entranceSign f| = 1 := by
  obtain ⟨-, hbefore, hfeas, huniq⟩ := entrancePinch_spec hf hσ
  set σ := entrancePinch f with hσdef
  set m := entranceSlope f with hmdef
  have hle : |f σ - m * σ| ≤ 1 := by
    have h1 := hfeas ⟨σ, hσ.le, le_rfl⟩
    simpa using h1
  change |f σ - m * σ| = 1
  by_contra hne
  have hlt : |f σ - m * σ| < 1 := lt_of_le_of_ne hle hne
  set ρ := (|f σ - m * σ| + 1) / 2 with hρdef
  have hρ : ρ < 1 := by linarith
  have hcont : Continuous (fun t => |f t - m * t|) := by fun_prop
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuous_iff.mp hcont σ (ρ - |f σ - m * σ|) (by linarith)
  set T₁ : ℝ≥0 := (σ - δ / 2).toNNReal with hT₁def
  have hT₁ : (T₁ : ℝ) < σ := by
    rw [hT₁def, Real.coe_toNNReal']
    exact max_lt (by linarith) hσ
  obtain ⟨a, ham, ha⟩ := exists_ne_feasible_of_error_lt f (hbefore T₁ hT₁) m
  apply ham
  refine eq_of_mix_unique hρ (fun t => σ - δ / 2 ≤ t) hfeas huniq ?_ ?_
  · intro t ht
    have hd : dist (t : ℝ) σ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · linarith [t.property.2]
    have h1 := hball t hd
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    simp only [sub_zero]
    linarith
  · intro t ht
    push Not at ht
    have htT : (t : ℝ) ≤ T₁ := by
      rw [hT₁def, Real.coe_toNNReal']
      exact le_max_of_le_left ht.le
    exact ha ⟨t, t.property.1, htT⟩

/-- The terminal sign at a finite positive pinch is `1` or `-1`. -/
theorem entranceSign_eq_one_or_neg_one {f : C(ℝ, ℝ)} (hf : |f 0| < 1)
    (hσ : 0 < entrancePinch f) :
    entranceSign f = 1 ∨ entranceSign f = -1 :=
  (abs_eq zero_le_one).mp (abs_entranceSign_eq_one hf hσ)

end

end SwingRepair
