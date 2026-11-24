import PLAStochastic.Swing.Ladder.Blackwell.UniformWindowLimit

/-!
# Spread-out inter-arrival laws

A *spread-out* inter-arrival law, in the sense used here, is a probability law `ν` on
`(0,∞)` with an explicit Lebesgue component `κ · Leb|[1,2] ≤ ν` and a finite second
moment.  This file collects, for one fixed such law and with no Gaussian structure, every
input of the analytic Blackwell argument of `Swing.Ladder.Blackwell.UniformWindowLimit`:

* Chebyshev bounds for the convolution powers and the geometric smallness of their mass
  on `[0,1)`;
* the equilibrium overshoot law `Q` is a probability law with Lebesgue density at most
  `1/κ` and a Chebyshev tail;
* the renewal measure `U = ∑ ν^{*n}` charges no negative set, grows at most linearly, and
  every window satisfies `U((c, c+w]) ≤ U([0,w])` (proved on the canonical i.i.d.
  realization `⨂ ν` of the sequence space);
* the a.s.-crossing identity `∫_{[0,c]} ν((c-s,∞)) U(ds) = 1`, proved by telescoping;
* hence the exact stationary identity `∫ U((b-x-y, b-y]) Q(dy) = x / E H`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A spread-out inter-arrival law: a probability law on `(0,∞)` with the Lebesgue
component `κ · Leb|[1,2]` and a finite second moment. -/
structure SpreadOutLaw (ν : Measure ℝ) (κ : ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ν
  Iic_zero : ν (Iic 0) = 0
  pos : 0 < κ
  minor : ENNReal.ofReal κ • volume.restrict (Icc (1 : ℝ) 2) ≤ ν
  sq_integrable : Integrable (fun x : ℝ => x ^ 2) ν

namespace SpreadOutLaw

variable {ν : Measure ℝ} {κ : ℝ}

theorem le_one (h : SpreadOutLaw ν κ) : κ ≤ 1 := by
  have := h.isProbabilityMeasure
  have h1 : (ENNReal.ofReal κ • volume.restrict (Icc (1 : ℝ) 2)) univ ≤ ν univ := h.minor univ
  rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc, measure_univ,
    show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_one, smul_eq_mul, mul_one] at h1
  exact ENNReal.ofReal_le_one.mp h1

theorem Iio_zero (h : SpreadOutLaw ν κ) : ν (Iio 0) = 0 :=
  measure_mono_null Iio_subset_Iic_self h.Iic_zero

theorem ae_pos (h : SpreadOutLaw ν κ) : ∀ᵐ x ∂ν, 0 < x := by
  rw [ae_iff]
  convert h.Iic_zero using 2
  ext x
  simp

theorem ae_nonneg (h : SpreadOutLaw ν κ) : 0 ≤ᵐ[ν] fun x : ℝ => x :=
  h.ae_pos.mono fun _ hx => hx.le

theorem id_integrable (h : SpreadOutLaw ν κ) : Integrable (fun x : ℝ => x) ν := by
  have := h.isProbabilityMeasure
  refine ((integrable_const (1 : ℝ)).add h.sq_integrable).mono' aestronglyMeasurable_id ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  show |x| ≤ 1 + x ^ 2
  nlinarith [abs_nonneg x, sq_abs x]

theorem mean_ge (h : SpreadOutLaw ν κ) : κ ≤ ladderMean ν := by
  have := h.isProbabilityMeasure
  rw [ladderMean_eq_integral h.ae_nonneg h.id_integrable]
  exact ladder_mean_ge_of_minorization h.pos.le h.minor h.id_integrable h.ae_nonneg

theorem mean_ne_zero (h : SpreadOutLaw ν κ) : ladderMeanENN ν ≠ 0 := by
  have hlow := lintegral_ofReal_ge_of_minorization h.minor
  intro h0
  rw [ladderMeanENN] at h0
  rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hlow
  linarith [h.pos]

theorem mean_ne_top (h : SpreadOutLaw ν κ) : ladderMeanENN ν ≠ ⊤ := by
  rw [ladderMeanENN, ← ofReal_integral_eq_lintegral_ofReal h.id_integrable h.ae_nonneg]
  exact ENNReal.ofReal_ne_top

theorem sqMoment_nonneg (_h : SpreadOutLaw ν κ) : 0 ≤ ∫ x, x ^ 2 ∂ν :=
  integral_nonneg fun x => sq_nonneg x

/-! ### Convolution powers -/

/-- Chebyshev through the union bound for every convolution power. -/
theorem convPow_tail_le (h : SpreadOutLaw ν κ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (measureConvPow ν m).real (Ioi c) ≤ (m : ℝ) ^ 3 * (∫ x, x ^ 2 ∂ν) / c ^ 2 := by
  have := h.isProbabilityMeasure
  set B := ∫ x, x ^ 2 ∂ν with hBdef
  have hB0 : 0 ≤ B := h.sqMoment_nonneg
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [measureConvPow_zero, Measure.real, Measure.dirac_apply' _ measurableSet_Ioi,
      Set.indicator_of_notMem (show (0 : ℝ) ∉ Ioi c from not_lt.mpr hc.le)]
    simp
  · have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hcm : 0 < c / m := div_pos hc hmpos
    have h1 := measureConvPow_Ioi_le ν (c / m) m
    rw [show (m : ℝ) * (c / m) = c by field_simp] at h1
    have h2 := measureReal_Ioi_le_sq_moment h.sq_integrable hcm
    have h1r : (measureConvPow ν m).real (Ioi c) ≤ (m : ℝ) * ν.real (Ioi (c / m)) := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_natCast, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_ne_top _ _)) h1
    calc (measureConvPow ν m).real (Ioi c)
        ≤ (m : ℝ) * ν.real (Ioi (c / m)) := h1r
      _ ≤ (m : ℝ) * (B / (c / m) ^ 2) := mul_le_mul_of_nonneg_left h2 hmpos.le
      _ = (m : ℝ) ^ 3 * B / c ^ 2 := by field_simp

theorem Iio_one_le (h : SpreadOutLaw ν κ) : ν (Iio 1) ≤ ENNReal.ofReal (1 - κ) := by
  have := h.isProbabilityMeasure
  have hIcc : ENNReal.ofReal κ ≤ ν (Icc 1 2) := by
    have h0 := h.minor (Icc 1 2)
    rwa [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Icc,
      Set.inter_self, Real.volume_Icc, show (2 : ℝ) - 1 = 1 by norm_num,
      ENNReal.ofReal_one, mul_one] at h0
  have hIci : ENNReal.ofReal κ ≤ ν (Ici 1) := hIcc.trans (measure_mono Icc_subset_Ici_self)
  have hcompl : ν (Iio 1) = 1 - ν (Ici 1) := by
    rw [← Set.compl_Ici, measure_compl measurableSet_Ici (measure_ne_top _ _), measure_univ]
  rw [hcompl, ENNReal.ofReal_sub 1 h.pos.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hIci 1

/-- The `m`-th convolution power has mass at most `(1-κ)^m` on `[0,1)`. -/
theorem convPow_Iio_one_le (h : SpreadOutLaw ν κ) (m : ℕ) :
    (measureConvPow ν m).real (Iio 1) ≤ (1 - κ) ^ m := by
  have := h.isProbabilityMeasure
  have hκ1 := h.le_one
  refine ENNReal.toReal_le_of_le_ofReal (pow_nonneg (by linarith) m) ?_
  calc measureConvPow ν m (Iio 1) ≤ (ν (Iio 1)) ^ m := measureConvPow_Iio_one_le ν h.Iio_zero m
    _ ≤ (ENNReal.ofReal (1 - κ)) ^ m := by
        gcongr
        exact h.Iio_one_le
    _ = ENNReal.ofReal ((1 - κ) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm

/-! ### The equilibrium overshoot law -/

theorem equilibrium_isProbabilityMeasure (h : SpreadOutLaw ν κ) :
    IsProbabilityMeasure (equilibriumOvershootLaw ν) := by
  have := h.isProbabilityMeasure
  exact equilibriumOvershootLaw_isProbabilityMeasure ν h.ae_nonneg h.mean_ne_zero h.mean_ne_top

/-- The equilibrium law has Lebesgue density at most `1/κ`. -/
theorem equilibrium_le_smul_volume (h : SpreadOutLaw ν κ) :
    equilibriumOvershootLaw ν ≤ ENNReal.ofReal (1 / κ) • volume := by
  have := h.isProbabilityMeasure
  have hmean : ENNReal.ofReal κ ≤ ladderMeanENN ν := lintegral_ofReal_ge_of_minorization h.minor
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [equilibriumOvershootLaw_apply ν hA, Measure.smul_apply, smul_eq_mul]
  have hpt : ∀ o : ℝ, ν (Ioi o) / ladderMeanENN ν ≤ ENNReal.ofReal (1 / κ) := by
    intro o
    calc ν (Ioi o) / ladderMeanENN ν ≤ 1 / ladderMeanENN ν :=
          ENNReal.div_le_div_right prob_le_one _
      _ ≤ 1 / ENNReal.ofReal κ := ENNReal.div_le_div_left hmean 1
      _ = ENNReal.ofReal (1 / κ) := by
          rw [one_div, one_div, ENNReal.ofReal_inv_of_pos h.pos]
  calc (∫⁻ o in A ∩ Ici 0, ν (Ioi o) / ladderMeanENN ν)
      ≤ ∫⁻ _o in A ∩ Ici 0, ENNReal.ofReal (1 / κ) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / κ) * volume (A ∩ Ici 0) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (1 / κ) * volume A :=
        mul_le_mul' le_rfl (measure_mono inter_subset_left)

/-- The equilibrium overshoot tail obeys the Chebyshev bound `E H² / (κ T)`. -/
theorem equilibrium_tail_le (h : SpreadOutLaw ν κ) {T : ℝ} (hT : 0 < T) :
    (equilibriumOvershootLaw ν).real (Ioi T) ≤ (∫ x, x ^ 2 ∂ν) / (κ * T) := by
  have := h.isProbabilityMeasure
  have hlaw : (equilibriumOvershootLaw ν).real (Ioi T) =
      (∫ x, max (x - T) 0 ∂ν) / ladderMean ν := by
    rw [Measure.real, equilibriumOvershootLaw_Ioi ν h.mean_ne_zero hT.le,
      equilibriumOvershootTail_toReal]
  have hsplit : (∫ x, max (x - T) 0 ∂ν) = ∫ x in Ioi T, (x - T) ∂ν := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi T)]
    · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
        have hx' : T < x := hx
        exact max_eq_left (by linarith))
    · intro x hx
      have hx' : ¬ T < x := hx
      exact max_eq_right (by linarith)
  have hnum : (∫ x, max (x - T) 0 ∂ν) ≤ (∫ x, x ^ 2 ∂ν) / T := by
    rw [hsplit]
    exact setIntegral_sub_le_sq_moment h.id_integrable h.sq_integrable (t := T) hT.le hT
  rw [hlaw]
  have hB0 := h.sqMoment_nonneg
  calc (∫ x, max (x - T) 0 ∂ν) / ladderMean ν
      ≤ ((∫ x, x ^ 2 ∂ν) / T) / κ := by
        refine div_le_div₀ (by positivity) hnum h.pos h.mean_ge
    _ = (∫ x, x ^ 2 ∂ν) / (κ * T) := by field_simp

/-! ### The renewal measure -/

theorem renewal_Iio_zero (h : SpreadOutLaw ν κ) : ladderRenewalMeasure ν (Iio 0) = 0 := by
  have := h.isProbabilityMeasure
  rw [ladderRenewalMeasure_apply _ measurableSet_Iio]
  simp only [measureConvPow_Iio_zero ν h.Iio_zero, tsum_zero]

/-- The renewal mass of `[0,b]` grows at most linearly, from one Laplace value. -/
theorem renewal_Icc_le (h : SpreadOutLaw ν κ) {b : ℝ} (hb : 0 ≤ b) :
    ladderRenewalMeasure ν (Icc 0 b) ≤ ENNReal.ofReal (2 * Real.exp 1 * (1 + b) / κ) := by
  have := h.isProbabilityMeasure
  have hc := h.pos
  have hc1 := h.le_one
  have hb1 : (0 : ℝ) < 1 + b := by linarith
  set lam : ℝ := 1 / (1 + b) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one hb1]
    linarith
  have hq0 : (0 : ℝ) ≤ 1 - κ * lam / 2 := by nlinarith
  have hq1 : 1 - κ * lam / 2 < 1 := by nlinarith
  have hbound := ladderRenewalMeasure_Icc_le ν (b := b) (lam := lam) (q := 1 - κ * lam / 2)
    hlam0.le hq0 hq1 (ladderLaplace_le_of_minorization hc.le hlam0.le hlam1 h.Iic_zero h.minor)
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hden : 1 - (1 - κ * lam / 2) = κ * lam / 2 := by ring
  rw [hden]
  have hexp : Real.exp (lam * b) ≤ Real.exp 1 := by
    refine Real.exp_le_exp.mpr ?_
    rw [hlamdef, div_mul_eq_mul_div, one_mul, div_le_one hb1]
    linarith
  have hpos : (0 : ℝ) < κ * lam / 2 := by positivity
  rw [div_le_div_iff₀ hpos hc]
  have hlamval : lam * (1 + b) = 1 := by
    rw [hlamdef]
    field_simp
  have hkey : 2 * Real.exp 1 * (1 + b) * (κ * lam / 2) = Real.exp 1 * κ * (lam * (1 + b)) := by
    ring
  rw [hkey, hlamval, mul_one]
  exact mul_le_mul_of_nonneg_right hexp hc.le

theorem renewal_Icc_ne_top (h : SpreadOutLaw ν κ) (u : ℝ) :
    ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤ := by
  rcases le_or_gt 0 u with hu | hu
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.renewal_Icc_le hu)
  · rw [Icc_eq_empty (by linarith), measure_empty]
    exact ENNReal.zero_ne_top

end SpreadOutLaw

/-! ### The canonical i.i.d. realization and the window bound -/

/-- On the canonical product space the partial sums of the coordinates have the
convolution powers as laws. -/
theorem infinitePi_renewalSum_map (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (renewalSum (fun k (w : ℕ → ℝ) => w k) n) =
      measureConvPow ν n := by
  have hH : ∀ k, Measurable (fun w : ℕ → ℝ => w k) := fun k => measurable_pi_apply k
  have hi : iIndepFun (fun k (w : ℕ → ℝ) => w k) (Measure.infinitePi (fun _ : ℕ => ν)) := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => (id : ℝ → ℝ))
      (fun _ => measurable_id)
    simpa using this
  have hmap : ∀ k, (Measure.infinitePi (fun _ : ℕ => ν)).map (fun w : ℕ → ℝ => w k) = ν :=
    fun k => Measure.infinitePi_map_eval _ k
  have hsum : renewalSum (fun k (w : ℕ → ℝ) => w k) n =
      renewalBlockSum (fun k (w : ℕ → ℝ) => w k) 0 n := by
    funext w
    simp [renewalSum, renewalBlockSum, Nat.Ico_zero_eq_range]
  rw [hsum]
  exact renewalBlockSum_map hH hi hmap 0 n

/-- **The position-uniform window bound** for an arbitrary probability law on the
nonnegative half-line: `U((c, c+w]) ≤ U([0,w])`. -/
theorem ladderRenewalMeasure_Ioc_le_Icc_of (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hU0 : ladderRenewalMeasure ν (Iio 0) = 0) (c : ℝ) {w : ℝ} (_hw : 0 ≤ w) :
    ladderRenewalMeasure ν (Ioc c (c + w)) ≤ ladderRenewalMeasure ν (Icc 0 w) := by
  set U := ladderRenewalMeasure ν with hU
  have hIic : U (Iic w) ≤ U (Icc 0 w) := by
    have hsub : Iic w ⊆ Icc (0 : ℝ) w ∪ Iio 0 := by
      intro x hx
      rcases le_or_gt 0 x with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr h
    calc U (Iic w) ≤ U (Icc 0 w ∪ Iio 0) := measure_mono hsub
      _ ≤ U (Icc 0 w) + U (Iio 0) := measure_union_le _ _
      _ = U (Icc 0 w) := by rw [hU0, add_zero]
  rcases le_or_gt 0 c with hc | hc
  · set P := Measure.infinitePi (fun _ : ℕ => ν) with hPdef
    have hH : ∀ k, Measurable (fun w : ℕ → ℝ => w k) := fun k => measurable_pi_apply k
    have hi : iIndepFun (fun k (w : ℕ → ℝ) => w k) P := by
      have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => (id : ℝ → ℝ))
        (fun _ => measurable_id)
      simpa using this
    have hmap : ∀ k, P.map (fun w : ℕ → ℝ => w k) = ν :=
      fun k => Measure.infinitePi_map_eval _ k
    have hmain := tsum_measure_renewalSum_Ioc_le (μ := P) hH hi hmap (w := w) hc
    have hleft : U (Ioc c (c + w)) =
        ∑' n : ℕ, P {x | renewalSum (fun k (w : ℕ → ℝ) => w k) n x ∈ Ioc c (c + w)} := by
      rw [hU, ladderRenewalMeasure_apply _ measurableSet_Ioc]
      refine tsum_congr fun n => ?_
      rw [← infinitePi_renewalSum_map ν n,
        Measure.map_apply (renewalSum_measurable hH n) measurableSet_Ioc]
      rfl
    have hright : (∑' j : ℕ, measureConvPow ν j (Iic w)) = U (Iic w) := by
      rw [hU, ladderRenewalMeasure_apply _ measurableSet_Iic]
    rw [hleft]
    exact (hmain.trans_eq hright).trans hIic
  · have hsub : Ioc c (c + w) ⊆ Icc (0 : ℝ) w ∪ Iio 0 := by
      intro x hx
      rcases le_or_gt 0 x with h | h
      · exact Or.inl ⟨h, le_trans hx.2 (by linarith)⟩
      · exact Or.inr h
    calc U (Ioc c (c + w)) ≤ U (Icc 0 w ∪ Iio 0) := measure_mono hsub
      _ ≤ U (Icc 0 w) + U (Iio 0) := measure_union_le _ _
      _ = U (Icc 0 w) := by rw [hU0, add_zero]

/-! ### The a.s.-crossing identity by telescoping -/

/-- One step of the telescoping: the mass of `ν^{*n}` in `[0,c]` splits into the part that
the next increment carries above `c` and the mass of `ν^{*(n+1)}` in `[0,c]`. -/
theorem convPow_Icc_split (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Iio 0) = 0)
    {c : ℝ} (n : ℕ) :
    (∫⁻ s in Icc (0 : ℝ) c, ν (Ioi (c - s)) ∂(measureConvPow ν n)) +
        measureConvPow ν (n + 1) (Icc 0 c) = measureConvPow ν n (Icc 0 c) := by
  set ρ := measureConvPow ν n with hρ
  have hρ0 : ρ (Iio 0) = 0 := measureConvPow_Iio_zero ν hν0 n
  have hnext : measureConvPow ν (n + 1) (Icc 0 c) =
      ∫⁻ s in Icc (0 : ℝ) c, ν (Iic (c - s)) ∂ρ := by
    rw [measureConvPow_succ, measure_conv_apply _ _ measurableSet_Icc,
      ← lintegral_indicator measurableSet_Icc]
    have hae : ∀ᵐ s ∂ρ, 0 ≤ s := by
      rw [ae_iff]
      convert hρ0 using 2
      ext s
      simp
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    by_cases hsc : s ≤ c
    · rw [Set.indicator_of_mem (show s ∈ Icc (0 : ℝ) c from ⟨hs, hsc⟩)]
      refine le_antisymm (measure_mono fun y hy => ?_) ?_
      · have hy' : 0 ≤ s + y ∧ s + y ≤ c := hy
        show y ≤ c - s
        linarith
      · have hsub : Iic (c - s) ⊆ {y : ℝ | s + y ∈ Icc 0 c} ∪ Iio 0 := by
          intro y hy
          rcases le_or_gt 0 y with h0 | h0
          · left
            have hy' : y ≤ c - s := hy
            exact ⟨by linarith, by linarith⟩
          · exact Or.inr h0
        calc ν (Iic (c - s)) ≤ ν ({y : ℝ | s + y ∈ Icc 0 c} ∪ Iio 0) := measure_mono hsub
          _ ≤ ν {y : ℝ | s + y ∈ Icc 0 c} + ν (Iio 0) := measure_union_le _ _
          _ = ν {y : ℝ | s + y ∈ Icc 0 c} := by rw [hν0, add_zero]
    · rw [Set.indicator_of_notMem (show s ∉ Icc (0 : ℝ) c from fun h => hsc h.2)]
      refine le_antisymm (le_of_le_of_eq (measure_mono fun y hy => ?_) hν0) bot_le
      have hy' : 0 ≤ s + y ∧ s + y ≤ c := hy
      show y < 0
      linarith [not_le.mp hsc]
  have hmeasIoi : Measurable (fun s : ℝ => ν (Ioi (c - s))) :=
    (measurable_ladderTail ν).comp (measurable_const.sub measurable_id)
  rw [hnext, ← lintegral_add_left hmeasIoi]
  have hone : ∀ s : ℝ, ν (Ioi (c - s)) + ν (Iic (c - s)) = 1 := by
    intro s
    rw [← Set.compl_Ioi, measure_add_measure_compl measurableSet_Ioi, measure_univ]
  simp_rw [hone]
  rw [lintegral_one, Measure.restrict_apply_univ]

/-- **The a.s.-crossing identity** `∫_{[0,c]} ν((c-s,∞)) U(ds) = 1` for every probability
law on `[0,∞)` whose renewal measure is finite on `[0,c]`. -/
theorem renewalOvershootTail_zero_eq_one_of (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c)
    (hfin : ladderRenewalMeasure ν (Icc 0 c) ≠ ⊤) :
    renewalOvershootTail ν c 0 = 1 := by
  set t : ℕ → ℝ≥0∞ := fun n => ∫⁻ s in Icc (0 : ℝ) c, ν (Ioi (c - s)) ∂(measureConvPow ν n)
    with htdef
  set a : ℕ → ℝ≥0∞ := fun n => measureConvPow ν n (Icc 0 c) with hadef
  have hstep : ∀ n, t n + a (n + 1) = a n := fun n => convPow_Icc_split ν hν0 n
  have ha0 : a 0 = 1 := by
    simp only [hadef, measureConvPow_zero]
    rw [Measure.dirac_apply' _ measurableSet_Icc,
      Set.indicator_of_mem (show (0 : ℝ) ∈ Icc 0 c from ⟨le_rfl, hc⟩)]
    rfl
  have hpartial : ∀ N : ℕ, (∑ n ∈ Finset.range N, t n) + a N = 1 := by
    intro N
    induction N with
    | zero => simp [ha0]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, hstep N, ih]
  have hafin : ∀ N, a N ≠ ⊤ := fun N => measure_ne_top _ _
  have hpartial' : ∀ N : ℕ, (∑ n ∈ Finset.range N, t n) = 1 - a N :=
    fun N => ENNReal.eq_sub_of_add_eq (hafin N) (hpartial N)
  have hatsum : (∑' N, a N) ≠ ⊤ := by
    rw [hadef, ← ladderRenewalMeasure_apply _ measurableSet_Icc]
    exact hfin
  have hazero : Tendsto a atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hatsum
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, t n) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hazero
      (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at this
    exact this.congr fun N => (hpartial' N).symm
  have htsum : renewalOvershootTail ν c 0 = ∑' n, t n := by
    rw [renewalOvershootTail, ladderRenewalMeasure, Measure.restrict_sum _ measurableSet_Icc,
      lintegral_sum_measure]
    refine tsum_congr fun n => ?_
    simp only [htdef, add_zero]
  rw [htsum]
  exact tendsto_nhds_unique (ENNReal.tendsto_nat_tsum t) hlim

namespace SpreadOutLaw

variable {ν : Measure ℝ} {κ : ℝ}

theorem renewal_Ioc_le_Icc (h : SpreadOutLaw ν κ) (c : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ladderRenewalMeasure ν (Ioc c (c + w)) ≤ ladderRenewalMeasure ν (Icc 0 w) := by
  have := h.isProbabilityMeasure
  exact ladderRenewalMeasure_Ioc_le_Icc_of ν h.renewal_Iio_zero c hw

/-- The explicit position-uniform window constant. -/
theorem renewal_Ioc_le_const (h : SpreadOutLaw ν κ) (c : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ladderRenewalMeasure ν (Ioc c (c + w)) ≤ ENNReal.ofReal (2 * Real.exp 1 * (1 + w) / κ) :=
  (h.renewal_Ioc_le_Icc c hw).trans (h.renewal_Icc_le hw)

theorem renewalOvershootTail_zero (h : SpreadOutLaw ν κ) {c : ℝ} (hc : 0 ≤ c) :
    renewalOvershootTail ν c 0 = 1 := by
  have := h.isProbabilityMeasure
  exact renewalOvershootTail_zero_eq_one_of ν h.Iio_zero hc (h.renewal_Icc_ne_top c)

/-- **The stationary identity**: the `Q`-average of the shifted window masses is exactly
`x / E H`. -/
theorem integral_equilibrium_window_eq (h : SpreadOutLaw ν κ) {b x : ℝ} (hx : 0 ≤ x)
    (hxb : x ≤ b) :
    (∫ y, (ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))).toReal
      ∂(equilibriumOvershootLaw ν)) = x / ladderMean ν := by
  have := h.isProbabilityMeasure
  have hmeas : Measurable (fun y : ℝ => ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))) :=
    measurable_ladderRenewal_window_shift ν b x
  have hfin : ∀ y : ℝ, ladderRenewalMeasure ν (Ioc (b - x - y) (b - y)) < ⊤ := by
    intro y
    have hbnd := h.renewal_Ioc_le_const (b - x - y) hx
    rw [show b - x - y + x = b - y by ring] at hbnd
    exact lt_of_le_of_lt hbnd ENNReal.ofReal_lt_top
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall hfin),
    lintegral_equilibrium_window_eq ν h.renewal_Iio_zero
      (fun c hc => h.renewalOvershootTail_zero hc) h.ae_nonneg h.mean_ne_zero h.mean_ne_top
      hx hxb,
    ENNReal.toReal_div, ENNReal.toReal_ofReal hx]
  rfl

end SpreadOutLaw

end SwingRepair
