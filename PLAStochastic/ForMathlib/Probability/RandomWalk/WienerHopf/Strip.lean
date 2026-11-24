import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderMass

/-!
# The Wiener–Hopf factorization on a strip

If the step law has the two-sided exponential moments `∫ e^{± a y} dρ < ∞` and both ladder
gaps are positive, then the factorization `1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))` holds on
the closed unit disk in `s` times the closed strip `|Re z| ≤ a` (`wienerHopf_strip`). The gaps
`E[e^{a H₋}; τ₋ < ∞] < 1` and `E[e^{-a H₊}; τ₊ < ∞] < 1` hold as soon as `ρ` charges both
`(-∞, 0)` and `(0, ∞)` (`wienerHopf_strip_of_pos`). No continuity or atom condition is needed:
the identity is evaluated from the formal power series identity, using the ladder-height
exponential moments of `LadderMass` for absolute convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {B : Set ℝ}

/-- Absolute convergence of a ladder series dominated by a real exponential ladder series. -/
theorem summable_entry_of_le (hBm : MeasurableSet B) {s z : ℂ} (hs : ‖s‖ ≤ 1) {θ : ℝ}
    (hθ : ∀ x ∈ B, z.re * x ≤ θ * x) (hM : Integrable (fun y : ℝ => Real.exp (θ * y)) ρ)
    (he : Summable fun n : ℕ => ∫ ω in {ω | firstEntry B ω = n},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ) :
    Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry B ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => norm_nonneg _)) (fun n => ?_) he
  have hle : ∫ ω in {ω | firstEntry B ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ ≤
      ∫ ω in {ω | firstEntry B ω = n}, Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_exp_partialSum hM n).1.integrableOn ?_
    refine (ae_restrict_iff' (measurableSet_firstEntry_eq hBm n)).mpr
      (Filter.Eventually.of_forall fun ω hω => ?_)
    simp only [mem_ofPred_eq] at hω
    show ‖cexp (z * partialSum n ω)‖ ≤ Real.exp (θ * partialSum n ω)
    rw [norm_cexp_mul_ofReal, Real.exp_le_exp]
    exact hθ _ (firstEntry_eq_coe_iff.mp hω).2.1
  calc _ ≤ 1 * ∫ ω in {ω | firstEntry B ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs)
          (integral_nonneg fun _ => norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hle

omit [IsProbabilityMeasure ρ] in
theorem integrable_cexp_of_abs_re_le {a : ℝ}
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) ρ) {z : ℂ} (hz : |z.re| ≤ a) :
    Integrable (fun y : ℝ => cexp (z * y)) ρ := by
  refine (hpos.add hneg).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_cexp_mul_ofReal]
  show Real.exp (z.re * y) ≤ Real.exp (a * y) + Real.exp (-a * y)
  rcases le_total 0 y with hy | hy
  · have : z.re * y ≤ a * y := mul_le_mul_of_nonneg_right (le_of_abs_le hz) hy
    linarith [Real.exp_le_exp.mpr this, Real.exp_pos (-a * y)]
  · have : z.re * y ≤ -a * y := by
      have := mul_le_mul_of_nonpos_right (neg_le_of_abs_le hz) hy
      linarith
    linarith [Real.exp_le_exp.mpr this, Real.exp_pos (a * y)]

/-- **Wiener–Hopf factorization on a strip** (W3): if `∫ e^{± a y} dρ < ∞` and the ladder gaps
`E[e^{a H₋}; τ₋ < ∞] < 1`, `E[e^{-a H₊}; τ₊ < ∞] < 1` hold, then for `‖s‖ ≤ 1` and
`|Re z| ≤ a`, `1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))`. -/
theorem wienerHopf_strip {a : ℝ} (ha : 0 ≤ a)
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) ρ)
    (hdesc : expEntryMass ρ (Iic 0) a < 1) (hasc : expEntryMass ρ (Ioi 0) (-a) < 1)
    {s z : ℂ} (hs : ‖s‖ ≤ 1) (hz : |z.re| ≤ a) :
    1 - s * stepTransform ρ z = (1 - ascTransform ρ s z) * (1 - descTransform ρ s z) := by
  -- ascending series, dominated by `e^{a S_n}` on `{τ₊ = n}`
  have hθp : ∀ x ∈ Iic (0 : ℝ), a * x ≤ 0 := fun x hx => mul_nonpos_of_nonneg_of_nonpos ha hx
  obtain ⟨hep, -, -⟩ := expEntryMass_compl_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic hθp
    hdesc hpos
  rw [compl_Iic] at hep
  have hB : Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry (Ioi 0) ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ :=
    summable_entry_of_le measurableSet_Ioi hs (fun x hx =>
      mul_le_mul_of_nonneg_right (le_of_abs_le hz) (le_of_lt (show (0:ℝ) < x from hx))) hpos hep
  -- descending series, dominated by `e^{-a S_n}` on `{τ₋ = n}`
  have hθm : ∀ x ∈ Ioi (0 : ℝ), -a * x ≤ 0 := fun x hx => by
    have := mul_nonneg ha (le_of_lt (show (0:ℝ) < x from hx)); linarith
  obtain ⟨hem, -, -⟩ := expEntryMass_compl_le (ρ := ρ) measurableSet_Ioi isLadderSet_Ioi hθm
    hasc hneg
  rw [compl_Ioi] at hem
  have hA : Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry (Iic 0) ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ :=
    summable_entry_of_le measurableSet_Iic hs (fun x hx =>
      mul_le_mul_of_nonpos_right (neg_le_of_abs_le hz) hx) hneg hem
  have h := wienerHopf_of_summable (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (integrable_cexp_of_abs_re_le hpos hneg hz) (by rwa [compl_Iic]) hA
  rwa [compl_Iic] at h

theorem exists_pos_measureReal_Iic_neg (h : 0 < ρ (Iio 0)) :
    ∃ b > 0, 0 < ρ.real (Iic (-b)) := by
  by_contra hcon
  push Not at hcon
  have hU : Iio (0 : ℝ) = ⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1))) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hzero : ∀ n : ℕ, ρ (Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
    intro n
    have h1 := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    have h2 : ρ.real (Iic (-(1 / ((n : ℝ) + 1)))) = 0 := le_antisymm h1 measureReal_nonneg
    rwa [measureReal_eq_zero_iff] at h2
  rw [hU, measure_iUnion_null hzero] at h
  exact lt_irrefl 0 h

theorem exists_pos_measureReal_Ici_pos (h : 0 < ρ (Ioi 0)) :
    ∃ b > 0, 0 < ρ.real (Ici b) := by
  by_contra hcon
  push Not at hcon
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ici (1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn.le⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hzero : ∀ n : ℕ, ρ (Ici (1 / ((n : ℝ) + 1))) = 0 := by
    intro n
    have h1 := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    have h2 : ρ.real (Ici (1 / ((n : ℝ) + 1))) = 0 := le_antisymm h1 measureReal_nonneg
    rwa [measureReal_eq_zero_iff] at h2
  rw [hU, measure_iUnion_null hzero] at h
  exact lt_irrefl 0 h

/-- The weak descending gap is positive as soon as `ρ` charges `(-∞, 0)`. -/
theorem expEntryMass_Iic_lt_one {θ : ℝ} (hθ : 0 < θ) (h : 0 < ρ (Iio 0)) :
    expEntryMass ρ (Iic 0) θ < 1 := by
  obtain ⟨b, hb, hρb⟩ := exists_pos_measureReal_Iic_neg h
  have hgap := one_sub_expEntryMass_Iic_ge (ρ := ρ) hθ.le hb.le
  have : 0 < 1 - Real.exp (-(θ * b)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
  nlinarith [mul_pos this hρb]

/-- The strict ascending gap is positive as soon as `ρ` charges `(0, ∞)`. -/
theorem expEntryMass_Ioi_lt_one {θ : ℝ} (hθ : 0 < θ) (h : 0 < ρ (Ioi 0)) :
    expEntryMass ρ (Ioi 0) (-θ) < 1 := by
  obtain ⟨b, hb, hρb⟩ := exists_pos_measureReal_Ici_pos h
  have hgap := one_sub_expEntryMass_Ioi_ge (ρ := ρ) hθ.le hb
  have : 0 < 1 - Real.exp (-(θ * b)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
  nlinarith [mul_pos this hρb]

/-- **Wiener–Hopf factorization on a strip**, with hypotheses on the step law only: if
`∫ e^{± a y} dρ < ∞` (`a > 0`) and `ρ` charges both `(-∞, 0)` and `(0, ∞)`, then
`1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))` for `‖s‖ ≤ 1` and `|Re z| ≤ a`. -/
theorem wienerHopf_strip_of_pos {a : ℝ} (ha : 0 < a)
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) ρ)
    (hl : 0 < ρ (Iio 0)) (hr : 0 < ρ (Ioi 0)) {s z : ℂ} (hs : ‖s‖ ≤ 1) (hz : |z.re| ≤ a) :
    1 - s * stepTransform ρ z = (1 - ascTransform ρ s z) * (1 - descTransform ρ s z) :=
  wienerHopf_strip ha.le hpos hneg (expEntryMass_Iic_lt_one ha hl)
    (expEntryMass_Ioi_lt_one ha hr) hs hz

end PGM.WienerHopf
