import PLAStochastic.Swing.Gaussian.Tail.ChargingEstimates

/-! # Gaussian anti-concentration of the actual output margin

The output margin of one completed segment is `E-|X'|` with
`X' = D_n+Z-n m`, where `D_n` and `m` are fixed before the fresh increment
`Z`.  Its preimage of a target interval is a union of two intervals of the
same length, so the Gaussian density bound gives a linear estimate in the
target length.  This is the analytic core of Lemma H.2; no Gaussian law is
assumed for a selected increment.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem gaussianPDFReal_le_zero_value (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg x]

/-- Above a nonnegative threshold the Gaussian mass is controlled by the
Lebesgue measure times the density at the threshold. -/
theorem gaussianReal_le_density_volume {a : ℝ} (ha : 0 ≤ a) {S : Set ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ Ici a) :
    gaussianReal 0 1 S ≤ ENNReal.ofReal (gaussianPDFReal 0 1 a)*volume S := by
  rw [gaussianReal_apply _ (by norm_num) S]
  calc
    (∫⁻ x in S, gaussianPDF 0 1 x) ≤ ∫⁻ _ in S, ENNReal.ofReal (gaussianPDFReal 0 1 a) := by
      apply setLIntegral_mono' hS
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_antitone_nonneg ha (hsub hx))
    _ = ENNReal.ofReal (gaussianPDFReal 0 1 a)*volume S := setLIntegral_const _ _

theorem gaussianReal_le_density_volume_global {S : Set ℝ} (hS : MeasurableSet S) :
    gaussianReal 0 1 S ≤ ENNReal.ofReal (gaussianPDFReal 0 1 0)*volume S := by
  rw [gaussianReal_apply _ (by norm_num) S]
  calc
    (∫⁻ x in S, gaussianPDF 0 1 x) ≤ ∫⁻ _ in S, ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
      apply setLIntegral_mono' hS
      intro x _
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_zero_value x)
    _ = ENNReal.ofReal (gaussianPDFReal 0 1 0)*volume S := setLIntegral_const _ _

/-- The actual target set of fresh increments. -/
def marginTargetSet (Eb v p q : ℝ) : Set ℝ := {z : ℝ | Eb-|v+z| ∈ Icc p q}

theorem measurableSet_marginTargetSet (Eb v p q : ℝ) : MeasurableSet (marginTargetSet Eb v p q) :=
  measurableSet_Icc.preimage ((measurable_const.sub ((measurable_const.add measurable_id).abs)))

/-- The preimage of a target interval is contained in two intervals of that length. -/
theorem marginTargetSet_subset (Eb v p q : ℝ) :
    marginTargetSet Eb v p q ⊆ Icc (Eb-q-v) (Eb-p-v) ∪ Icc (-(Eb-p)-v) (-(Eb-q)-v) := by
  intro z hz
  have hz' : p ≤ Eb-|v+z| ∧ Eb-|v+z| ≤ q := mem_Icc.mp hz
  rcases le_or_gt 0 (v+z) with h | h
  · left
    rw [abs_of_nonneg h] at hz'
    exact mem_Icc.mpr ⟨by linarith, by linarith⟩
  · right
    rw [abs_of_neg h] at hz'
    exact mem_Icc.mpr ⟨by linarith, by linarith⟩

theorem volume_marginTargetSet_le {Eb v p q : ℝ} (hpq : p ≤ q) :
    volume (marginTargetSet Eb v p q) ≤ ENNReal.ofReal (2*(q-p)) := by
  refine (measure_mono (marginTargetSet_subset Eb v p q)).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [Real.volume_Icc, Real.volume_Icc]
  have h₁ : Eb-p-v-(Eb-q-v) = q-p := by ring
  have h₂ : -(Eb-q)-v-(-(Eb-p)-v) = q-p := by ring
  rw [h₁, h₂, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The anti-concentration estimate on the whole line. -/
theorem gaussianReal_marginTargetSet_le {Eb v p q : ℝ} (hpq : p ≤ q) :
    gaussianReal 0 1 (marginTargetSet Eb v p q) ≤
      ENNReal.ofReal (2*(q-p)*gaussianPDFReal 0 1 0) := by
  refine (gaussianReal_le_density_volume_global (measurableSet_marginTargetSet Eb v p q)).trans ?_
  refine (mul_le_mul' (le_refl _) (volume_marginTargetSet_le hpq)).trans ?_
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [gaussianPDFReal_nonneg (0 : ℝ) 1 0])

/-- The anti-concentration estimate above a positive rejection threshold. -/
theorem gaussianReal_marginTargetSet_above_le {Eb v p q r : ℝ} (hpq : p ≤ q) (hr : 0 ≤ r) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Ioi r) ≤
      ENNReal.ofReal (2*(q-p)*gaussianPDFReal 0 1 r) := by
  have hsub : marginTargetSet Eb v p q ∩ Ioi r ⊆ Ici r := fun z hz => (mem_Ioi.mp hz.2).le
  have hmeas : MeasurableSet (marginTargetSet Eb v p q ∩ Ioi r) :=
    (measurableSet_marginTargetSet Eb v p q).inter measurableSet_Ioi
  refine (gaussianReal_le_density_volume hr hmeas hsub).trans ?_
  refine (mul_le_mul' (le_refl _) ((measure_mono inter_subset_left).trans
    (volume_marginTargetSet_le hpq))).trans ?_
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [gaussianPDFReal_nonneg (0 : ℝ) 1 r])

/-- The absolute one-step comparison constant. -/
def marginAntiConcentrationConstant : ℝ :=
  2*gaussianPDFReal 0 1 0/gaussianPDFReal 0 1 2

theorem marginAntiConcentrationConstant_pos : 0 < marginAntiConcentrationConstant := by
  have h0 : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have h2 : 0 < gaussianPDFReal 0 1 2 := gaussianPDFReal_pos 0 1 2 (by norm_num)
  dsimp [marginAntiConcentrationConstant]
  positivity

theorem gaussianReal_Ioi_ge_of_le_one {r : ℝ} (hr : r ≤ 1) :
    ENNReal.ofReal (gaussianPDFReal 0 1 2) ≤ gaussianReal 0 1 (Ioi r) := by
  have hl := gaussianReal_Ioc_density_lower (a := (1 : ℝ)) (b := (2 : ℝ)) (by norm_num) (by norm_num)
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi r := fun z hz => lt_of_le_of_lt hr hz.1
  refine le_trans ?_ ((measure_mono hsub).trans' hl)
  exact ENNReal.ofReal_le_ofReal (by nlinarith [gaussianPDFReal_nonneg (0 : ℝ) 1 2])

/-- One-step comparison: below the unit threshold the target probability is a
bounded multiple of the target length times the actual rejection probability. -/
theorem gaussianReal_marginTarget_small_threshold {Eb v p q r : ℝ} (hpq : p ≤ q)
    (hr : r ≤ 1) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Ioi r) ≤
      ENNReal.ofReal (marginAntiConcentrationConstant*(q-p))*gaussianReal 0 1 (Ioi r) := by
  have h0 : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have h2 : 0 < gaussianPDFReal 0 1 2 := gaussianPDFReal_pos 0 1 2 (by norm_num)
  have hle : gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Ioi r) ≤
      ENNReal.ofReal (2*(q-p)*gaussianPDFReal 0 1 0) :=
    (measure_mono inter_subset_left).trans (gaussianReal_marginTargetSet_le hpq)
  refine hle.trans ?_
  have hlow := mul_le_mul' (le_refl (ENNReal.ofReal (marginAntiConcentrationConstant*(q-p))))
    (gaussianReal_Ioi_ge_of_le_one hr)
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul (mul_nonneg marginAntiConcentrationConstant_pos.le (sub_nonneg.mpr hpq))]
  apply ENNReal.ofReal_le_ofReal
  have hexpand : marginAntiConcentrationConstant*(q-p)*gaussianPDFReal 0 1 2 =
      2*(q-p)*gaussianPDFReal 0 1 0 := by
    dsimp [marginAntiConcentrationConstant]
    field_simp
  rw [hexpand]

/-- Two-step comparison: above the unit threshold the target probability is a
bounded multiple of the target length times the proxy acceptance probability. -/
theorem gaussianReal_marginTarget_large_threshold {Eb v p q r : ℝ} (hpq : p ≤ q) (hr : 1 < r) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Ioi r) ≤
      ENNReal.ofReal (4*(q-p))*gaussianReal 0 1 (Icc (r-1) (r-1/2)) := by
  have hle := gaussianReal_marginTargetSet_above_le (Eb := Eb) (v := v) hpq (by linarith : (0:ℝ) ≤ r)
  refine hle.trans ?_
  have hlow := mul_le_mul' (le_refl (ENNReal.ofReal (4*(q-p))))
    (gaussianReal_Icc_density_lower (a := r-1) (b := r-1/2) (by linarith) (by linarith))
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul (by nlinarith [sub_nonneg.mpr hpq])]
  apply ENNReal.ofReal_le_ofReal
  have hdens : gaussianPDFReal 0 1 r ≤ gaussianPDFReal 0 1 (r-1/2) :=
    gaussianPDFReal_antitone_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ q-p := sub_nonneg.mpr hpq
  nlinarith

/-! ## The mirrored estimates below a negative threshold -/

theorem gaussianPDFReal_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  congr 2
  ring

theorem gaussianPDFReal_antitone_nonpos {x y : ℝ} (hy : y ≤ 0) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 y := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem gaussianReal_le_density_volume_below {a : ℝ} (ha : a ≤ 0) {S : Set ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ Iic a) :
    gaussianReal 0 1 S ≤ ENNReal.ofReal (gaussianPDFReal 0 1 a)*volume S := by
  rw [gaussianReal_apply _ (by norm_num) S]
  calc
    (∫⁻ x in S, gaussianPDF 0 1 x) ≤ ∫⁻ _ in S, ENNReal.ofReal (gaussianPDFReal 0 1 a) := by
      apply setLIntegral_mono' hS
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_antitone_nonpos ha (hsub hx))
    _ = ENNReal.ofReal (gaussianPDFReal 0 1 a)*volume S := setLIntegral_const _ _

/-- A lower bound on a finite interval that lies below the origin. -/
theorem gaussianReal_Ioc_density_lower_below {a b : ℝ} (hb : b ≤ 0) (_hab : a ≤ b) :
    ENNReal.ofReal ((b-a)*gaussianPDFReal 0 1 a) ≤ gaussianReal 0 1 (Ioc a b) := by
  rw [gaussianReal_apply _ (by norm_num) (Ioc a b)]
  have hm : (∫⁻ _ : ℝ in Ioc a b, gaussianPDF 0 1 a) ≤ ∫⁻ x : ℝ in Ioc a b, gaussianPDF 0 1 x := by
    apply setLIntegral_mono' measurableSet_Ioc
    intro x hx
    exact ENNReal.ofReal_le_ofReal
      (gaussianPDFReal_antitone_nonpos (hx.2.trans hb) hx.1.le)
  simpa only [setLIntegral_const, Real.volume_Ioc, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), mul_comm] using hm

theorem gaussianReal_Icc_density_lower_below {a b : ℝ} (hb : b ≤ 0) (hab : a ≤ b) :
    ENNReal.ofReal ((b-a)*gaussianPDFReal 0 1 a) ≤ gaussianReal 0 1 (Icc a b) :=
  (gaussianReal_Ioc_density_lower_below hb hab).trans (measure_mono Ioc_subset_Icc_self)

theorem gaussianReal_marginTargetSet_below_le {Eb v p q r : ℝ} (hpq : p ≤ q) (hr : r ≤ 0) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Iio r) ≤
      ENNReal.ofReal (2*(q-p)*gaussianPDFReal 0 1 r) := by
  have hsub : marginTargetSet Eb v p q ∩ Iio r ⊆ Iic r := fun z hz => (mem_Iio.mp hz.2).le
  have hmeas : MeasurableSet (marginTargetSet Eb v p q ∩ Iio r) :=
    (measurableSet_marginTargetSet Eb v p q).inter measurableSet_Iio
  refine (gaussianReal_le_density_volume_below hr hmeas hsub).trans ?_
  refine (mul_le_mul' (le_refl _) ((measure_mono inter_subset_left).trans
    (volume_marginTargetSet_le hpq))).trans ?_
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [gaussianPDFReal_nonneg (0 : ℝ) 1 r])

theorem gaussianReal_Iio_ge_of_neg_one_le {r : ℝ} (hr : -1 ≤ r) :
    ENNReal.ofReal ((1/2)*gaussianPDFReal 0 1 2) ≤ gaussianReal 0 1 (Iio r) := by
  have hl := gaussianReal_Ioc_density_lower_below (a := (-2 : ℝ)) (b := (-3/2 : ℝ))
    (by norm_num) (by norm_num)
  have hsub : Ioc (-2 : ℝ) (-3/2) ⊆ Iio r := fun z hz => lt_of_le_of_lt hz.2 (by linarith)
  refine le_trans ?_ (hl.trans (measure_mono hsub))
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show ((-3/2 : ℝ)-(-2)) = 1/2 by ring, show ((-2 : ℝ)) = -(2 : ℝ) by ring,
    gaussianPDFReal_neg]

theorem gaussianReal_marginTarget_small_threshold_below {Eb v p q r : ℝ} (hpq : p ≤ q)
    (hr : -1 ≤ r) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Iio r) ≤
      ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p))*gaussianReal 0 1 (Iio r) := by
  have h0 : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have h2 : 0 < gaussianPDFReal 0 1 2 := gaussianPDFReal_pos 0 1 2 (by norm_num)
  have hle : gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Iio r) ≤
      ENNReal.ofReal (2*(q-p)*gaussianPDFReal 0 1 0) :=
    (measure_mono inter_subset_left).trans (gaussianReal_marginTargetSet_le hpq)
  refine hle.trans ?_
  have hlow := mul_le_mul' (le_refl (ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p))))
    (gaussianReal_Iio_ge_of_neg_one_le hr)
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul (by nlinarith [marginAntiConcentrationConstant_pos, sub_nonneg.mpr hpq] :
    (0 : ℝ) ≤ 2*marginAntiConcentrationConstant*(q-p))]
  apply ENNReal.ofReal_le_ofReal
  have hexpand : 2*marginAntiConcentrationConstant*(q-p)*((1/2)*gaussianPDFReal 0 1 2) =
      2*(q-p)*gaussianPDFReal 0 1 0 := by
    dsimp [marginAntiConcentrationConstant]
    field_simp
  rw [hexpand]

theorem gaussianReal_marginTarget_large_threshold_below {Eb v p q r : ℝ} (hpq : p ≤ q)
    (hr : r < -1) :
    gaussianReal 0 1 (marginTargetSet Eb v p q ∩ Iio r) ≤
      ENNReal.ofReal (4*(q-p))*gaussianReal 0 1 (Icc (r+1/2) (r+1)) := by
  have hle := gaussianReal_marginTargetSet_below_le (Eb := Eb) (v := v) hpq (by linarith)
  refine hle.trans ?_
  have hlow := mul_le_mul' (le_refl (ENNReal.ofReal (4*(q-p))))
    (gaussianReal_Icc_density_lower_below (a := r+1/2) (b := r+1) (by linarith) (by linarith))
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul (by nlinarith [sub_nonneg.mpr hpq])]
  apply ENNReal.ofReal_le_ofReal
  have hdens : gaussianPDFReal 0 1 r ≤ gaussianPDFReal 0 1 (r+1/2) :=
    gaussianPDFReal_antitone_nonpos (by linarith) (by linarith)
  have hq : 0 ≤ q-p := sub_nonneg.mpr hpq
  have hsimp : r+1-(r+1/2) = 1/2 := by ring
  rw [hsimp]
  nlinarith

end SwingRepair
