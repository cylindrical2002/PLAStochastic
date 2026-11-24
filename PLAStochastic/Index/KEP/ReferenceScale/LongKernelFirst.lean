import PLAStochastic.Index.KEP.ReferenceScale.LongKernelBudgets
import PLAStochastic.Index.KEP.ReferenceScale.LongKernelQuantitative

/-!
# First derivatives with a regular part independent of input derivatives

The two genuine final convolution steps let the BV component pay no derivative
norm. Only the geometrically small remainder pays the first norm. Consequently
a product of a short first derivative and this long first derivative costs a
square root of the input second norm, plus a geometrically small linear term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem truncatedConvolution_first_bv_two_steps
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' g : ℝ → ℝ} {a b D B : ℝ}
    (hab : a ≤ b) (hp : Continuous p.density) (hp' : Continuous p') (hp'' : Continuous p'')
    (hd : ∀ t, HasDerivAt p.density (p' t) t) (hdd : ∀ t, HasDerivAt p' (p'' t) t)
    (hpD : ∀ t, p.density t ≤ D) (hB : 0 ≤ B) (hg : Integrable g volume)
    (hs : ∀ z, z ∉ Icc a b → g z = 0)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B) (y : ℝ) :
    |truncatedConvolution a b p' (truncatedConvolution a b p.density g) y| ≤
      D * B * (1 + 2 * D * (b - a)) := by
  have hD : 0 ≤ D := (p.nonneg 0).trans (hpD 0)
  have hbv : BoundedVariationOn (fun z => (g z : ℂ)) univ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hV : (eVariationOn (fun z => (g z : ℂ)) univ).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  have hmass := integral_abs_bv_support_le hab hB hg hs hvar
  have hc' : Continuous (truncatedConvolution a b p' g) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp' hp'' hdd hg.integrableOn t).continuousAt
  have hb (t : ℝ) : |truncatedConvolution a b p' g t| ≤ D * B :=
    (truncatedConvolution_first_bv_bound hp hp' hd p.nonneg hpD hg hs hbv t).trans
      (mul_le_mul_of_nonneg_left hV hD)
  have h := abs_truncatedConvolution_second_le hab hp hp' p.integrable hc' hd
    (hasDerivAt_truncatedConvolution hp hp' hd hg.integrableOn)
    (mul_nonneg hD hB) (fun t _ => hb t) y
  rw [show (∫ t, |p.density t|) = 1 by
    simp_rw [abs_of_nonneg (p.nonneg _)]
    exact p.integral_eq_one] at h
  have he (t : ℝ) : |truncatedConvolution a b p.density g t| ≤ D * ((b - a) * B) :=
    (abs_truncatedConvolution_le_density_bound p.measurable p.nonneg hpD hg hs t).trans
      (mul_le_mul_of_nonneg_left hmass hD)
  have hpa : |p.density (y - a)| ≤ D := by rw [abs_of_nonneg (p.nonneg _)]; exact hpD _
  have hpb : |p.density (y - b)| ≤ D := by rw [abs_of_nonneg (p.nonneg _)]; exact hpD _
  calc
    _ ≤ D * B * 1 + |p.density (y - a)| *
        |truncatedConvolution a b p.density g a| + |p.density (y - b)| *
        |truncatedConvolution a b p.density g b| := h
    _ ≤ D * B * 1 + D * (D * ((b - a) * B)) + D * (D * ((b - a) * B)) := by
      gcongr
      · exact he a
      · exact he b
    _ = _ := by ring

theorem truncatedConvolution_first_of_decomposition
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' g r : ℝ → ℝ} {a b D B R : ℝ}
    (hab : a ≤ b) (hp : Continuous p.density) (hp' : Continuous p') (hp'' : Continuous p'')
    (hpi' : Integrable p' volume) (hd : ∀ t, HasDerivAt p.density (p' t) t)
    (hdd : ∀ t, HasDerivAt p' (p'' t) t) (hpD : ∀ t, p.density t ≤ D) (hB : 0 ≤ B)
    (hg : Integrable g volume) (hr : Integrable r volume) (hr2 : MemLp r 2 volume)
    (hs : ∀ z, z ∉ Icc a b → g z = 0 ∧ r z = 0)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B)
    (hR : Real.sqrt (∫ z, r z ^ 2) ≤ R) (y : ℝ) :
    |truncatedConvolution a b p' (truncatedConvolution a b p.density (g + r)) y| ≤
      D * B * (1 + 2 * D * (b - a)) + (∫ t, |p' t|) * Real.sqrt D * R := by
  have hG := truncatedConvolution_first_bv_two_steps p hab hp hp' hp'' hd hdd hpD hB hg
    (fun z hz => (hs z hz).1) hvar y
  have hR' := truncatedConvolution_second_remainder_bound p hp hp' hd hpi' hpD hr hr2
    (fun z hz => (hs z hz).2) y
  have hRb := hR'.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hcg : Continuous (truncatedConvolution a b p.density g) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp hp' hd hg.integrableOn t).continuousAt
  have hcr : Continuous (truncatedConvolution a b p.density r) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp hp' hd hr.integrableOn t).continuousAt
  have he : truncatedConvolution a b p.density (g + r) =
      truncatedConvolution a b p.density g + truncatedConvolution a b p.density r := by
    funext t
    exact truncatedConvolution_add hp hg.integrableOn hr.integrableOn t
  rw [he, truncatedConvolution_add hp'
    (hcg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hcr.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  exact (abs_add_le _ _).trans (add_le_add hG hRb)

theorem krDens_first_of_decomposition
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {f' f'' g r : ℝ → ℝ} {w β a D B R : ℝ}
    (hw : 0 ≤ w) (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t) (hpD : ∀ t, p.density t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (p.density x)))
    (ha : a ≠ 0) (n : ℕ) (x : ℝ) (hB : 0 ≤ B)
    (hg : Integrable g volume) (hr : Integrable r volume) (hr2 : MemLp r 2 volume)
    (hs : ∀ z, z ∉ Icc 0 w → g z = 0 ∧ r z = 0)
    (hdecomp : ∀ z, krDens (Icc 0 w) ν p.density β a (n + 1) x z = g z + r z)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B)
    (hR : Real.sqrt (∫ z, r z ^ 2) ≤ R) (y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (fun z => krDens (Icc 0 w) ν p.density β a (n + 2) x z) y| ≤
      (D / |a|) * B * (1 + 2 * (D / |a|) * w) +
        ((∫ t, |f' t|) / |a|) * Real.sqrt (D / |a|) * R := by
  have hpD' : ∀ t, (kepStepDensity p β a ha).density t ≤ D / |a| := fun t =>
    div_le_div_of_nonneg_right (hpD _) (abs_nonneg a)
  have hh := truncatedConvolution_first_of_decomposition (kepStepDensity p β a ha)
    (a := 0) (b := w) hw (continuous_kepStepSpatial hp β a)
    (continuous_kepStepSpatialFirst hp' β a) (continuous_kepStepSpatialSecond hp'' β a)
    (integrable_kepStepSpatialFirst hpi' ha β)
    (hasDerivAt_kepStepSpatial hd β a) (hasDerivAt_kepStepSpatialFirst hdd β a)
    hpD' hB hg hr hr2 hs hvar hR y
  change |truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
    (truncatedConvolution 0 w (kepStepSpatial p.density β a) (g + r)) y| ≤ _ at hh
  simp only [sub_zero, integral_abs_kepStepSpatialFirst f' β ha] at hh
  have he : truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (fun z => krDens (Icc 0 w) ν p.density β a (n + 2) x z) y =
      truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (truncatedConvolution 0 w (kepStepSpatial p.density β a) (g + r)) y := by
    unfold truncatedConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [krDens_eq_kepFinalConvolution ν (β := β) p.measurable p.nonneg hpD hν ha n x
      ⟨hz.1.le, hz.2⟩]
    unfold kepFinalConvolution truncatedConvolution
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    rw [hdecomp]
    rfl
  rw [he]
  exact hh

def kepLongFirstBudget (D vlo vhi w : ℝ) (k : ℕ) (J1 : ℝ) : ℝ :=
  2 * D * kepLongUniformVariation D vlo vhi w k * (1 + 4 * D * w) +
    2 * J1 * Real.sqrt (2 * D) * kepLongUniformRemainder D vlo vhi w k

/-- At every endpoint, the regular term is independent of all input derivative
norms. The actual killed-row decomposition is proved, rather than assumed. -/
theorem krDens_first_long_uniform_bound
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν p.density w A a β a') {f' f'' : ℝ → ℝ}
    (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t) (m k : ℕ) (hk : 8 ≤ k) (x y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialFirst f' β a')
      (fun z => krDens (Icc 0 w) ν p.density β a' (m + k + 2) x z) y| ≤
      kepLongFirstBudget D vlo vhi w k (∫ t, |f' t|) := by
  obtain ⟨g, r, -, hg, -, -, hr, hr2, hs, hsum, hvar, hR⟩ :=
    krDens_long_real_decomposition ν H m k hk x
  have hb := krDens_first_of_decomposition p ν H.hw0.le hp hp' hp'' hpi' hd hdd
    H.hfD H.hνf H.ha' (m + k) x (kepLongRowVarBudget_nonneg ν H m k x)
    hg hr hr2 hs (fun z => by
      simpa only [show m + k + 1 = m + 1 + k by omega] using hsum z) hvar hR y
  have hD : 0 < D := H.hD
  have ha : 1 / 2 ≤ |a'| := H.ha₁'
  have ha0 : 0 < |a'| := by linarith
  have hDa : D / |a'| ≤ 2 * D := (div_le_iff₀ ha0).mpr (by nlinarith)
  have hJ : 0 ≤ ∫ t, |f' t| := integral_nonneg (fun _ => abs_nonneg _)
  have hJa : (∫ t, |f' t|) / |a'| ≤ 2 * (∫ t, |f' t|) :=
    (div_le_iff₀ ha0).mpr (by nlinarith)
  have hV := kepLongRowVarBudget_le_uniform ν H m k x
  have hR' := kepLongRowRemBudget_le_uniform ν H m k x
  have hV0 := kepLongRowVarBudget_nonneg ν H m k x
  have hVU := kepLongUniformVariation_nonneg (w := w) k H.hD H.hvlo H.hvhi
  have hw0 : 0 ≤ w := H.hw0.le
  have hR0 : 0 ≤ kepLongRowRemBudget ν p.density D vlo vhi w β a' m k x := by
    dsimp [kepLongRowRemBudget, kepLongRowEnergy]
    positivity
  apply hb.trans
  unfold kepLongFirstBudget
  apply add_le_add
  · apply mul_le_mul
    · exact mul_le_mul hDa hV hV0 (by positivity)
    · have hh := mul_le_mul_of_nonneg_right hDa hw0
      linarith
    · positivity
    · positivity
  · apply mul_le_mul
    · exact mul_le_mul hJa (Real.sqrt_le_sqrt hDa) (Real.sqrt_nonneg _) (by positivity)
    · exact hR'
    · exact hR0
    · positivity

theorem kepLongFirstBudget_le_second_budget {D vlo vhi w J1 : ℝ} (k : ℕ)
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 1 ≤ w) (hJ1 : 0 ≤ J1) :
    kepLongFirstBudget D vlo vhi w k J1 ≤
      (1 + 2 * D) * kepLongSecondSlopeBudget D vlo vhi w k 1 J1 := by
  have hV := kepLongUniformVariation_nonneg (w := w) k hD hvlo hvhi
  have hR := kepLongUniformRemainder_nonneg D vlo vhi w k
  have hlow : 1 + 4 * D * w ≤ (1 + 2 * D) * (3 + 2 * w) := by nlinarith
  have hrough : 2 ≤ (1 + 2 * D) * 6 := by linarith
  unfold kepLongFirstBudget kepLongSecondSlopeBudget
  rw [mul_add (1 + 2 * D)]
  apply add_le_add
  · calc
      _ ≤ 2 * D * kepLongUniformVariation D vlo vhi w k *
          ((1 + 2 * D) * (3 + 2 * w)) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = _ := by ring
  · calc
      _ = 2 * (J1 * Real.sqrt (2 * D) * kepLongUniformRemainder D vlo vhi w k) := by ring
      _ ≤ ((1 + 2 * D) * 6) *
          (J1 * Real.sqrt (2 * D) * kepLongUniformRemainder D vlo vhi w k) :=
        mul_le_mul_of_nonneg_right hrough (by positivity)
      _ = _ := by ring

theorem tsum_polynomial_weighted_kepLongFirstBudget_tail_le
    {D vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ w eta : ℝ, 1 ≤ w →
      eta ≤ krKappa D vlo vhi / (16 * w ^ 2) → ∀ N : ℕ, ∀ J1 : ℝ,
      0 ≤ J1 →
      Summable (fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
        kepLongFirstBudget D vlo vhi w (k + N) J1) ∧
      (∑' k : ℕ, (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
        kepLongFirstBudget D vlo vhi w (k + N) J1) ≤
      K * w ^ (2 * p + 4) * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * J1) := by
  obtain ⟨K, hK, hsum⟩ :=
    tsum_polynomial_weighted_kepLongSecondSlopeBudget_tail_le hD hvlo hvhi p
  have hC : 0 < 1 + 2 * D := by linarith
  refine ⟨(1 + 2 * D) * K, by positivity, ?_⟩
  intro w eta hw heta N J1 hJ1
  have hκ := krKappa_pos hD hvlo hvhi
  have heta' : eta < krKappa D vlo vhi / (8 * w ^ 2) := by
    apply heta.trans_lt
    apply div_lt_div_of_pos_left hκ (by positivity)
    nlinarith
  let G := fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
    kepLongSecondSlopeBudget D vlo vhi w (k + N) 1 J1
  have hsG : Summable G := by
    convert (summable_nat_add_iff N).2
      (summable_polynomial_weighted_kepLongSecondSlopeBudget (J1 := 1) (J2 := J1)
        hD hvlo hvhi hw heta' p) using 1 <;> first
    | rfl
    | (funext k; simp only [G, Nat.cast_add])
  have hb (k : ℕ) : (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
      kepLongFirstBudget D vlo vhi w (k + N) J1 ≤ (1 + 2 * D) * G k := by
    calc
      _ ≤ (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
          ((1 + 2 * D) * kepLongSecondSlopeBudget D vlo vhi w (k + N) 1 J1) :=
        mul_le_mul_of_nonneg_left
          (kepLongFirstBudget_le_second_budget (k + N) hD hvlo hvhi hw hJ1) (by positivity)
      _ = _ := by dsimp [G]; ring
  have hnonneg (k : ℕ) : 0 ≤ (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
      kepLongFirstBudget D vlo vhi w (k + N) J1 := by
    have hV := kepLongUniformVariation_nonneg (w := w) (k + N) hD hvlo hvhi
    have hR := kepLongUniformRemainder_nonneg D vlo vhi w (k + N)
    dsimp [kepLongFirstBudget]
    have hw0 : 0 ≤ w := by linarith
    positivity
  have hs := (hsG.mul_left (1 + 2 * D)).of_nonneg_of_le hnonneg hb
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, (1 + 2 * D) * G k := hs.tsum_le_tsum hb (hsG.mul_left _)
    _ = (1 + 2 * D) * ∑' k : ℕ, G k := tsum_mul_left
    _ ≤ (1 + 2 * D) *
        (K * w ^ (2 * p + 4) * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * J1)) :=
      mul_le_mul_of_nonneg_left (hsum w eta hw heta N 1 J1 (by norm_num) hJ1) hC.le
    _ = _ := by ring

end

end PGM
