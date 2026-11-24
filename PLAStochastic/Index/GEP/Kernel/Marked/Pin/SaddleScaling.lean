import PLAStochastic.Index.GEP.Kernel.Marked.Pin.TiltedDensity

/-! # Actual gap scaling and the slope-one normalization at the canonical saddle -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The actual probability law of the scaled gap. -/
def kernelScaledLaw (ν : ProbabilityMeasure ℝ) (s : ℝ) : ProbabilityMeasure ℝ :=
  ν.map (show AEMeasurable (fun x : ℝ => s * x) (ν : Measure ℝ) from by fun_prop)

/-- The fixed Lebesgue density representative after scaling the gap coordinate. -/
def kernelScaledDensity (s : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x / s) / |s|

/-- The selected scaled density represents the actual pushforward law. -/
theorem kernel_scaled_density_measure (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {s : ℝ} (hs : s ≠ 0) :
    (kernelScaledLaw ν s : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (kernelScaledDensity s f x)) := by
  rw [kernelScaledLaw, ProbabilityMeasure.toMeasure_map, hνf]
  ext A hA
  have hpre : MeasurableSet ((fun x : ℝ => s * x) ⁻¹' A) := (by fun_prop :
    Measurable (fun x : ℝ => s * x)) hA
  rw [Measure.map_apply (by fun_prop) hA, withDensity_apply _ hpre, withDensity_apply _ hA]
  have hvol : (volume : Measure ℝ) =
      ENNReal.ofReal |s⁻¹| • (volume.map (fun z => s⁻¹ * z)) :=
    (Real.smul_map_volume_mul_left (inv_ne_zero hs)).symm
  calc
    ∫⁻ x in (fun x : ℝ => s * x) ⁻¹' A, ENNReal.ofReal (f x) =
        ∫⁻ x, ((fun x : ℝ => s * x) ⁻¹' A).indicator (fun x => ENNReal.ofReal (f x)) x :=
      (lintegral_indicator hpre _).symm
    _ = ENNReal.ofReal |s⁻¹| * ∫⁻ z, ((fun x : ℝ => s * x) ⁻¹' A).indicator
        (fun x => ENNReal.ofReal (f x)) (s⁻¹ * z) := by
      conv_lhs => rw [hvol]
      rw [lintegral_smul_measure, (measurableEmbedding_mulLeft₀ (inv_ne_zero hs)).lintegral_map,
        smul_eq_mul]
    _ = ENNReal.ofReal |s⁻¹| * ∫⁻ z, A.indicator (fun z => ENNReal.ofReal (f (z / s))) z := by
      congr 1
      apply lintegral_congr
      intro z
      have he : s * (z / s) = z := by field_simp
      have hfarg : s⁻¹ * z = z / s := by ring
      by_cases hz : z ∈ A <;> simp [Set.mem_preimage, he, hz, hfarg]
    _ = ∫⁻ z in A, ENNReal.ofReal (kernelScaledDensity s f z) := by
      rw [lintegral_indicator hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      simp only [kernelScaledDensity, abs_inv]
      ring

/-- The actual complex step is unchanged when scaling gaps and dividing the slope. -/
theorem kernel_kStep_scaled (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (β a : ℝ)
    {s : ℝ} (hs : s ≠ 0) :
    kStep J (kernelScaledLaw ν s : Measure ℝ) β (a / s) = kStep J (ν : Measure ℝ) β a := by
  rw [kernelScaledLaw, ProbabilityMeasure.toMeasure_map]
  funext u y
  by_cases hy : y ∈ J
  · simp only [kStep, indicator_of_mem hy]
    rw [(measurableEmbedding_mulLeft₀ hs).integral_map]
    congr 1
    funext x
    congr 1
    field_simp
  · simp only [kStep, indicator_of_notMem hy]

/-- The real step has the same exact coordinate scaling. -/
theorem kernel_krStep_scaled (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (β a : ℝ)
    {s : ℝ} (hs : s ≠ 0) :
    krStep J (kernelScaledLaw ν s : Measure ℝ) β (a / s) = krStep J (ν : Measure ℝ) β a := by
  rw [kernelScaledLaw, ProbabilityMeasure.toMeasure_map]
  funext u y
  by_cases hy : y ∈ J
  · simp only [krStep, indicator_of_mem hy]
    rw [(measurableEmbedding_mulLeft₀ hs).integral_map]
    congr 1
    funext x
    congr 1
    field_simp
  · simp only [krStep, indicator_of_notMem hy]

/-- Row equality is pointwise and leaves both residual endpoints untouched. -/
theorem kernel_krRow_scaled (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (β a : ℝ)
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) (φ : ℝ → ℝ) :
    krRow J (kernelScaledLaw ν s : Measure ℝ) β (a / s) n φ =
      krRow J (ν : Measure ℝ) β a n φ := by
  simp only [krRow, kernel_krStep_scaled J ν β a hs]

/-- The gap-density Jacobian cancels the slope Jacobian in the residual kernel. -/
theorem kernel_krKer_scaled (J : Set ℝ) (f : ℝ → ℝ) (β a : ℝ)
    {s : ℝ} (hs : s ≠ 0) (y z : ℝ) :
    krKer J (kernelScaledDensity s f) β (a / s) y z = krKer J f β a y z := by
  by_cases ha : a = 0
  · simp [ha, krKer]
  have he : ((y + β - z) / (a / s)) / s = (y + β - z) / a := by field_simp
  unfold krKer kernelScaledDensity
  rw [he, abs_div]
  have hsabs : |s| ≠ 0 := abs_ne_zero.mpr hs
  have haabs : |a| ≠ 0 := abs_ne_zero.mpr ha
  field_simp

/-- The actual path-defined densities coincide at every endpoint, without another Jacobian. -/
theorem kernel_krDens_scaled {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) {s : ℝ} (hs : s ≠ 0) (n : ℕ) (y z : ℝ) :
    krDens J (kernelScaledLaw ν s) (kernelScaledDensity s f) β (a / s) n y z =
      krDens J ν f β a n y z := by
  have hfs : Measurable (kernelScaledDensity s f) := by unfold kernelScaledDensity; fun_prop
  have hfs0 (x : ℝ) : 0 ≤ kernelScaledDensity s f x := div_nonneg (hf0 _) (abs_nonneg _)
  have hfsD (x : ℝ) : kernelScaledDensity s f x ≤ D / |s| :=
    div_le_div_of_nonneg_right (hfD _) (abs_nonneg _)
  rw [kernel_krDens_eq_iterate hJ _ hfs hfs0 hfsD, kernel_krStep_scaled J ν β a hs,
    kernel_krDens_eq_iterate hJ ν hf hf0 hfD]
  simp_rw [kernel_krKer_scaled J f β a hs]


/-- The explicit tilted representative retains a pointwise exponential envelope. -/
theorem RegLaw.kernel_tilt_density_envelope {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {f : ℝ → ℝ} (hfz : ∀ x ≤ 0, f x = 0)
    (hfe : ∀ x, f x ≤ D * Real.exp (-θ * x))
    {lam : ℝ} (hlam : |lam| ≤ θ / 2) (x : ℝ) :
    kernelTiltDensity ν lam f x ≤ (D * Real.exp θ) * Real.exp (-(θ / 2) * x) := by
  have hU := hν.univClass hθ hvlo
  have hmgf : 1 ≤ mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam :=
    hU.one_le_integral_exp_centered hlam
  have hcgf : 0 ≤ cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam := Real.log_nonneg hmgf
  have hraw : lam ≤ cgf id (ν : Measure ℝ) lam := by
    rw [hU.kernel_raw_cgf_eq hlam]
    linarith
  by_cases hx : 0 < x
  · have he : -θ * x + (lam * x - cgf id (ν : Measure ℝ) lam) ≤ θ - θ / 2 * x := by
      have hh := mul_le_mul_of_nonneg_right (abs_le.mp hlam).2 hx.le
      have hn := (abs_le.mp hlam).1
      nlinarith
    calc
      kernelTiltDensity ν lam f x ≤
          Real.exp (lam * x - cgf id (ν : Measure ℝ) lam) * (D * Real.exp (-θ * x)) :=
        mul_le_mul_of_nonneg_left (hfe x) (Real.exp_nonneg _)
      _ = D * Real.exp (-θ * x + (lam * x - cgf id (ν : Measure ℝ) lam)) := by
        rw [Real.exp_add]
        ring
      _ ≤ D * Real.exp (θ - θ / 2 * x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hν.D_nonneg
      _ = (D * Real.exp θ) * Real.exp (-(θ / 2) * x) := by rw [Real.exp_sub, neg_mul, Real.exp_neg]; ring
  · simp only [kernelTiltDensity, hfz x (not_lt.mp hx), mul_zero]
    exact mul_nonneg (mul_nonneg hν.D_nonneg (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-- Scaling by `1/2 ≤ s ≤ 2` retains the actual representative's positive exponential envelope. -/
theorem kernel_scaled_density_envelope {D θ s : ℝ} {f : ℝ → ℝ}
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hslo : 1 / 2 ≤ s) (hshi : s ≤ 2)
    (hfz : ∀ x ≤ 0, f x = 0) (hfe : ∀ x, f x ≤ D * Real.exp (-θ * x)) (x : ℝ) :
    kernelScaledDensity s f x ≤ (2 * D) * Real.exp (-(θ / 2) * x) := by
  have hs : 0 < s := by linarith
  by_cases hx : 0 < x
  · have hfrac : x / 2 ≤ x / s :=
      div_le_div_of_nonneg_left hx.le hs hshi
    have hex : Real.exp (-θ * (x / s)) ≤ Real.exp (-(θ / 2) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hfrac hθ]
    calc
      kernelScaledDensity s f x = f (x / s) / s := by rw [kernelScaledDensity, abs_of_pos hs]
      _ ≤ (D * Real.exp (-θ * (x / s))) / s := div_le_div_of_nonneg_right (hfe _) hs.le
      _ ≤ (2 * D) * Real.exp (-θ * (x / s)) := by
        rw [div_le_iff₀ hs]
        have hh := mul_le_mul_of_nonneg_right hslo
          (show 0 ≤ D * Real.exp (-θ * (x / s)) by positivity)
        nlinarith
      _ ≤ (2 * D) * Real.exp (-(θ / 2) * x) := mul_le_mul_of_nonneg_left hex (by positivity)
  · rw [kernelScaledDensity, hfz (x / s) (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hx) hs.le), zero_div]
    positivity

/-- Canonical saddles turn the actual tilted row into a slope-one regular row.
The explicit representative has all pointwise support and envelope facts required by KrBand. -/
theorem kernel_regLaw_saddle_scaled (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ a : ℝ, |a - 1| ≤ δ →
          let lam := kernelTiltSaddle D θ vlo ν a
          ∃ τ : ProbabilityMeasure ℝ,
            (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) ∧
            (τ : Measure ℝ) = volume.withDensity
              (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) ∧
            |lam| ≤ kernelTiltClassRadius D θ vlo vhi ∧
            c * (a - 1) ^ 2 ≤ kernelTiltRate ν a lam ∧
            RegLaw (2 * D * Real.exp θ) (θ / 4) (3 * vlo / 16) (5 * vhi) (kernelScaledLaw τ a) ∧
            (kernelScaledLaw τ a : Measure ℝ) = volume.withDensity
              (fun x => ENNReal.ofReal (kernelScaledDensity a (kernelTiltDensity ν lam f) x)) ∧
            Measurable (kernelScaledDensity a (kernelTiltDensity ν lam f)) ∧
            (∀ x, 0 ≤ kernelScaledDensity a (kernelTiltDensity ν lam f) x) ∧
            (∀ x ≤ 0, kernelScaledDensity a (kernelTiltDensity ν lam f) x = 0) ∧
            (∀ x, kernelScaledDensity a (kernelTiltDensity ν lam f) x ≤ 2 * D * Real.exp θ) ∧
            (∀ x, kernelScaledDensity a (kernelTiltDensity ν lam f) x ≤
              (2 * D * Real.exp θ) * Real.exp (-(θ / 4) * x)) ∧
            (∀ J : Set ℝ, ∀ β : ℝ, ∀ n : ℕ, ∀ φ : ℝ → ℝ,
              krRow J (τ : Measure ℝ) β (β * a) n φ = krRow J (kernelScaledLaw τ a : Measure ℝ) β β n φ) ∧
            (∀ J : Set ℝ, MeasurableSet J → ∀ β : ℝ, ∀ n : ℕ, ∀ y z : ℝ,
              krDens J τ (kernelTiltDensity ν lam f) β (β * a) n y z =
                krDens J (kernelScaledLaw τ a) (kernelScaledDensity a (kernelTiltDensity ν lam f))
                  β β n y z) := by
  obtain ⟨δ, c, hδ, hδhi, hc, hnorm⟩ := kernel_regLaw_saddle_normalized D θ vlo vhi hD hθ hvlo hv
  refine ⟨δ, c, hδ, hδhi, hc, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfz, hfe, hνf⟩ := hν.density
  have hfD (x : ℝ) : f x ≤ D := by
    by_cases hx : 0 < x
    · exact (hfe x).trans (mul_le_of_le_one_right hD.le
        (Real.exp_le_one_iff.mpr (by nlinarith)))
    · rw [hfz x (not_lt.mp hx)]
      exact hD.le
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro a ha
  dsimp only
  let lam := kernelTiltSaddle D θ vlo ν a
  obtain ⟨hlam, _, hrate, ρ, hρ, hρreg⟩ := hnorm ν hν a ha
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp ha).1]
  have hahi : a ≤ 2 := by linarith [(abs_le.mp ha).2]
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) := rfl
  have hτf : (τ : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) :=
    kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hl)
  have hρeq : kernelScaledLaw τ a = ρ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [kernelScaledLaw, ProbabilityMeasure.toMeasure_map, hτ, hρ]
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x := mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hftz (x : ℝ) (hx : x ≤ 0) : kernelTiltDensity ν lam f x = 0 := by
    simp only [kernelTiltDensity, hfz x hx, mul_zero]
  have hfte (x : ℝ) : kernelTiltDensity ν lam f x ≤
      (D * Real.exp θ) * Real.exp (-(θ / 2) * x) := hν.kernel_tilt_density_envelope hθ hvlo hfz hfe hl x
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hl x
  refine ⟨τ, hτ, hτf, hlam, hrate, hρeq.symm ▸ hρreg, kernel_scaled_density_measure τ hτf ha0.ne',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kernelScaledDensity
    fun_prop
  · intro x
    exact div_nonneg (hft0 _) (abs_nonneg _)
  · intro x hx
    rw [kernelScaledDensity, hftz (x / a) (div_nonpos_of_nonpos_of_nonneg hx ha0.le), zero_div]
  · intro x
    rw [kernelScaledDensity, abs_of_pos ha0]
    apply (div_le_div_of_nonneg_right (hftD _) ha0.le).trans
    rw [div_le_iff₀ ha0]
    have hh := mul_le_mul_of_nonneg_right halo (show 0 ≤ D * Real.exp θ by positivity)
    nlinarith
  · intro x
    have hh := kernel_scaled_density_envelope (by positivity) (by positivity : 0 ≤ θ / 2)
      halo hahi hftz hfte x
    rw [show 2 * (D * Real.exp θ) = 2 * D * Real.exp θ by ring,
      show (θ / 2) / 2 = θ / 4 by ring] at hh
    exact hh
  · intro J β n φ
    simpa only [mul_div_cancel_right₀ _ ha0.ne'] using
      (kernel_krRow_scaled J τ β (β * a) ha0.ne' n φ).symm
  · intro J hJ β n y z
    simpa only [mul_div_cancel_right₀ _ ha0.ne'] using
      (kernel_krDens_scaled hJ τ hft hft0 hftD β (β * a) ha0.ne' n y z).symm

end
end PGM
