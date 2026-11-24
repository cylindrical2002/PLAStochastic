import PLAStochastic.Swing.Gaussian.Bridge.ChangeOfMeasure

/-! Elementary horizon-to-infinity limits for the Gaussian bridge density.
These lemmas isolate the vanishing exponential correction that appears in the
Radon--Nikodym factor when the remainder variance diverges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair

/-- The bridge's endpoint exponential correction vanishes as the remainder
variance tends to infinity. -/
theorem gaussianBridge_exponential_correction_tendsto_one
    {m : ℕ} {r : ℕ → ℝ≥0} {z : Fin m → ℝ}
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun k => Real.exp
      (-((∑ i, z i)^2) / (2 * (r k : ℝ)))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun k => ((r k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr hr)
  have harg : Tendsto (fun k =>
      -((∑ i, z i)^2) / (2 * (r k : ℝ))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => -((∑ i, z i)^2) / 2) atTop
        (𝓝 (-((∑ i, z i)^2) / 2)) := tendsto_const_nhds
    have hm := hc.mul hinv
    convert hm using 1
    · funext k
      field_simp
    · norm_num
  have he := (Real.continuous_exp.continuousAt.tendsto.comp harg)
  change Tendsto (Real.exp ∘ (fun k => -((∑ i, z i)^2) / (2 * (r k : ℝ)))) atTop (𝓝 1)
  simpa only [Real.exp_zero] using he

/-- The same correction converges to one after the bridge density's
`ENNReal.ofReal` coercion. -/
theorem gaussianBridge_exponential_correction_enn_tendsto_one
    {m : ℕ} {r : ℕ → ℝ≥0} {z : Fin m → ℝ}
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun k => ENNReal.ofReal (Real.exp
      (-((∑ i, z i)^2) / (2 * (r k : ℝ))))) atTop (𝓝 1) := by
  simpa using ENNReal.tendsto_ofReal
    (gaussianBridge_exponential_correction_tendsto_one (m := m) (r := r) (z := z) hr)

end SwingRepair

namespace SwingRepair
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

/-- Real-valued form of the bridge density, separating the variance ratio and
    the endpoint exponential correction. -/
theorem gaussianBridgeProductDensity_real_formula
    (m : ℕ) {r : ℝ≥0} (hr : 0 < r) (z : Fin m → ℝ) :
    gaussianPDFReal 0 r (-(∑ i, z i))/gaussianPDFReal 0 ((m : ℝ≥0)+r) 0 =
      Real.sqrt (((m : ℝ) + r) / r) * Real.exp
        (-((∑ i, z i)^2)/(2*(r:ℝ))) := by
  simp only [gaussianPDFReal, sub_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one, NNReal.coe_add, NNReal.coe_natCast]
  have hrR : (0 : ℝ) < r := hr
  have hmr : 0 < (m : ℝ) + r := by positivity
  field_simp
  have hB : 0 ≤ (2 * Real.pi * (r : ℝ)) := by positivity
  have hid : (2 * Real.pi * (r : ℝ)) * (((m : ℝ)+r) / r) =
      2 * Real.pi * ((m : ℝ)+r) := by
    field_simp
  rw [← hid, Real.sqrt_mul hB]

/-- Pointwise finite-dimensional bridge densities converge to unit density as
    the remainder variance diverges. -/
theorem gaussianBridgeProductDensity_tendsto_one
    {m : ℕ} {r : ℕ → ℝ≥0} {z : Fin m → ℝ}
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun k => gaussianBridgeProductDensity m (r k) z) atTop (𝓝 1) := by
  have hR1 : ∀ᶠ k in atTop, (1 : ℝ≥0) ≤ r k :=
    hr.eventually (eventually_ge_atTop (1 : ℝ≥0))
  have hR : ∀ᶠ k in atTop, 0 < r k := by
    filter_upwards [hR1] with k hk
    exact lt_of_lt_of_le zero_lt_one hk
  have hinv : Tendsto (fun k => ((r k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr hr)
  have hratio : Tendsto (fun k => ((m : ℝ) + (r k : ℝ)) / (r k : ℝ))
      atTop (𝓝 1) := by
    have hm : Tendsto (fun k : ℕ => (m : ℝ) * ((r k : ℝ))⁻¹)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hinv :
          Tendsto (fun k : ℕ => (m : ℝ) * ((r k : ℝ))⁻¹) atTop (𝓝 ((m : ℝ) * 0)))
    have hconst1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hadd := hconst1.add hm
    have heq : (fun k : ℕ => ((m : ℝ) + (r k : ℝ)) / (r k : ℝ)) =ᶠ[atTop]
        (fun k => 1 + (m : ℝ) * ((r k : ℝ))⁻¹) := by
      filter_upwards [hR] with k hk
      field_simp
      ring
    have hh := hadd.congr' heq.symm
    simpa only [add_zero] using hh
  have hsqrt : Tendsto (fun k => Real.sqrt (((m : ℝ) + (r k : ℝ)) / (r k : ℝ)))
      atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
    change Tendsto (fun k => Real.sqrt (((m : ℝ) + (r k : ℝ)) / (r k : ℝ))) atTop (𝓝 1)
    simpa [Function.comp_def] using h
  have hexp := gaussianBridge_exponential_correction_tendsto_one
    (m := m) (r := r) (z := z) hr
  have hmul := hsqrt.mul hexp
  have hformula : ∀ᶠ k in atTop,
      gaussianBridgeProductDensity m (r k) z = ENNReal.ofReal
        (Real.sqrt (((m : ℝ) + (r k : ℝ)) / (r k : ℝ)) *
          Real.exp (-((∑ i, z i)^2)/(2*(r k : ℝ)))) := by
    filter_upwards [hR] with k hk
    rw [gaussianBridgeProductDensity, gaussianBridgeProductDensity_real_formula m hk z]
  have hof := ENNReal.tendsto_ofReal hmul
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
  have hformula' : (fun k => ENNReal.ofReal
      (Real.sqrt (((m : ℝ) + (r k : ℝ)) / (r k : ℝ)) *
        Real.exp (-((∑ i, z i)^2)/(2*(r k : ℝ))))) =ᶠ[atTop]
      (fun k => gaussianBridgeProductDensity m (r k) z) := by
    filter_upwards [hformula] with k hk
    exact hk.symm
  have hof' : Tendsto (fun k => ENNReal.ofReal
      (Real.sqrt (((m : ℝ) + (r k : ℝ)) / (r k : ℝ)) *
        Real.exp (-((∑ i, z i)^2)/(2*(r k : ℝ))))) atTop (𝓝 (ENNReal.ofReal 1)) := by
    simpa using hof
  exact hof'.congr' hformula'

end SwingRepair

namespace SwingRepair
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

/-- Event probabilities under the finite bridge density converge to the
    corresponding unconditioned Gaussian-prefix probabilities when the
    remainder variance diverges.  The explicit uniform `sqrt 2` density
    bound supplies dominated convergence. -/
theorem gaussianBridgePrefix_event_tendsto_unconditioned
    {m : ℕ} {r : ℕ → ℝ≥0} (hr : Tendsto r atTop atTop)
    (hrm : ∀ k, m ≤ r k) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    Tendsto (fun k =>
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity m (r k))) A) atTop
      (𝓝 ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)) A)) := by
  let P : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 2)
  have hmeas : ∀ᶠ k in atTop, Measurable (A.indicator (gaussianBridgeProductDensity m (r k))) := by
    filter_upwards [] with k
    exact (gaussianBridgeProductDensity_measurable m (r k)).indicator hA
  have hrpos : ∀ᶠ k in atTop, 0 < r k := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ≥0))] with k hk
    exact hk
  have hbound : ∀ᶠ k in atTop, ∀ᵐ z ∂P,
      A.indicator (gaussianBridgeProductDensity m (r k)) z ≤ c := by
    filter_upwards [hrpos] with k hk
    exact Eventually.of_forall (fun z => by
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz]
        apply gaussianBridgeProductDensity_le_sqrt_two m hk
        exact hrm k
      · simp [Set.indicator_of_notMem hz])
  have hfin : ∫⁻ z, c ∂P ≠ ∞ := by
    dsimp [c, P]
    simp
  have hlim : ∀ᵐ z ∂P, Tendsto (fun k =>
      A.indicator (gaussianBridgeProductDensity m (r k)) z) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ≥0∞)) z)) := by
    filter_upwards [] with z
    by_cases hz : z ∈ A
    · simp only [Set.indicator_of_mem hz]
      simpa using (gaussianBridgeProductDensity_tendsto_one (m := m)
        (r := r) (z := z) hr)
    · simp only [Set.indicator_of_notMem hz]
      exact tendsto_const_nhds
  have hdc := tendsto_lintegral_filter_of_dominated_convergence
    (μ := P) (F := fun k => A.indicator (gaussianBridgeProductDensity m (r k)))
    (f := A.indicator (fun _ => (1 : ℝ≥0∞))) (fun _ => c) hmeas hbound hfin hlim
  have hset : ∀ k, ((P.withDensity (gaussianBridgeProductDensity m (r k))) A) =
      ∫⁻ z, A.indicator (gaussianBridgeProductDensity m (r k)) z ∂P := by
    intro k
    rw [withDensity_apply (gaussianBridgeProductDensity m (r k)) hA,
      ← lintegral_indicator hA]
  have hset0 : P A = ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z ∂P := by
    symm
    calc
      (∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z ∂P) = ∫⁻ z in A, (1 : ℝ≥0∞) ∂P :=
        lintegral_indicator hA _
      _ = P A := by simp
  rw [show (fun k =>
      ((P.withDensity (gaussianBridgeProductDensity m (r k))) A)) =
      (fun k => ∫⁻ z, A.indicator (gaussianBridgeProductDensity m (r k)) z ∂P) by
        funext k; exact hset k,
    show P A = ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z ∂P by exact hset0]
  exact hdc

end SwingRepair

namespace SwingRepair
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

/-- The preceding density limit transferred back to the actual iid Gaussian
    sample space.  This is the finite-prefix bridge-to-unconditioned passage
    used in horizon truncation arguments. -/
theorem gaussianBridgePrefix_actual_event_tendsto_unconditioned
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {m : ℕ} {N : ℕ → ℕ}
    (hMN : ∀ k, m < N k)
    (hrem : Tendsto (fun k => ((N k - m : ℕ) : ℝ≥0)) atTop atTop)
    (hrem_m : ∀ k, (m : ℝ≥0) ≤ ((N k - m : ℕ) : ℝ≥0))
    {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    Tendsto (fun k => μ ((gaussianBridgeIncrementPrefix X (N k) m) ⁻¹' A)) atTop
      (𝓝 ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)) A)) := by
  let P : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let r : ℕ → ℝ≥0 := fun k => ((N k - m : ℕ) : ℝ≥0)
  have hbridge : ∀ k, μ ((gaussianBridgeIncrementPrefix X (N k) m) ⁻¹' A) =
      (P.withDensity (gaussianBridgeProductDensity m (r k))) A := by
    intro k
    dsimp [P, r]
    exact gaussianBridgePrefix_prefix_change_of_measure hX hi hG (hMN k) hA
  have hlim := gaussianBridgePrefix_event_tendsto_unconditioned
    (m := m) (r := r) hrem hrem_m hA
  rw [show (fun k => μ ((gaussianBridgeIncrementPrefix X (N k) m) ⁻¹' A)) =
      (fun k => (P.withDensity (gaussianBridgeProductDensity m (r k))) A) by
        funext k; exact hbridge k,
    show P A = (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) A by rfl]
  exact hlim

end SwingRepair
