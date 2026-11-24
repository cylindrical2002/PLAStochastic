import PLAStochastic.Index.GEP.Kernel.Influence.Pins.NonDirac
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.DiracPins
import PLAStochastic.Index.GEP.Kernel.Influence.Reward.PhysicalSum

/-! # Physical coarea with a reconstructed, slope-dependent exterior reward -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_pathWeight_reconstructed {eps : ℝ} {k : ℕ}
    {S : Set ℕ} {W R : (ℕ → ℝ) → ℝ≥0∞} {T : (ℕ → ℝ) → (ℕ → ℝ)}
    (hR : Measurable[kCoordSigma S] R)
    (hT : ∀ g j, j ∈ S → T g j = g j)
    (hWR : ∀ g, W (T g) = R g) (g : ℕ → ℝ) :
    kernelIFPathWeight eps k W (T g) = kernelIFPathWeight eps k R (T g) := by
  have hR' := kernel_coord_measurable_invariant hR T hT g
  unfold kernelIFPathWeight
  by_cases he : T g ∈ kernelIFPathEvent eps k
  · simp only [Set.indicator_of_mem he, hWR, hR']
  · simp only [Set.indicator_of_notMem he]

theorem kernel_IF_left_path_preserves_outer {eps x a : ℝ} {k i j m : ℕ}
    {q : FluxFacetIndex k} (_hq : fluxFacetValid q)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) :
    ∀ g n, n ∈ Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ) →
      kernelIFLeftPath eps x a q i j m g n = g n := by
  intro g n hn
  rcases hn with hn | hn <;> simp only [mem_Iio, mem_Ici] at hn
  · simp only [kernelIFLeftPath, Function.update_of_ne (by omega : n ≠ i),
      Function.update_of_ne (by omega : n ≠ m), Function.update_of_ne (by omega : n ≠ j)]
  · simp only [kernelIFLeftPath, Function.update_of_ne (by omega : n ≠ i),
      Function.update_of_ne (by omega : n ≠ m), Function.update_of_ne (by omega : n ≠ j)]

theorem kernel_IF_right_path_preserves_outer {eps x a : ℝ} {k i j m : ℕ}
    {q : FluxFacetIndex k} (_hq : fluxFacetValid q)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) :
    ∀ g n, n ∈ Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ) →
      kernelIFRightPath eps x a q i j m g n = g n := by
  intro g n hn
  rcases hn with hn | hn <;> simp only [mem_Iio, mem_Ici] at hn
  · simp only [kernelIFRightPath, Function.update_of_ne (by omega : n ≠ i),
      Function.update_of_ne (by omega : n ≠ m), Function.update_of_ne (by omega : n ≠ j)]
  · simp only [kernelIFRightPath, Function.update_of_ne (by omega : n ≠ i),
      Function.update_of_ne (by omega : n ≠ m), Function.update_of_ne (by omega : n ≠ j)]

theorem kernel_IF_left_reconstructed_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hx : 0 < x)
    (hlong : (q.1 : ℕ)+1 < q.2.1)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable W) {R : ℝ → (ℕ → ℝ) → ℝ≥0∞}
    (hR : ∀ a > 0, Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] (R a))
    (hWR : ∀ a > 0, ∀ g, W (kernelIFLeftPath eps x a q i
      (kernelIFPinSmoothing q.2.1 i) ((q.2.2.1 : ℕ)-1) g) = R a g) :
    kernelIFLeftDensity ν (fun u => ENNReal.ofReal (f u)) eps q i
      (kernelIFPinSmoothing q.2.1 i) ((q.2.2.1 : ℕ)-1) W x =
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * R a g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
            (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let j := kernelIFPinSmoothing q.2.1 i
  let m := (q.2.2.1 : ℕ)-1
  have hp := (measurable_kernelIFLeftPath eps q i j m).comp
    (show Measurable (fun z : (ℕ → ℝ) × ℝ => ((x,z.2),z.1)) by fun_prop)
  have hA : Measurable (kernelFacetRestA q i j) := by
    unfold kernelFacetRestA gapKeys
    fun_prop
  have hB : Measurable (kernelFacetRestB q m) := by
    unfold kernelFacetRestB gapKeys
    fun_prop
  have hm : Measurable (fun z : (ℕ → ℝ) × ℝ =>
      ENNReal.ofReal (kernelFacetQ eps q / z.2^2) *
        (ENNReal.ofReal (f (kernelFacetP eps q/z.2-x-kernelFacetRestA q i j z.1)) *
        ENNReal.ofReal (f (kernelFacetQ eps q/z.2-kernelFacetRestB q m z.1)) *
        kernelIFPathWeight eps k W (kernelIFLeftPath eps x z.2 q i j m z.1))) :=
    (by fun_prop : Measurable (fun z : (ℕ → ℝ) × ℝ =>
      ENNReal.ofReal (kernelFacetQ eps q/z.2^2))).mul
      (((hf.ennreal_ofReal.comp (by fun_prop)).mul (hf.ennreal_ofReal.comp (by fun_prop))).mul
        ((measurable_kernelIFPathWeight eps k hW).comp hp))
  rw [kernelIFLeftDensity, lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hrs := hq.1.1
  have hst := hq.1.2
  obtain ⟨hj₁, hj₂, _⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hchange (g : ℕ → ℝ) :
      kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i j m g) =
        kernelIFPathWeight eps k (R a) (kernelIFLeftPath eps x a q i j m g) := by
    apply kernel_IF_pathWeight_reconstructed (hR a ha)
      (kernel_IF_left_path_preserves_outer hq.1 hi₁ hi₂ hj₁ hj₂ (by have := hq.1; omega)
        (by have := hq.1; omega)) (hWR a ha)
  dsimp only [j, m] at hchange
  simp_rw [hchange]
  rw [lintegral_const_mul' _ _ (by finiteness),
    kernel_IF_left_full_pin_integral ν hf hf0 hfD hfneg hν hpos hq ha hx hlong hi₁ hi₂ (hR a ha),
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetQ eps q / a^2 from
      le_of_lt (div_pos hq.2.2 (sq_pos_of_pos ha))),
    div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']

theorem kernel_IF_right_reconstructed_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hx : 0 < x)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable W) {R : ℝ → (ℕ → ℝ) → ℝ≥0∞}
    (hR : ∀ a > 0, Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] (R a))
    (hWR : ∀ a > 0, ∀ g, W (kernelIFRightPath eps x a q i
      (kernelIFPinSmoothing q.2.2.1 i) ((q.2.1 : ℕ)-1) g) = R a g) :
    kernelIFRightDensity ν (fun u => ENNReal.ofReal (f u)) eps q i
      (kernelIFPinSmoothing q.2.2.1 i) ((q.2.1 : ℕ)-1) W x =
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * R a g ∂iidLaw ν) *
        (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
          (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
            (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let j := kernelIFPinSmoothing q.2.2.1 i
  let m := (q.2.1 : ℕ)-1
  have hp := (measurable_kernelIFRightPath eps q i j m).comp
    (show Measurable (fun z : (ℕ → ℝ) × ℝ => ((x,z.2),z.1)) by fun_prop)
  have hA : Measurable (kernelFacetRestRight q i j) := by
    unfold kernelFacetRestRight gapKeys
    fun_prop
  have hB : Measurable (kernelFacetRestLeft q m) := by
    unfold kernelFacetRestLeft gapKeys
    fun_prop
  have hm : Measurable (fun z : (ℕ → ℝ) × ℝ =>
      ENNReal.ofReal (kernelFacetP eps q / z.2^2) *
        (ENNReal.ofReal (f (kernelFacetQ eps q/z.2-x-kernelFacetRestRight q i j z.1)) *
        ENNReal.ofReal (f (kernelFacetP eps q/z.2-kernelFacetRestLeft q m z.1)) *
        kernelIFPathWeight eps k W (kernelIFRightPath eps x z.2 q i j m z.1))) :=
    (by fun_prop : Measurable (fun z : (ℕ → ℝ) × ℝ =>
      ENNReal.ofReal (kernelFacetP eps q/z.2^2))).mul
      (((hf.ennreal_ofReal.comp (by fun_prop)).mul (hf.ennreal_ofReal.comp (by fun_prop))).mul
        ((measurable_kernelIFPathWeight eps k hW).comp hp))
  rw [kernelIFRightDensity, lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hrs := hq.1.1
  have hst := hq.1.2
  obtain ⟨hj₁, hj₂, _⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hchange (g : ℕ → ℝ) :
      kernelIFPathWeight eps k W (kernelIFRightPath eps x a q i j m g) =
        kernelIFPathWeight eps k (R a) (kernelIFRightPath eps x a q i j m g) := by
    apply kernel_IF_pathWeight_reconstructed (hR a ha)
      (kernel_IF_right_path_preserves_outer hq.1 hi₁ hi₂ hj₁ hj₂ (by have := hq.1; omega)
        (by have := hq.1; omega)) (hWR a ha)
  dsimp only [j, m] at hchange
  simp_rw [hchange]
  rw [lintegral_const_mul' _ _ (by finiteness),
    kernel_IF_right_full_pin_integral ν hf hf0 hfD hfneg hν hpos hq ha hx hlong hi₁ hi₂ (hR a ha),
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetP eps q / a^2 from
      le_of_lt (div_pos hq.2.1 (sq_pos_of_pos ha))),
    div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']

end
end PGM
