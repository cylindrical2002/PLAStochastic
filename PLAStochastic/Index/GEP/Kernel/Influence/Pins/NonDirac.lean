import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterSurvival
import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.MarkedLast

/-! # Coarea as actual pins for every non-Dirac marked bridge -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

/-- The product before slope integration: one physical pin for each bridge,
and an arbitrary jointly measurable exterior reward. -/
theorem kernel_IF_left_full_pin_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (hx : 0 < x)
    (hlong : (q.1 : ℕ)+1 < q.2.1)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    (∫⁻ g, ENNReal.ofReal (f (kernelFacetP eps q/a-x-
        kernelFacetRestA q i (kernelIFPinSmoothing q.2.1 i) g)) *
      ENNReal.ofReal (f (kernelFacetQ eps q/a-kernelFacetRestB q ((q.2.2.1 : ℕ)-1) g)) *
      kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i
        (kernelIFPinSmoothing q.2.1 i) ((q.2.2.1 : ℕ)-1) g) ∂iidLaw ν) =
    ENNReal.ofReal (a^2) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
            (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  change r ≤ kernelIFPinSmoothing s i at hjr
  change kernelIFPinSmoothing s i < s at hjs
  change kernelIFPinSmoothing s i ≠ i at hji
  have hrewrite : ∀ g, W (kernelIFLeftPath eps x a q i (kernelIFPinSmoothing s i) (t-1) g) = W g := by
    apply kernel_coord_measurable_invariant hW
    intro g j hj
    rcases hj with hj | hj
    · simp only [mem_Iio] at hj
      simp only [kernelIFLeftPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ t-1), Function.update_of_ne (by omega : j ≠ kernelIFPinSmoothing s i)]
    · simp only [mem_Ici] at hj
      simp only [kernelIFLeftPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ t-1), Function.update_of_ne (by omega : j ≠ kernelIFPinSmoothing s i)]
  have hproj := kernel_IF_left_projection_ae ν hpos (eps := eps) (a := a)
    (f := fun u => ENNReal.ofReal (f u))
    (by intro u hu; rw [hfneg u hu, ENNReal.ofReal_zero]) hx q i (kernelIFPinSmoothing s i) (t-1) W
  have hpath (g : ℕ → ℝ) := kernel_IF_left_full_pins (x := x) hq ha hlong hi₁ hi₂ f g
  let F (g : ℕ → ℝ) := kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x
    (i-r) (s-i-1) b b' (fun j => g (j+r))
  let G (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
    (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s))
  have hF0 (g : ℕ → ℝ) : 0 ≤ F g := kernel_marked_pin_block_nonneg hf0 _ _ _ _ _ _ _ _
  have hG0 (g : ℕ → ℝ) : 0 ≤ G g :=
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)
  have heq : (∫⁻ g, ENNReal.ofReal (f (kernelFacetP eps q/a-x-kernelFacetRestA q i (kernelIFPinSmoothing s i) g)) *
        ENNReal.ofReal (f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g)) *
        kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i (kernelIFPinSmoothing s i) (t-1) g) ∂iidLaw ν) =
      ∫⁻ g, ENNReal.ofReal (a^2) * ((ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g) *
        (ENNReal.ofReal (F g) * ENNReal.ofReal (G g))) ∂iidLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [hproj] with g hg
    rw [kernel_IF_left_weight_blocks hq ha hi₁ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hg, hrewrite]
    have hreal : f (kernelFacetP eps q/a-x-kernelFacetRestA q i (kernelIFPinSmoothing s i) g) *
        f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g) *
        kernelIFSurvival eps a q (kernelIFLeftPath eps x a q i (kernelIFPinSmoothing s i) (t-1) g) =
      a^2 * (kernelIFOuterSurvival eps a q g * (F g * G g)) := by
      rw [hpath g]
      dsimp [kernelIFOuterSurvival, F, G, r, s, t, b, b']
      ring
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hf0 _),
      ← ENNReal.ofReal_mul (mul_nonneg (hf0 _) (hf0 _)), hreal,
      ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_mul (kernel_IF_outer_survival_nonneg eps a q g),
      ENNReal.ofReal_mul (hF0 g)]
    ac_rfl
  rw [heq, lintegral_const_mul' _ _ (by finiteness)]
  have hsum : r+(i-r+(s-i-1)+1) = s := by omega
  have hsum' : r+(i-r+(s-i-1)+1)+(t-s-1+1) = t := by omega
  have hm : t-s-1+1 = t-s := by omega
  have hW' := (measurable_kernelIFOuterSurvival_coords eps a q).ennreal_ofReal.mul hW
  have hh := kernel_marked_pins_with_outer_reward_full ν (J := Icc 0 (2*eps)) measurableSet_Icc
    (measure_Icc_lt_top.ne) hf hf0 hfD hν ha.ne' 1 x b b'
    r (i-r) (s-i-1) (t-s-1) (by omega)
    (W := fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g)
    (by rw [hsum']; exact hW')
  rw [hsum, hm] at hh
  exact congrArg (ENNReal.ofReal (a^2) * ·) hh

/-- The original left coarea density has exactly the physical coefficient `Q`
after both density Jacobians are cancelled. -/
theorem kernel_IF_left_full_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hx : 0 < x)
    (hlong : (q.1 : ℕ)+1 < q.2.1)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelIFLeftDensity ν (fun u => ENNReal.ofReal (f u)) eps q i
      (kernelIFPinSmoothing q.2.1 i) ((q.2.2.1 : ℕ)-1) W x =
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
            (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let j := kernelIFPinSmoothing q.2.1 i
  let m := (q.2.2.1 : ℕ)-1
  have hWm : Measurable W := hW.mono (kCoordSigma_le _) le_rfl
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
        ((measurable_kernelIFPathWeight eps k hWm).comp hp))
  rw [kernelIFLeftDensity, lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [lintegral_const_mul' _ _ (by finiteness),
    kernel_IF_left_full_pin_integral ν hf hf0 hfD hfneg hν hpos hq ha hx hlong hi₁ hi₂ hW,
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetQ eps q / a^2 from
      le_of_lt (div_pos hq.2.2 (sq_pos_of_pos ha))),
    div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']

/-- The product before slope integration: one physical pin for each bridge,
and an arbitrary jointly measurable exterior reward. -/
theorem kernel_IF_right_full_pin_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (hx : 0 < x)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    (∫⁻ g, ENNReal.ofReal (f (kernelFacetQ eps q/a-x-
        kernelFacetRestRight q i (kernelIFPinSmoothing q.2.2.1 i) g)) *
      ENNReal.ofReal (f (kernelFacetP eps q/a-kernelFacetRestLeft q ((q.2.1 : ℕ)-1) g)) *
      kernelIFPathWeight eps k W (kernelIFRightPath eps x a q i
        (kernelIFPinSmoothing q.2.2.1 i) ((q.2.1 : ℕ)-1) g) ∂iidLaw ν) =
    ENNReal.ofReal (a^2) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
        (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
          (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
            (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  change s ≤ kernelIFPinSmoothing t i at hjr
  change kernelIFPinSmoothing t i < t at hjs
  change kernelIFPinSmoothing t i ≠ i at hji
  have hrewrite : ∀ g, W (kernelIFRightPath eps x a q i (kernelIFPinSmoothing t i) (s-1) g) = W g := by
    apply kernel_coord_measurable_invariant hW
    intro g j hj
    rcases hj with hj | hj
    · simp only [mem_Iio] at hj
      simp only [kernelIFRightPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ kernelIFPinSmoothing t i), Function.update_of_ne (by omega : j ≠ s-1)]
    · simp only [mem_Ici] at hj
      simp only [kernelIFRightPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ kernelIFPinSmoothing t i), Function.update_of_ne (by omega : j ≠ s-1)]
  have hproj := kernel_IF_right_projection_ae ν hpos (eps := eps) (a := a)
    (f := fun u => ENNReal.ofReal (f u))
    (by intro u hu; rw [hfneg u hu, ENNReal.ofReal_zero]) hx q i (kernelIFPinSmoothing t i) (s-1) W
  have hpath (g : ℕ → ℝ) := kernel_IF_right_full_pins (x := x) hq ha hlong hi₁ hi₂ f g
  let F (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
    (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r))
  let G (g : ℕ → ℝ) := kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x
    (i-s) (t-i-1) b' b (fun j => g (j+s))
  have hF0 (g : ℕ → ℝ) : 0 ≤ F g :=
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)
  have hG0 (g : ℕ → ℝ) : 0 ≤ G g := kernel_marked_pin_block_nonneg hf0 _ _ _ _ _ _ _ _
  have heq : (∫⁻ g, ENNReal.ofReal (f (kernelFacetQ eps q/a-x-kernelFacetRestRight q i (kernelIFPinSmoothing t i) g)) *
        ENNReal.ofReal (f (kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g)) *
        kernelIFPathWeight eps k W (kernelIFRightPath eps x a q i (kernelIFPinSmoothing t i) (s-1) g) ∂iidLaw ν) =
      ∫⁻ g, ENNReal.ofReal (a^2) * ((ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g) *
        (ENNReal.ofReal (F g) * ENNReal.ofReal (G g))) ∂iidLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [hproj] with g hg
    rw [kernel_IF_right_weight_blocks hq ha hi₁ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hg, hrewrite]
    have hreal : f (kernelFacetQ eps q/a-x-kernelFacetRestRight q i (kernelIFPinSmoothing t i) g) *
        f (kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g) *
        kernelIFSurvival eps a q (kernelIFRightPath eps x a q i (kernelIFPinSmoothing t i) (s-1) g) =
      a^2 * (kernelIFOuterSurvival eps a q g * (F g * G g)) := by
      rw [hpath g]
      dsimp [kernelIFOuterSurvival, F, G, r, s, t, b, b']
      ring
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hf0 _),
      ← ENNReal.ofReal_mul (mul_nonneg (hf0 _) (hf0 _)), hreal,
      ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_mul (kernel_IF_outer_survival_nonneg eps a q g),
      ENNReal.ofReal_mul (hF0 g)]
    ac_rfl
  rw [heq, lintegral_const_mul' _ _ (by finiteness)]
  have hsum : r+(s-r-1+1) = s := by omega
  have hsum' : r+(s-r-1+1)+(i-s+(t-i-1)+1) = t := by omega
  have hm : s-r-1+1 = s-r := by omega
  have hW' := (measurable_kernelIFOuterSurvival_coords eps a q).ennreal_ofReal.mul hW
  have hh := kernel_pins_marked_with_outer_reward_full ν (J := Icc 0 (2*eps)) measurableSet_Icc
    (measure_Icc_lt_top.ne) hf hf0 hfD hν ha.ne' 1 x b b'
    r (s-r-1) (i-s) (t-i-1) (by omega)
    (W := fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g)
    (by rw [hsum']; exact hW')
  rw [hsum, hm] at hh
  exact congrArg (ENNReal.ofReal (a^2) * ·) hh

/-- The original right coarea density has exactly the physical coefficient `Q`
after both density Jacobians are cancelled. -/
theorem kernel_IF_right_full_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hx : 0 < x)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelIFRightDensity ν (fun u => ENNReal.ofReal (f u)) eps q i
      (kernelIFPinSmoothing q.2.2.1 i) ((q.2.1 : ℕ)-1) W x =
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
        (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
          (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
            (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let j := kernelIFPinSmoothing q.2.2.1 i
  let m := (q.2.1 : ℕ)-1
  have hWm : Measurable W := hW.mono (kCoordSigma_le _) le_rfl
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
        ((measurable_kernelIFPathWeight eps k hWm).comp hp))
  rw [kernelIFRightDensity, lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [lintegral_const_mul' _ _ (by finiteness),
    kernel_IF_right_full_pin_integral ν hf hf0 hfD hfneg hν hpos hq ha hx hlong hi₁ hi₂ hW,
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetP eps q / a^2 from
      le_of_lt (div_pos hq.2.1 (sq_pos_of_pos ha))),
    div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']

def kernelIFLeftPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
        (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
          (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))))

def kernelIFRightPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
      (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
        (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))))

theorem kernel_IF_left_candidate_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hlong : (q.1 : ℕ)+1 < q.2.1) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q W) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFLeftPinDensity ν f eps q i W := by
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hst := hq.1.2
  have hh := kernel_IF_left_candidate_ae ν hf.ennreal_ofReal hν hq hi₁ hi₂ hjr hjs hji
    (m := (q.2.2.1 : ℕ)-1) (by omega) (by omega) (hW.mono (kCoordSigma_le _) le_rfl)
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
  rw [hx]
  exact kernel_IF_left_full_density_pins ν hf hf0 hfD hfneg hν hpos hq hxp hlong hi₁ hi₂ hW

theorem kernel_IF_right_candidate_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q W) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFRightPinDensity ν f eps q i W := by
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hrs := hq.1.1
  have hh := kernel_IF_right_candidate_ae ν hf.ennreal_ofReal hν hq hi₁ hi₂ hjr hjs hji
    (m := (q.2.1 : ℕ)-1) (by omega) (by omega) (hW.mono (kCoordSigma_le _) le_rfl)
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
  rw [hx]
  exact kernel_IF_right_full_density_pins ν hf hf0 hfD hfneg hν hpos hq hxp hlong hi₁ hi₂ hW

end
end PGM
