import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.OuterReward
import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.CoareaPath
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.PositivityProjection

/-!
# The actual coarea integral as killed pins and the joint outer reward

The original reconstructed density and positivity event are consumed directly.
The two physical density factors cancel the coarea Jacobian, while the reward
on the two outside paths remains a single joint function.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

/-- The two exterior survival factors, on the unmodified outside coordinates. -/
def kernelIFOuterSurvival (eps a : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (g : ℕ → ℝ) : ℝ :=
  krAlive (Icc 0 (2*eps)) (-1) (-a) q.1 (eps-fluxFacetSign q*eps)
    (kernelReversePrefix g q.1) *
  krAlive (Icc 0 (2*eps)) 1 a (k-q.2.2.1) (eps-fluxFacetSign q*eps)
    (fun j => g (j+q.2.2.1))

theorem measurable_kernelIFOuterSurvival_coords (eps a : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) :
    Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))]
      (kernelIFOuterSurvival eps a q) := by
  have h₀ := kernel_blockTest_coord_measurable (J := Icc 0 (2*eps)) measurableSet_Icc (-1) (-a)
    (q.1 : ℕ) (eps-fluxFacetSign q*eps) (φ := fun _ => (1 : ℝ)) measurable_const
    (c := fun j => (q.1 : ℕ)-1-j)
    (S := Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))
    (by intro j hj; left; change (q.1 : ℕ)-1-j < (q.1 : ℕ); omega)
  have h₃ := kernel_blockTest_coord_measurable (J := Icc 0 (2*eps)) measurableSet_Icc 1 a
    (k-q.2.2.1) (eps-fluxFacetSign q*eps) (φ := fun _ => (1 : ℝ)) measurable_const
    (c := fun j => j+q.2.2.1)
    (S := Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))
    (by intro j _; right; change (q.2.2.1 : ℕ) ≤ j+(q.2.2.1 : ℕ); omega)
  convert h₀.mul h₃ using 1
  funext g
  simp only [Pi.mul_apply, kernelBlockTest, mul_one, kernelIFOuterSurvival]
  unfold kernelReversePrefix
  rfl

theorem kernel_IF_outer_survival_nonneg (eps a : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) (g : ℕ → ℝ) : 0 ≤ kernelIFOuterSurvival eps a q g :=
  mul_nonneg (krAlive_nonneg _ _ _) (krAlive_nonneg _ _ _)

/-- The product before slope integration: one physical pin for each bridge,
and an arbitrary jointly measurable exterior reward. -/
theorem kernel_IF_left_pin_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (hx : 0 < x)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i+1 < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    (∫⁻ g, ENNReal.ofReal (f (kernelFacetP eps q/a-x-
        kernelFacetRestA q i ((q.2.1 : ℕ)-1) g)) *
      ENNReal.ofReal (f (kernelFacetQ eps q/a-kernelFacetRestB q ((q.2.2.1 : ℕ)-1) g)) *
      kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i
        ((q.2.1 : ℕ)-1) ((q.2.2.1 : ℕ)-1) g) ∂iidLaw ν) =
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
  have hrewrite : ∀ g, W (kernelIFLeftPath eps x a q i (s-1) (t-1) g) = W g := by
    apply kernel_coord_measurable_invariant hW
    intro g j hj
    rcases hj with hj | hj
    · simp only [mem_Iio] at hj
      simp only [kernelIFLeftPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ t-1), Function.update_of_ne (by omega : j ≠ s-1)]
    · simp only [mem_Ici] at hj
      simp only [kernelIFLeftPath, Function.update_of_ne (by omega : j ≠ i),
        Function.update_of_ne (by omega : j ≠ t-1), Function.update_of_ne (by omega : j ≠ s-1)]
  have hproj := kernel_IF_left_projection_ae ν hpos (eps := eps) (a := a)
    (f := fun u => ENNReal.ofReal (f u))
    (by intro u hu; rw [hfneg u hu, ENNReal.ofReal_zero]) hx q i (s-1) (t-1) W
  have hpath (g : ℕ → ℝ) := kernel_IF_left_last_pins (x := x) hq ha hi₁ hi₂ f g
  let F (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
    (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
      (Function.update (fun j => g (j+r)) (i-r) x)
  let G (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
    (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s))
  have hF0 (g : ℕ → ℝ) : 0 ≤ F g :=
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)
  have hG0 (g : ℕ → ℝ) : 0 ≤ G g :=
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)
  have heq : (∫⁻ g, ENNReal.ofReal (f (kernelFacetP eps q/a-x-kernelFacetRestA q i (s-1) g)) *
        ENNReal.ofReal (f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g)) *
        kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i (s-1) (t-1) g) ∂iidLaw ν) =
      ∫⁻ g, ENNReal.ofReal (a^2) * ((ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g) *
        (ENNReal.ofReal (F g) * ENNReal.ofReal (G g))) ∂iidLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [hproj] with g hg
    rw [kernel_IF_left_weight_blocks hq ha hi₁ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hg, hrewrite]
    have hreal : f (kernelFacetP eps q/a-x-kernelFacetRestA q i (s-1) g) *
        f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g) *
        kernelIFSurvival eps a q (kernelIFLeftPath eps x a q i (s-1) (t-1) g) =
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
  have hlen : i-r+(s-i-1) = s-r-1 := by omega
  have hm : t-s-1+1 = t-s := by omega
  have hW' := (measurable_kernelIFOuterSurvival_coords eps a q).ennreal_ofReal.mul hW
  have hh := kernel_marked_pins_with_outer_reward ν (J := Icc 0 (2*eps)) measurableSet_Icc
    (measure_Icc_lt_top.ne) hf hf0 hfD hν ha.ne' 1 x b b'
    r (i-r) (s-i-1) (t-s-1) (by omega)
    (W := fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g)
    (by rw [hsum']; exact hW')
  rw [hsum, hlen, hm] at hh
  exact congrArg (ENNReal.ofReal (a^2) * ·) hh

/-- The original left coarea density has exactly the physical coefficient `Q`
after both density Jacobians are cancelled. -/
theorem kernel_IF_left_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hx : 0 < x)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i+1 < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelIFLeftDensity ν (fun u => ENNReal.ofReal (f u)) eps q i
      ((q.2.1 : ℕ)-1) ((q.2.2.1 : ℕ)-1) W x =
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
      ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * W g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
            (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  let j := (q.2.1 : ℕ)-1
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
    kernel_IF_left_pin_integral ν hf hf0 hfD hfneg hν hpos hq ha hx hi₁ hi₂ hW,
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetQ eps q / a^2 from
      le_of_lt (div_pos hq.2.2 (sq_pos_of_pos ha))),
    div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']

end
end PGM
