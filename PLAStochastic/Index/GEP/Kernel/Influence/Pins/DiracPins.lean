import PLAStochastic.Index.GEP.Kernel.Influence.Pins.DiracPath

/-! # The actual short facet density as an exterior row reward and one pin -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_projection_update_two {f : ℝ → ℝ≥0∞}
    (hfneg : ∀ u, u ≤ 0 → f u = 0) {eps a x v : ℝ} (hx : 0 < x)
    {k i m : ℕ} (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞)
    {g : ℕ → ℝ} (hg : ∀ j < k, 0 < g j) :
    let h := Function.update (Function.update g m v) i x
    f v * kernelIFBlockWeight eps a q W h =
      f v * (ENNReal.ofReal (kernelIFSurvival eps a q h) * W h) := by
  dsimp only
  by_cases hv : 0 < v
  · have hp : ∀ j < k, 0 < Function.update (Function.update g m v) i x j := by
      intro j hj
      by_cases hji : j = i
      · subst j; simpa only [Function.update_self] using hx
      · rw [Function.update_of_ne hji]
        by_cases hjm : j = m
        · subst j; simpa only [Function.update_self] using hv
        · simpa only [Function.update_of_ne hjm] using hg j hj
    rw [kernelIFBlockWeight, indicator_of_mem (show
      Function.update (Function.update g m v) i x ∈ {g : ℕ → ℝ | ∀ j < k, 0 < g j} from hp)]
  · rw [hfneg v (le_of_not_gt hv), zero_mul, zero_mul]

theorem kernel_outer_one_pin_lintegral (ν : ProbabilityMeasure ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (β a y z : ℝ) {r s t : ℕ} (hrs : r ≤ s) (hst : s < t)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable[kCoordSigma (Iio r ∪ Ici t)] W) :
    (∫⁻ g, W g * ENNReal.ofReal (kernelBlockTest J β a (t-s-1) y
      (fun u => krKer J f β a u z) (fun j => g (j+s))) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) * ENNReal.ofReal (krDens J ν f β a (t-s) y z) := by
  have hK : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have hG := (kernel_blockTest_coord_measurable hJ β a (t-s-1) y hK
    (c := fun j => j+s) (S := Ico s t) (by intro j hj; constructor <;> omega)).ennreal_ofReal
  have hdis : Disjoint (Iio r ∪ Ici t) (Ico s t) := Set.disjoint_left.mpr (by
    intro j hj hj'
    rcases hj with hj | hj <;> simp only [mem_Iio,mem_Ici,mem_Ico] at * <;> omega)
  rw [kernel_iid_lintegral_mul_coords ν hdis hW hG,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelBlockTest hJ β a (t-s-1) y hK).ennreal_ofReal,
    kernel_lintegral_pin_block ν hJ hf hf0 hfD]
  rw [show t-s-1+1 = t-s by omega]

theorem kernel_outer_first_pin_lintegral (ν : ProbabilityMeasure ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (β a y z : ℝ) {r s t : ℕ} (hrs : r < s) (hst : s ≤ t)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable[kCoordSigma (Iio r ∪ Ici t)] W) :
    (∫⁻ g, W g * ENNReal.ofReal (kernelBlockTest J β a (s-r-1) y
      (fun u => krKer J f β a u z) (fun j => g (j+r))) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) * ENNReal.ofReal (krDens J ν f β a (s-r) y z) := by
  have hK : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have hG := (kernel_blockTest_coord_measurable hJ β a (s-r-1) y hK
    (c := fun j => j+r) (S := Ico r s) (by intro j hj; constructor <;> omega)).ennreal_ofReal
  have hdis : Disjoint (Iio r ∪ Ici t) (Ico r s) := Set.disjoint_left.mpr (by
    intro j hj hj'
    rcases hj with hj | hj <;> simp only [mem_Iio,mem_Ici,mem_Ico] at * <;> omega)
  rw [kernel_iid_lintegral_mul_coords ν hdis hW hG,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelBlockTest hJ β a (s-r-1) y hK).ennreal_ofReal,
    kernel_lintegral_pin_block ν hJ hf hf0 hfD]
  rw [show s-r-1+1 = s-r by omega]

theorem kernel_IF_left_short_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelIFLeftShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q ((q.2.2.1 : ℕ)-1) W x =
      ENNReal.ofReal (kernelFacetQ eps q/x) *
        ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetP eps q/x) q g) * W g ∂iidLaw ν) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetP eps q/x)
            (q.2.2.1-q.2.1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))) := by
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let a := kernelFacetP eps q/x
  let v (g : ℕ → ℝ) := kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q (t-1) g
  let H (g : ℕ → ℝ) := kernelIFLeftShortPath eps x q (t-1) g
  let F (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1)
    (eps+fluxFacetSign q*eps) (fun z => krKer (Icc 0 (2*eps)) f 1 a z (eps-fluxFacetSign q*eps))
      (fun j => g (j+s))
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have ha : 0 < a := div_pos hq.2.1 hx
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hPa : kernelFacetP eps q/a = x := by dsimp [a]; field_simp
  have hQa : kernelFacetQ eps q/a = kernelFacetQ eps q/kernelFacetP eps q*x := by
    dsimp [a]; field_simp
  have hrewrite : ∀ g, W (H g) = W g := by
    apply kernel_coord_measurable_invariant hW H
    intro g j hj
    rcases hj with hj | hj <;> simp only [mem_Iio,mem_Ici] at hj
    · simp only [H, kernelIFLeftShortPath, Function.update_of_ne (by omega : j ≠ q.1),
        Function.update_of_ne (by omega : j ≠ t-1)]
    · simp only [H, kernelIFLeftShortPath, Function.update_of_ne (by omega : j ≠ q.1),
        Function.update_of_ne (by omega : j ≠ t-1)]
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving.ae hpos
  have heq : (∫⁻ g, ENNReal.ofReal (f (v g)) * kernelIFPathWeight eps k W (H g) ∂iidLaw ν) =
      ENNReal.ofReal a * ∫⁻ g, (ENNReal.ofReal (kernelIFOuterSurvival eps a q g)*W g) *
        ENNReal.ofReal (F g) ∂iidLaw ν := by
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_congr_ae
    filter_upwards [hall] with g hg
    have hsums := kernel_IF_left_short_sums (x := x) hq hshort (m := t-1) (by omega) (by omega) g
    rw [kernel_IF_pathWeight_eq_blocks hq ha W (H g) (hsums.1.trans hPa.symm) (hsums.2.trans hQa.symm)]
    have hp := kernel_IF_projection_update_two (f := fun u => ENNReal.ofReal (f u))
      (by intro u hu; rw [hfneg u hu, ENNReal.ofReal_zero])
      (eps := eps) (a := a) (v := v g) (i := q.1) (m := t-1) hx q W (fun j _ => hg j)
    change ENNReal.ofReal (f (v g)) * kernelIFBlockWeight eps a q W (H g) =
      ENNReal.ofReal (f (v g)) * (ENNReal.ofReal (kernelIFSurvival eps a q (H g)) * W (H g)) at hp
    rw [hp, hrewrite, ← mul_assoc, ← ENNReal.ofReal_mul (hf0 _)]
    have hpath := kernel_IF_left_short_pins hq hshort heps hx f g
    change f (v g) * kernelIFSurvival eps a q (H g) = a * (kernelIFOuterSurvival eps a q g * F g) at hpath
    rw [hpath, ENNReal.ofReal_mul ha.le,
      ENNReal.ofReal_mul (kernel_IF_outer_survival_nonneg eps a q g)]
    ac_rfl
  unfold kernelIFLeftShortDensity
  rw [heq]
  dsimp only [F]
  rw [kernel_outer_one_pin_lintegral ν (J := Icc 0 (2*eps)) measurableSet_Icc hf hf0 hfD 1 a
    (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps) hrs.le hst
    (W := fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g)*W g)
    ((measurable_kernelIFOuterSurvival_coords eps a q).ennreal_ofReal.mul hW),
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetQ eps q/kernelFacetP eps q from
      le_of_lt (div_pos hq.2.2 hq.2.1))]
  congr 2
  dsimp [a]
  field_simp

theorem kernel_IF_right_short_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelIFRightShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q ((q.2.1 : ℕ)-1) W x =
      ENNReal.ofReal (kernelFacetP eps q/x) *
        ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetQ eps q/x) q g) * W g ∂iidLaw ν) *
          ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetQ eps q/x)
            (q.2.1-q.1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps))) := by
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let a := kernelFacetQ eps q/x
  let v (g : ℕ → ℝ) := kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q (s-1) g
  let H (g : ℕ → ℝ) := kernelIFRightShortPath eps x q (s-1) g
  let F (g : ℕ → ℝ) := kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1)
    (eps-fluxFacetSign q*eps) (fun z => krKer (Icc 0 (2*eps)) f 1 a z (eps+fluxFacetSign q*eps))
      (fun j => g (j+r))
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have ha : 0 < a := div_pos hq.2.2 hx
  have hP : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hPa : kernelFacetQ eps q/a = x := by dsimp [a]; field_simp
  have hQa : kernelFacetP eps q/a = kernelFacetP eps q/kernelFacetQ eps q*x := by
    dsimp [a]; field_simp
  have hrewrite : ∀ g, W (H g) = W g := by
    apply kernel_coord_measurable_invariant hW H
    intro g j hj
    rcases hj with hj | hj <;> simp only [mem_Iio,mem_Ici] at hj
    · simp only [H, kernelIFRightShortPath, Function.update_of_ne (by omega : j ≠ q.2.1),
        Function.update_of_ne (by omega : j ≠ s-1)]
    · simp only [H, kernelIFRightShortPath, Function.update_of_ne (by omega : j ≠ q.2.1),
        Function.update_of_ne (by omega : j ≠ s-1)]
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving.ae hpos
  have heq : (∫⁻ g, ENNReal.ofReal (f (v g)) * kernelIFPathWeight eps k W (H g) ∂iidLaw ν) =
      ENNReal.ofReal a * ∫⁻ g, (ENNReal.ofReal (kernelIFOuterSurvival eps a q g)*W g) *
        ENNReal.ofReal (F g) ∂iidLaw ν := by
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_congr_ae
    filter_upwards [hall] with g hg
    have hsums := kernel_IF_right_short_sums (x := x) hq hshort (m := s-1) (by omega) (by omega) g
    rw [kernel_IF_pathWeight_eq_blocks hq ha W (H g) (hsums.1.trans hQa.symm) (hsums.2.trans hPa.symm)]
    have hp := kernel_IF_projection_update_two (f := fun u => ENNReal.ofReal (f u))
      (by intro u hu; rw [hfneg u hu, ENNReal.ofReal_zero])
      (eps := eps) (a := a) (v := v g) (i := q.2.1) (m := s-1) hx q W (fun j _ => hg j)
    change ENNReal.ofReal (f (v g)) * kernelIFBlockWeight eps a q W (H g) =
      ENNReal.ofReal (f (v g)) * (ENNReal.ofReal (kernelIFSurvival eps a q (H g)) * W (H g)) at hp
    rw [hp, hrewrite, ← mul_assoc, ← ENNReal.ofReal_mul (hf0 _)]
    have hpath := kernel_IF_right_short_pins hq hshort heps hx f g
    change f (v g) * kernelIFSurvival eps a q (H g) = a * (kernelIFOuterSurvival eps a q g * F g) at hpath
    rw [hpath, ENNReal.ofReal_mul ha.le,
      ENNReal.ofReal_mul (kernel_IF_outer_survival_nonneg eps a q g)]
    ac_rfl
  unfold kernelIFRightShortDensity
  rw [heq]
  dsimp only [F]
  rw [kernel_outer_first_pin_lintegral ν (J := Icc 0 (2*eps)) measurableSet_Icc hf hf0 hfD 1 a
    (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps) hrs hst.le
    (W := fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g)*W g)
    ((measurable_kernelIFOuterSurvival_coords eps a q).ennreal_ofReal.mul hW),
    ← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ kernelFacetP eps q/kernelFacetQ eps q from
      le_of_lt (div_pos hq.2.1 hq.2.2))]
  congr 2
  dsimp [a]
  field_simp

end
end PGM
