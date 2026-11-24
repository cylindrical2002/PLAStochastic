import PLAStochastic.Index.GEP.Kernel.Facet.IIDLinearRoot
import PLAStochastic.Index.GEP.Kernel.Facet.SlopeCoarea

/-!
# The two-coordinate coarea parametrization on the original iid law

Coordinate replacements use the original `Function.update` convention. All
weights are evaluated on the same reconstructed path.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Two successive independent insertions preserve the original iid law. The
identity retains arbitrary measurable dependence on the reconstructed path. -/
theorem kernel_lintegral_two_update (ν : ProbabilityMeasure ℝ) (j m : ℕ)
    {F : (ℕ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g, F g ∂iidLaw ν) = ∫⁻ v, ∫⁻ u, ∫⁻ g,
      F (Function.update (Function.update g j u) m v) ∂iidLaw ν
        ∂(ν : Measure ℝ) ∂(ν : Measure ℝ) := by
  rw [lintegral_update ν m hF]
  apply lintegral_congr
  intro v
  exact lintegral_update ν j (hF.comp
    ((measurable_update_pair m).comp (measurable_const.prodMk measurable_id)))

/-- Density form of the actual two-coordinate insertion. No independent law
for a selected facet is introduced. -/
theorem kernel_lintegral_two_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (j m : ℕ) {F : (ℕ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g, F g ∂iidLaw ν) = ∫⁻ g, ∫⁻ z : ℝ × ℝ,
      f z.1 * f z.2 * F (Function.update (Function.update g j z.1) m z.2)
        ∂volume.prod volume ∂iidLaw ν := by
  have hU : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) =>
      Function.update (Function.update p.2 j p.1.2) m p.1.1) :=
    (measurable_update_pair m).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_update_pair j).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hm : Measurable (fun z : (ℝ × ℝ) × (ℕ → ℝ) =>
      F (Function.update (Function.update z.2 j z.1.2) m z.1.1)) := hF.comp hU
  have hp : Measurable (fun z : ℝ × ℝ => ∫⁻ g,
      F (Function.update (Function.update g j z.2) m z.1) ∂iidLaw ν) :=
    hm.lintegral_prod_right'
  rw [kernel_lintegral_two_update ν j m hF, lintegral_lintegral hp.aemeasurable,
    lintegral_lintegral_swap (f := fun (z : ℝ × ℝ) (g : ℕ → ℝ) =>
      F (Function.update (Function.update g j z.2) m z.1)) hm.aemeasurable]
  apply lintegral_congr
  intro g
  have hFg : Measurable (fun z : ℝ × ℝ =>
      F (Function.update (Function.update g j z.2) m z.1)) :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hff : Measurable (fun z : ℝ × ℝ => f z.1 * f z.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  rw [hν, prod_withDensity hf hf, lintegral_withDensity_eq_lintegral_mul _
    hff hFg]
  rw [← lintegral_prod_swap]
  apply lintegral_congr
  intro z
  dsimp only [Pi.mul_apply, Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm (f z.2) (f z.1)]

/-- The two-coordinate coarea formula against arbitrary nonnegative tests. -/
theorem kernel_linear_facet_lintegral {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (c d : ℝ) {W : ℝ × ℝ → ℝ≥0∞} (hW : Measurable W)
    (hpos : ∀ u v, v + d ≤ 0 → W (u, v) = 0)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ z : ℝ × ℝ, W z * φ (p / q * (z.2 + d) - z.1 - c) ∂volume.prod volume) =
      ∫⁻ x, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
        W (p / a - x - c, q / a - d)) * φ x := by
  have hE : Measurable (fun z : ℝ × ℝ => p / q * (z.2 + d) - z.1 - c) := by fun_prop
  have hI : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (q / z.2 ^ 2) *
      W (p / z.2 - z.1 - c, q / z.2 - d)) := by fun_prop
  have hD : Measurable (fun x => ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
      W (p / a - x - c, q / a - d)) := hI.lintegral_prod_right'
  have h := congrArg (fun μ : Measure ℝ => ∫⁻ x, φ x ∂μ)
    (kernel_linear_facet_map_slope_density hp hq c d hW hpos)
  have hφE : Measurable (fun z : ℝ × ℝ => φ (p / q * (z.2 + d) - z.1 - c)) := hφ.comp hE
  rw [lintegral_map hφ hE, lintegral_withDensity_eq_lintegral_mul _ hW hφE,
    lintegral_withDensity_eq_lintegral_mul _ hD hφ] at h
  exact h

/-- Reinsert both smoothing coordinates into the same actual path. -/
def kernelCoareaIIDWeight (f : ℝ → ℝ≥0∞) (j m : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞)
    (g : ℕ → ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  f z.1 * f z.2 * W (Function.update (Function.update g j z.1) m z.2)

theorem measurable_kernelCoareaIIDWeight {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (j m : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (fun z : (ℕ → ℝ) × (ℝ × ℝ) => kernelCoareaIIDWeight f j m W z.1 z.2) := by
  have hU : Measurable (fun z : (ℕ → ℝ) × (ℝ × ℝ) =>
      Function.update (Function.update z.1 j z.2.1) m z.2.2) :=
    (measurable_update_pair m).comp ((measurable_snd.comp measurable_snd).prodMk
      ((measurable_update_pair j).comp
        ((measurable_fst.comp measurable_snd).prodMk measurable_fst)))
  exact ((hf.comp (measurable_fst.comp measurable_snd)).mul
    (hf.comp (measurable_snd.comp measurable_snd))).mul (hW.comp hU)

/-- The explicit slope density after retaining all the other original iid
coordinates. No independent replacement of an active path weight occurs. -/
def kernelCoareaIIDDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (j m : ℕ) (p q : ℝ) (c d : (ℕ → ℝ) → ℝ) (W : (ℕ → ℝ) → ℝ≥0∞)
    (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
    kernelCoareaIIDWeight f j m W g (p / a - x - c g, q / a - d g)) ∂iidLaw ν

/-- Actual iid linear-facet coarea. The affine identity and physical support
are checked on the reconstructed path; the resulting density retains its
full weight. This formula is used before independent block factorization. -/
theorem kernel_iid_facet_map_slope_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (j m : ℕ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {c d E : (ℕ → ℝ) → ℝ} (hc : Measurable c) (hd : Measurable d) (hE : Measurable E)
    (hroot : ∀ g u v, E (Function.update (Function.update g j u) m v) =
      p / q * (v + d g) - u - c g)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W)
    (hpos : ∀ g u v, v + d g ≤ 0 → kernelCoareaIIDWeight f j m W g (u, v) = 0) :
    ((iidLaw ν).withDensity W).map E =
      volume.withDensity (kernelCoareaIIDDensity ν f j m p q c d W) := by
  have hV := measurable_kernelCoareaIIDWeight hf j m hW
  have hA : Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ =>
      (z.1.2, (p / z.2 - z.1.1 - c z.1.2, q / z.2 - d z.1.2))) := by fun_prop
  have hH : Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ => ENNReal.ofReal (q / z.2 ^ 2) *
      kernelCoareaIIDWeight f j m W z.1.2
        (p / z.2 - z.1.1 - c z.1.2, q / z.2 - d z.1.2)) :=
    (by fun_prop : Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ =>
      ENNReal.ofReal (q / z.2 ^ 2))).mul (hV.comp hA)
  have hD : Measurable (fun z : ℝ × (ℕ → ℝ) => ∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal (q / a ^ 2) * kernelCoareaIIDWeight f j m W z.2
        (p / a - z.1 - c z.2, q / a - d z.2)) := hH.lintegral_prod_right'
  have hDen : Measurable (kernelCoareaIIDDensity ν f j m p q c d W) :=
    hD.lintegral_prod_right'
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hφE : Measurable (fun g => φ (E g)) := hφ.comp hE
  rw [lintegral_map hφ hE, lintegral_withDensity_eq_lintegral_mul _ hW hφE,
    lintegral_withDensity_eq_lintegral_mul _ hDen hφ]
  simp only [Pi.mul_apply]
  have hF : Measurable (fun g => W g * φ (E g)) := hW.mul hφE
  rw [kernel_lintegral_two_density ν hf hν j m hF]
  simp only [hroot, ← mul_assoc]
  change (∫⁻ g, ∫⁻ z : ℝ × ℝ, kernelCoareaIIDWeight f j m W g z *
      φ (p / q * (z.2 + d g) - z.1 - c g) ∂volume.prod volume ∂iidLaw ν) = _
  have hg (g : ℕ → ℝ) := kernel_linear_facet_lintegral hp hq (c g) (d g)
    (W := kernelCoareaIIDWeight f j m W g)
    (hV.comp (measurable_const.prodMk measurable_id)) (hpos g) hφ
  simp_rw [hg]
  have hswap : Measurable (fun z : (ℕ → ℝ) × ℝ =>
      (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
        kernelCoareaIIDWeight f j m W z.1 (p / a - z.2 - c z.1, q / a - d z.1)) * φ z.2) :=
    (hD.comp measurable_swap).mul (hφ.comp measurable_snd)
  rw [lintegral_lintegral_swap (f := fun (g : ℕ → ℝ) (x : ℝ) =>
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
      kernelCoareaIIDWeight f j m W g (p / a - x - c g, q / a - d g)) * φ x) hswap.aemeasurable]
  apply lintegral_congr
  intro x
  have hDx : Measurable (fun g : ℕ → ℝ => ∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal (q / a ^ 2) * kernelCoareaIIDWeight f j m W g
        (p / a - x - c g, q / a - d g)) :=
    hD.comp (measurable_const.prodMk measurable_id)
  exact lintegral_mul_const (φ x) hDx

end
end PGM
