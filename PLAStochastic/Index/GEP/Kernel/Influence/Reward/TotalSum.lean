import PLAStochastic.Index.GEP.Kernel.Influence.Reward.ReconstructedPins
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.AllFacets

/-! # Actual total-sum rewards in every physical pin representation -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFLeftTotalPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
        (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
          (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))))

def kernelIFRightTotalPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν) *
      (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
        (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))))

theorem kernel_IF_left_total_candidate_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hlong : (q.1 : ℕ)+1 < q.2.1) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q (fun g => H (gapKeys g k))) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFLeftTotalPinDensity ν f eps q i H := by
  have hW : Measurable (fun g : ℕ → ℝ => H (gapKeys g k)) := hH.comp (by unfold gapKeys; fun_prop)
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hst := hq.1.2
  have hh := kernel_IF_left_candidate_ae ν hf.ennreal_ofReal hν hq hi₁ hi₂ hjr hjs hji
    (m := (q.2.2.1 : ℕ)-1) (by omega) (by omega) hW
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
  rw [hx]
  exact kernel_IF_left_reconstructed_density_pins ν hf hf0 hfD hfneg hν hpos hq hxp hlong hi₁ hi₂ hW
    (R := fun a g => H (kernelIFPhysicalSum a q g))
    (fun a _ => hH.comp (kernel_IF_physical_sum_coord_measurable a q))
    (fun a _ g => congrArg H (kernel_IF_left_total_sum hq.1 hi₁ hi₂ hjr hjs hji
      (by omega) (by omega) g))

theorem kernel_IF_right_total_candidate_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q (fun g => H (gapKeys g k))) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFRightTotalPinDensity ν f eps q i H := by
  have hW : Measurable (fun g : ℕ → ℝ => H (gapKeys g k)) := hH.comp (by unfold gapKeys; fun_prop)
  obtain ⟨hjr,hjs,hji⟩ := kernel_IF_pin_smoothing_mem hlong hi₁ hi₂
  have hrs := hq.1.1
  have hh := kernel_IF_right_candidate_ae ν hf.ennreal_ofReal hν hq hi₁ hi₂ hjr hjs hji
    (m := (q.2.1 : ℕ)-1) (by omega) (by omega) hW
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
  rw [hx]
  exact kernel_IF_right_reconstructed_density_pins ν hf hf0 hfD hfneg hν hpos hq hxp hlong hi₁ hi₂ hW
    (R := fun a g => H (kernelIFPhysicalSum a q g))
    (fun a _ => hH.comp (kernel_IF_physical_sum_coord_measurable a q))
    (fun a _ g => congrArg H (kernel_IF_right_total_sum hq.1 hi₁ hi₂ hjr hjs hji
      (by omega) (by omega) g))


theorem kernel_IF_left_short_total_sum {eps x : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (hx : 0 < x) (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFLeftShortPath eps x q m g) k =
      kernelIFPhysicalSum (kernelFacetP eps q/x) q g := by
  have hrs := hq.1.1
  have hst := hq.1.2
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  have hik : (q.1 : ℕ) < k := by omega
  have hmk : m < k := by omega
  have hmi : (q.1 : ℕ) ≠ m := by omega
  have hgap : gapKeys g q.2.1 - gapKeys g q.1 = g q.1 := by
    rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ]
    ring
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : kernelFacetP eps q + kernelFacetQ eps q =
      (q.2.2.1 : ℝ)-(q.1 : ℝ) := by
    unfold kernelFacetP kernelFacetQ
    ring
  have he : gapKeys (kernelIFLeftShortPath eps x q m g) k =
      gapKeys g q.1 + (x+kernelFacetQ eps q/kernelFacetP eps q*x) +
        (gapKeys g k-gapKeys g q.2.2.1) := by
    simp only [kernelIFLeftShortPath, kernel_gapKeys_update_affine, hik, hmk, if_true,
      Function.update_of_ne hmi]
    unfold kernelFacetRestB
    linarith [hgap]
  rw [he, kernelIFPhysicalSum, ← hsum]
  field_simp


theorem kernel_IF_right_short_total_sum {eps x : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (hx : 0 < x) (_hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFRightShortPath eps x q m g) k =
      kernelIFPhysicalSum (kernelFacetQ eps q/x) q g := by
  have hrs := hq.1.1
  have hst := hq.1.2
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  have hik : (q.2.1 : ℕ) < k := by omega
  have hmk : m < k := by omega
  have hmi : (q.2.1 : ℕ) ≠ m := by omega
  have hgap : gapKeys g q.2.2.1 - gapKeys g q.2.1 = g q.2.1 := by
    rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ]
    ring
  have hP : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : kernelFacetP eps q + kernelFacetQ eps q =
      (q.2.2.1 : ℝ)-(q.1 : ℝ) := by
    unfold kernelFacetP kernelFacetQ
    ring
  have he : gapKeys (kernelIFRightShortPath eps x q m g) k =
      gapKeys g q.1 + (x+kernelFacetP eps q/kernelFacetQ eps q*x) +
        (gapKeys g k-gapKeys g q.2.2.1) := by
    simp only [kernelIFRightShortPath, kernel_gapKeys_update_affine, hik, hmk, if_true,
      Function.update_of_ne hmi]
    unfold kernelFacetRestLeft
    linarith [hgap]
  rw [he, kernelIFPhysicalSum, ← hsum]
  field_simp
  ring


def kernelIFLeftTotalDiracPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetQ eps q/x) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetP eps q/x) q g) * H (kernelIFPhysicalSum (kernelFacetP eps q/x) q g) ∂iidLaw ν) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetP eps q/x)
        (q.2.2.1-q.2.1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))

def kernelIFRightTotalDiracPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetP eps q/x) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetQ eps q/x) q g) * H (kernelIFPhysicalSum (kernelFacetQ eps q/x) q g) ∂iidLaw ν) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetQ eps q/x)
        (q.2.1-q.1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)))

theorem kernel_IF_left_total_short_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelIFLeftShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q ((q.2.2.1 : ℕ)-1)
      (fun g => H (gapKeys g k)) x = kernelIFLeftTotalDiracPinDensity ν f eps q H x := by
  let a := kernelFacetP eps q/x
  let R (g : ℕ → ℝ) := H (kernelIFPhysicalSum a q g)
  let m := (q.2.2.1 : ℕ)-1
  have hrs := hq.1.1
  have hst := hq.1.2
  have hm₁ : (q.2.1 : ℕ) ≤ m := by dsimp [m]; omega
  have hm₂ : m < q.2.2.1 := by dsimp [m]; omega
  have hR : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] R :=
    hH.comp (kernel_IF_physical_sum_coord_measurable a q)
  have he : kernelIFLeftShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q m
      (fun g => H (gapKeys g k)) x =
      kernelIFLeftShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q m R x := by
    unfold kernelIFLeftShortDensity
    congr 1
    apply lintegral_congr
    intro g
    congr 1
    apply kernel_IF_pathWeight_reconstructed hR
    · intro g n hn
      rcases hn with hn | hn <;> simp only [mem_Iio, mem_Ici] at hn
      · simp only [kernelIFLeftShortPath, Function.update_of_ne (by omega : n ≠ q.1),
          Function.update_of_ne (by omega : n ≠ m)]
      · simp only [kernelIFLeftShortPath, Function.update_of_ne (by omega : n ≠ q.1),
          Function.update_of_ne (by omega : n ≠ m)]
    · intro g
      exact congrArg H (kernel_IF_left_short_total_sum hq hshort hx hm₁ hm₂ g)
  rw [he]
  exact kernel_IF_left_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hx hR


theorem kernel_IF_right_total_short_density_pins (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelIFRightShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q ((q.2.1 : ℕ)-1)
      (fun g => H (gapKeys g k)) x = kernelIFRightTotalDiracPinDensity ν f eps q H x := by
  let a := kernelFacetQ eps q/x
  let R (g : ℕ → ℝ) := H (kernelIFPhysicalSum a q g)
  let m := (q.2.1 : ℕ)-1
  have hrs := hq.1.1
  have hst := hq.1.2
  have hm₁ : (q.1 : ℕ) ≤ m := by dsimp [m]; omega
  have hm₂ : m < q.2.1 := by dsimp [m]; omega
  have hR : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] R :=
    hH.comp (kernel_IF_physical_sum_coord_measurable a q)
  have he : kernelIFRightShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q m
      (fun g => H (gapKeys g k)) x =
      kernelIFRightShortDensity ν (fun u => ENNReal.ofReal (f u)) eps q m R x := by
    unfold kernelIFRightShortDensity
    congr 1
    apply lintegral_congr
    intro g
    congr 1
    apply kernel_IF_pathWeight_reconstructed hR
    · intro g n hn
      rcases hn with hn | hn <;> simp only [mem_Iio, mem_Ici] at hn
      · simp only [kernelIFRightShortPath, Function.update_of_ne (by omega : n ≠ q.2.1),
          Function.update_of_ne (by omega : n ≠ m)]
      · simp only [kernelIFRightShortPath, Function.update_of_ne (by omega : n ≠ q.2.1),
          Function.update_of_ne (by omega : n ≠ m)]
    · intro g
      exact congrArg H (kernel_IF_right_short_total_sum hq hshort hx hm₁ hm₂ g)
  rw [he]
  exact kernel_IF_right_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hx hR

end
end PGM
