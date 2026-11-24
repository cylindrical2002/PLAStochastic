import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.LastGap
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.KilledBlocks

/-!
# Physical coarea paths and their last-step pin factors

The identities here apply to the reconstructed path already used by the actual
facet coarea theorem. The smoothing coordinates are the final random gaps of
their respective bridges. No independent path or pin-event probability replaces
the original active path.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

theorem kernel_krAlive_congr (J : Set ℝ) (β a : ℝ) (n : ℕ) (b : ℝ)
    {g h : ℕ → ℝ} (he : ∀ j < n, g j = h j) :
    krAlive J β a n b g = krAlive J β a n b h := by
  simpa only [kernelBlockTest, mul_one] using
    kernel_blockTest_congr J β a n b (fun _ => 1) he

theorem kernel_pin_density_factor_of_endpoint (J : Set ℝ) (f : ℝ → ℝ)
    {a : ℝ} (ha : a ≠ 0) (β y z : ℝ) (n : ℕ) (g : ℕ → ℝ)
    (hz : kWalk y β a g (n+1) = z) :
    f (g n) * krAlive J β a (n+1) y g =
      |a| * kernelBlockTest J β a n y (fun u => krKer J f β a u z) g := by
  have harg : (kWalk y β a g n + β - z) / a = g n := by
    apply (div_eq_iff ha).mpr
    rw [kernel_kWalk_succ_last] at hz
    linarith
  rw [krAlive_succ_last, hz]
  unfold kernelBlockTest krKer
  dsimp only
  rw [harg]
  rw [show krAlive J β a n y g *
      (J.indicator (fun _ => (1 : ℝ)) (kWalk y β a g n) *
        J.indicator (fun _ => (1 : ℝ)) z * (f (g n) / |a|)) =
      (krAlive J β a n y g * J.indicator (fun _ => (1 : ℝ)) (kWalk y β a g n)) *
        J.indicator (fun _ => (1 : ℝ)) z * (f (g n) / |a|) by ring,
    krAlive_mul_indicator]
  field_simp [abs_ne_zero.mpr ha]

theorem kernel_IF_bridge_endpoints {eps a : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (g : ℕ → ℝ)
    (hA : gapKeys g q.2.1 - gapKeys g q.1 = kernelFacetP eps q / a)
    (hB : gapKeys g q.2.2.1 - gapKeys g q.2.1 = kernelFacetQ eps q / a) :
    kWalk (eps-fluxFacetSign q*eps) 1 a (fun j => g (j+q.1)) (q.2.1-q.1) =
        eps+fluxFacetSign q*eps ∧
      kWalk (eps+fluxFacetSign q*eps) 1 a (fun j => g (j+q.2.1)) (q.2.2.1-q.2.1) =
        eps-fluxFacetSign q*eps := by
  have hAp : gapKeys g q.1 < gapKeys g q.2.1 := by
    have hp : 0 < kernelFacetP eps q / a := div_pos hq.2.1 ha
    linarith
  have hBp : gapKeys g q.2.1 < gapKeys g q.2.2.1 := by
    have hp : 0 < kernelFacetQ eps q / a := div_pos hq.2.2 ha
    linarith
  have hh := kernel_facet_bridge_contacts g hq.1.1 hq.1.2 hAp hBp
    (kernel_IF_width_of_sums hq ha g hA hB)
  dsimp only at hh
  rwa [kernel_IF_slope_of_sums hq ha.ne' g hA hB] at hh

/-- Exact two-density conversion for a mark before the last gap of the first
bridge. The factor `a²` is the one cancelled by the coarea Jacobian. -/
theorem kernel_IF_left_last_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i+1 < q.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let u := kernelFacetP eps q/a-x-kernelFacetRestA q i (s-1) g
    let v := kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g
    f u * f v * kernelIFSurvival eps a q
        (kernelIFLeftPath eps x a q i (s-1) (t-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
            (Function.update (fun j => g (j+r)) (i-r) x) *
          (kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFLeftPath eps x a q i (s-1) (t-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have hl : s-r-1+1 = s-r := by omega
  have hm : t-s-1+1 = t-s := by omega
  have hsums := kernel_IF_left_sums hq.1 hi₁ (by omega) (j := s-1) (m := t-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (eps := eps) (x := x) (a := a) g
  have hends := kernel_IF_bridge_endpoints hq ha h hsums.1 hsums.2
  have hF := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b b' (s-r-1) (fun j => h (j+r)) (by simpa only [hl] using hends.1)
  have hG := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b' b (t-s-1) (fun j => h (j+s)) (by simpa only [hm] using hends.2)
  have hvF : h (s-r-1+r) = kernelFacetP eps q/a-x-kernelFacetRestA q i (s-1) g := by
    have he : s-r-1+r = s-1 := by omega
    simp only [he, h, kernelIFLeftPath, Function.update_of_ne (by omega : s-1 ≠ i),
      Function.update_of_ne (by omega : s-1 ≠ t-1), Function.update_self]
  have hvG : h (t-s-1+s) = kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g := by
    have he : t-s-1+s = t-1 := by omega
    simp only [he, h, kernelIFLeftPath, Function.update_of_ne (by omega : t-1 ≠ i),
      Function.update_self]
  rw [hvF, hl, abs_of_pos ha] at hF
  rw [hvG, hm, abs_of_pos ha] at hG
  have hpF : kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => h (j+r)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
        (Function.update (fun j => g (j+r)) (i-r) x) := by
    apply kernel_blockTest_congr
    intro j hj
    by_cases hji : j = i-r
    · have he : j+r = i := by omega
      rw [he, hji]
      simp only [h, kernelIFLeftPath, Function.update_self]
    · simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+r ≠ i),
        Function.update_of_ne (by omega : j+r ≠ t-1),
        Function.update_of_ne (by omega : j+r ≠ s-1), Function.update_of_ne hji]
  have hpG : kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => h (j+s)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+s ≠ i),
      Function.update_of_ne (by omega : j+s ≠ t-1), Function.update_of_ne (by omega : j+s ≠ s-1)]
  have hp₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFLeftPath,
      Function.update_of_ne (by omega : r-1-j ≠ i),
      Function.update_of_ne (by omega : r-1-j ≠ t-1),
      Function.update_of_ne (by omega : r-1-j ≠ s-1)]
  have hp₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+t ≠ i),
      Function.update_of_ne (by omega : j+t ≠ t-1), Function.update_of_ne (by omega : j+t ≠ s-1)]
  rw [hpF] at hF
  rw [hpG] at hG
  change _ * _ * (krAlive _ _ _ r b (kernelReversePrefix h r) *
    (krAlive _ _ _ (s-r) b (fun j => h (j+r)) *
      (krAlive _ _ _ (t-s) b' (fun j => h (j+s)) *
        krAlive _ _ _ (k-t) b (fun j => h (j+t))))) = _
  rw [hp₀, hp₃]
  linear_combination
    krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) *
      (f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g) *
        krAlive (Icc 0 (2*eps)) 1 a (t-s) b' (fun j => h (j+s))) * hF +
    a * krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) *
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
        (Function.update (fun j => g (j+r)) (i-r) x) * hG

/-- Exact two-density conversion for a mark before the last gap of the second
bridge. The factor `a²` is the one cancelled by the coarea Jacobian. -/
theorem kernel_IF_right_last_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i+1 < q.2.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let u := kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-1) g
    let v := kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g
    f u * f v * kernelIFSurvival eps a q
        (kernelIFRightPath eps x a q i (t-1) (s-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
            (fun j => g (j+r)) *
          (kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b)
            (Function.update (fun j => g (j+s)) (i-s) x) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFRightPath eps x a q i (t-1) (s-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have hl : s-r-1+1 = s-r := by omega
  have hm : t-s-1+1 = t-s := by omega
  have hsums := kernel_IF_right_sums hq.1 hi₁ (by omega) (j := t-1) (m := s-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (eps := eps) (x := x) (a := a) g
  have hends := kernel_IF_bridge_endpoints hq ha h hsums.1 hsums.2
  have hF := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b b' (s-r-1) (fun j => h (j+r)) (by simpa only [hl] using hends.1)
  have hG := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b' b (t-s-1) (fun j => h (j+s)) (by simpa only [hm] using hends.2)
  have hvF : h (s-r-1+r) = kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g := by
    have he : s-r-1+r = s-1 := by omega
    simp only [he, h, kernelIFRightPath, Function.update_of_ne (by omega : s-1 ≠ i),
      Function.update_self]
  have hvG : h (t-s-1+s) = kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-1) g := by
    have he : t-s-1+s = t-1 := by omega
    simp only [he, h, kernelIFRightPath, Function.update_of_ne (by omega : t-1 ≠ i),
      Function.update_of_ne (by omega : t-1 ≠ s-1), Function.update_self]
  rw [hvF, hl, abs_of_pos ha] at hF
  rw [hvG, hm, abs_of_pos ha] at hG
  have hpF : kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => h (j+r)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+r ≠ i),
      Function.update_of_ne (by omega : j+r ≠ s-1), Function.update_of_ne (by omega : j+r ≠ t-1)]
  have hpG : kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => h (j+s)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b)
        (Function.update (fun j => g (j+s)) (i-s) x) := by
    apply kernel_blockTest_congr
    intro j hj
    by_cases hji : j = i-s
    · have he : j+s = i := by omega
      rw [he, hji]
      simp only [h, kernelIFRightPath, Function.update_self]
    · simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+s ≠ i),
        Function.update_of_ne (by omega : j+s ≠ s-1),
        Function.update_of_ne (by omega : j+s ≠ t-1), Function.update_of_ne hji]
  have hp₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFRightPath,
      Function.update_of_ne (by omega : r-1-j ≠ i),
      Function.update_of_ne (by omega : r-1-j ≠ t-1),
      Function.update_of_ne (by omega : r-1-j ≠ s-1)]
  have hp₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+t ≠ i),
      Function.update_of_ne (by omega : j+t ≠ t-1), Function.update_of_ne (by omega : j+t ≠ s-1)]
  rw [hpF] at hF
  rw [hpG] at hG
  change _ * _ * (krAlive _ _ _ r b (kernelReversePrefix h r) *
    (krAlive _ _ _ (s-r) b (fun j => h (j+r)) *
      (krAlive _ _ _ (t-s) b' (fun j => h (j+s)) *
        krAlive _ _ _ (k-t) b (fun j => h (j+t))))) = _
  rw [hp₀, hp₃]
  linear_combination
    krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) *
      (f (kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-1) g) *
        krAlive (Icc 0 (2*eps)) 1 a (t-s) b' (fun j => h (j+s))) * hF +
    a * krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) *
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b')
        (fun j => g (j+r)) * hG

end
end PGM
