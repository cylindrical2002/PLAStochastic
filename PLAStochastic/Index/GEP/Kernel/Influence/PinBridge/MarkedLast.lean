import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.MarkedPin

/-! # Physical coarea reconstruction when the marked gap is last -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

theorem kernel_IF_left_end_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.1 : ℕ) < i) (hi₂ : i+1 = q.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let u := kernelFacetP eps q/a-x-kernelFacetRestA q i (s-2) g
    let v := kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g
    f u * f v * kernelIFSurvival eps a q
        (kernelIFLeftPath eps x a q i (s-2) (t-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (s-r-1) 0 b b' (fun j => g (j+r)) *
          (kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFLeftPath eps x a q i (s-2) (t-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have hl : s-r-2+2 = s-r := by omega
  have hl' : s-r-2+1 = s-r-1 := by omega
  have hm : t-s-1+1 = t-s := by omega
  have hsums := kernel_IF_left_sums hq.1 hi₁.le (by omega) (j := s-2) (m := t-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (eps := eps) (x := x) (a := a) g
  have hends := kernel_IF_bridge_endpoints hq ha h hsums.1 hsums.2
  have hmark : h (s-r-2+1+r) = x := by
    have he : s-r-2+1+r = i := by omega
    simp only [he, h, kernelIFLeftPath, Function.update_self]
  have hF := kernel_pin_marked_end_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 x b b' (s-r-2) (fun j => h (j+r)) hmark (by simpa only [hl] using hends.1)
  have hG := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b' b (t-s-1) (fun j => h (j+s)) (by simpa only [hm] using hends.2)
  have hvF : h (s-r-2+r) = kernelFacetP eps q/a-x-kernelFacetRestA q i (s-2) g := by
    have he : s-r-2+r = s-2 := by omega
    simp only [he, h, kernelIFLeftPath, Function.update_of_ne (by omega : s-2 ≠ i),
      Function.update_of_ne (by omega : s-2 ≠ t-1), Function.update_self]
  have hvG : h (t-s-1+s) = kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g := by
    have he : t-s-1+s = t-1 := by omega
    simp only [he, h, kernelIFLeftPath, Function.update_of_ne (by omega : t-1 ≠ i),
      Function.update_self]
  rw [hvF, hl, hl', abs_of_pos ha] at hF
  rw [hvG, hm, abs_of_pos ha] at hG
  have hpF : kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (s-r-1) 0 b b' (fun j => h (j+r)) =
      kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (s-r-1) 0 b b' (fun j => g (j+r)) := by
    simp only [kernelMarkedPinBlock, if_true]
    congr 1
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+r ≠ i),
      Function.update_of_ne (by omega : j+r ≠ t-1), Function.update_of_ne (by omega : j+r ≠ s-2)]
  have hpG : kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => h (j+s)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+s ≠ i),
      Function.update_of_ne (by omega : j+s ≠ t-1), Function.update_of_ne (by omega : j+s ≠ s-2)]
  have hp₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFLeftPath,
      Function.update_of_ne (by omega : r-1-j ≠ i),
      Function.update_of_ne (by omega : r-1-j ≠ t-1),
      Function.update_of_ne (by omega : r-1-j ≠ s-2)]
  have hp₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFLeftPath, Function.update_of_ne (by omega : j+t ≠ i),
      Function.update_of_ne (by omega : j+t ≠ t-1), Function.update_of_ne (by omega : j+t ≠ s-2)]
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
      kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (s-r-1) 0 b b' (fun j => g (j+r)) * hG

theorem kernel_IF_right_end_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.2.1 : ℕ) < i) (hi₂ : i+1 = q.2.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let u := kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-2) g
    let v := kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g
    f u * f v * kernelIFSurvival eps a q
        (kernelIFRightPath eps x a q i (t-2) (s-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
          (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) *
          (kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (t-s-1) 0 b' b (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFRightPath eps x a q i (t-2) (s-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have hl : s-r-1+1 = s-r := by omega
  have hm : t-s-2+2 = t-s := by omega
  have hm' : t-s-2+1 = t-s-1 := by omega
  have hsums := kernel_IF_right_sums hq.1 hi₁.le (by omega) (j := t-2) (m := s-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (eps := eps) (x := x) (a := a) g
  have hends := kernel_IF_bridge_endpoints hq ha h hsums.1 hsums.2
  have hmark : h (t-s-2+1+s) = x := by
    have he : t-s-2+1+s = i := by omega
    simp only [he, h, kernelIFRightPath, Function.update_self]
  have hF := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b b' (s-r-1) (fun j => h (j+r)) (by simpa only [hl] using hends.1)
  have hG := kernel_pin_marked_end_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 x b' b (t-s-2) (fun j => h (j+s)) hmark (by simpa only [hm] using hends.2)
  have hvF : h (s-r-1+r) = kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g := by
    have he : s-r-1+r = s-1 := by omega
    simp only [he, h, kernelIFRightPath, Function.update_of_ne (by omega : s-1 ≠ i),
      Function.update_self]
  have hvG : h (t-s-2+s) = kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-2) g := by
    have he : t-s-2+s = t-2 := by omega
    simp only [he, h, kernelIFRightPath, Function.update_of_ne (by omega : t-2 ≠ i),
      Function.update_of_ne (by omega : t-2 ≠ s-1), Function.update_self]
  rw [hvF, hl, abs_of_pos ha] at hF
  rw [hvG, hm, hm', abs_of_pos ha] at hG
  have hpF : kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => h (j+r)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+r ≠ i),
      Function.update_of_ne (by omega : j+r ≠ s-1), Function.update_of_ne (by omega : j+r ≠ t-2)]
  have hpG : kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (t-s-1) 0 b' b (fun j => h (j+s)) =
      kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (t-s-1) 0 b' b (fun j => g (j+s)) := by
    simp only [kernelMarkedPinBlock, if_true]
    congr 1
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+s ≠ i),
      Function.update_of_ne (by omega : j+s ≠ s-1), Function.update_of_ne (by omega : j+s ≠ t-2)]
  have hp₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFRightPath,
      Function.update_of_ne (by omega : r-1-j ≠ i),
      Function.update_of_ne (by omega : r-1-j ≠ s-1),
      Function.update_of_ne (by omega : r-1-j ≠ t-2)]
  have hp₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFRightPath, Function.update_of_ne (by omega : j+t ≠ i),
      Function.update_of_ne (by omega : j+t ≠ s-1), Function.update_of_ne (by omega : j+t ≠ t-2)]
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
      (f (kernelFacetQ eps q/a-x-kernelFacetRestRight q i (t-2) g) *
        krAlive (Icc 0 (2*eps)) 1 a (t-s) b' (fun j => h (j+s))) * hF +
    a * krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) *
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) * hG

/-- The final random coordinate, excluding the prescribed marked gap. -/
def kernelIFPinSmoothing (t i : ℕ) : ℕ := if i+1 < t then t-1 else t-2

theorem kernel_IF_pin_smoothing_mem {r t i : ℕ} (hrt : r+1 < t)
    (_hi₁ : r ≤ i) (hi₂ : i < t) :
    r ≤ kernelIFPinSmoothing t i ∧ kernelIFPinSmoothing t i < t ∧
      kernelIFPinSmoothing t i ≠ i := by
  unfold kernelIFPinSmoothing
  split_ifs <;> omega

theorem kernel_IF_left_full_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hlong : (q.1 : ℕ)+1 < q.2.1)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let j := kernelIFPinSmoothing s i
    f (kernelFacetP eps q/a-x-kernelFacetRestA q i j g) *
      f (kernelFacetQ eps q/a-kernelFacetRestB q (t-1) g) *
      kernelIFSurvival eps a q (kernelIFLeftPath eps x a q i j (t-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (i-r) (s-i-1) b b' (fun j => g (j+r)) *
          (kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
            (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  by_cases hi : i+1 < (q.2.1 : ℕ)
  · have hlen : i-(q.1 : ℕ)+((q.2.1 : ℕ)-i-1) = (q.2.1 : ℕ)-q.1-1 := by omega
    have hn : (q.2.1 : ℕ)-i-1 ≠ 0 := by omega
    simpa only [kernelIFPinSmoothing, if_pos hi, kernelMarkedPinBlock, if_neg hn, hlen] using
      kernel_IF_left_last_pins (x := x) hq ha hi₁ hi f g
  · have he : i+1 = (q.2.1 : ℕ) := by omega
    have hl : (q.1 : ℕ) < i := by omega
    have hright : (q.2.1 : ℕ)-i-1 = 0 := by omega
    have hleft : i-(q.1 : ℕ) = (q.2.1 : ℕ)-q.1-1 := by omega
    simpa only [kernelIFPinSmoothing, if_neg hi, hright, hleft] using
      kernel_IF_left_end_pins (x := x) hq ha hl he f g

theorem kernel_IF_right_full_pins {eps x a : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hlong : (q.2.1 : ℕ)+1 < q.2.2.1)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    let j := kernelIFPinSmoothing t i
    f (kernelFacetQ eps q/a-x-kernelFacetRestRight q i j g) *
      f (kernelFacetP eps q/a-kernelFacetRestLeft q (s-1) g) *
      kernelIFSurvival eps a q (kernelIFRightPath eps x a q i j (s-1) g) =
      a^2 * (krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
          (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) *
          (kernelMarkedPinBlock (Icc 0 (2*eps)) f 1 a x (i-s) (t-i-1) b' b (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t))))) := by
  dsimp only
  by_cases hi : i+1 < (q.2.2.1 : ℕ)
  · have hlen : i-(q.2.1 : ℕ)+((q.2.2.1 : ℕ)-i-1) = (q.2.2.1 : ℕ)-q.2.1-1 := by omega
    have hn : (q.2.2.1 : ℕ)-i-1 ≠ 0 := by omega
    simpa only [kernelIFPinSmoothing, if_pos hi, kernelMarkedPinBlock, if_neg hn, hlen] using
      kernel_IF_right_last_pins (x := x) hq ha hi₁ hi f g
  · have he : i+1 = (q.2.2.1 : ℕ) := by omega
    have hl : (q.2.1 : ℕ) < i := by omega
    have hright : (q.2.2.1 : ℕ)-i-1 = 0 := by omega
    have hleft : i-(q.2.1 : ℕ) = (q.2.2.1 : ℕ)-q.2.1-1 := by omega
    simpa only [kernelIFPinSmoothing, if_neg hi, hright, hleft] using
      kernel_IF_right_end_pins (x := x) hq ha hl he f g

end
end PGM
