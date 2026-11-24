import PLAStochastic.Index.GEP.Kernel.Influence.Pins.DiracFacet

/-! # Actual deterministic marked bridge and the remaining random pin -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_contact_endpoints_mem {eps : ℝ} (heps : 0 ≤ eps) {k : ℕ}
    (q : FluxFacetIndex k) :
    eps-fluxFacetSign q*eps ∈ Icc 0 (2*eps) ∧
      eps+fluxFacetSign q*eps ∈ Icc 0 (2*eps) := by
  rcases kernel_fluxFacetSign_cases q with h | h <;> rw [h] <;>
    constructor <;> constructor <;> nlinarith

theorem kernel_IF_left_short_sums {eps x : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFLeftShortPath eps x q m g) q.2.1-
        gapKeys (kernelIFLeftShortPath eps x q m g) q.1 = x ∧
      gapKeys (kernelIFLeftShortPath eps x q m g) q.2.2.1-
        gapKeys (kernelIFLeftShortPath eps x q m g) q.2.1 =
          kernelFacetQ eps q/kernelFacetP eps q*x := by
  constructor
  · rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ, kernelIFLeftShortPath, Function.update_self]
    ring
  · unfold kernelIFLeftShortPath
    rw [kernel_block_sum_update_outside _ hq.1.2.le (Or.inl hq.1.1),
      kernel_block_sum_update_inside _ hm₁ hm₂]
    unfold kernelFacetRestB
    ring

theorem kernel_IF_left_short_pins {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let a := kernelFacetP eps q/x
    let s : ℕ := q.2.1
    let t : ℕ := q.2.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    f (kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q (t-1) g) *
      kernelIFSurvival eps a q (kernelIFLeftShortPath eps x q (t-1) g) =
      a * (kernelIFOuterSurvival eps a q g *
        kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
          (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let a := kernelFacetP eps q/x
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFLeftShortPath eps x q (t-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have ha : 0 < a := div_pos hq.2.1 hx
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hPa : kernelFacetP eps q/a = x := by dsimp [a]; field_simp
  have hQa : kernelFacetQ eps q/a = kernelFacetQ eps q/kernelFacetP eps q*x := by
    dsimp [a]
    field_simp
  have hsums := kernel_IF_left_short_sums (x := x) hq hshort (m := t-1) (by omega) (by omega) g
  have hends := kernel_IF_bridge_endpoints hq ha h (hsums.1.trans hPa.symm) (hsums.2.trans hQa.symm)
  have hleft : krAlive (Icc 0 (2*eps)) 1 a (s-r) b (fun j => h (j+r)) = 1 := by
    have he : s-r = 1 := by omega
    rw [he] at hends ⊢
    rw [krAlive_succ_last (n := 0), hends.1, krAlive_zero]
    rw [indicator_of_mem (kernel_IF_contact_endpoints_mem heps q).1,
      indicator_of_mem (kernel_IF_contact_endpoints_mem heps q).2]
    norm_num
  have hn : t-s-1+1 = t-s := by omega
  have hpin := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b' b (t-s-1) (fun j => h (j+s)) (by simpa only [hn] using hends.2)
  have hv : h (t-s-1+s) = kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q (t-1) g := by
    have he : t-s-1+s = t-1 := by omega
    simp only [he, h, kernelIFLeftShortPath, Function.update_of_ne (by omega : t-1 ≠ q.1),
      Function.update_self]
  rw [hv, hn, abs_of_pos ha] at hpin
  have hp : kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => h (j+s)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (t-s-1) b'
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b) (fun j => g (j+s)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFLeftShortPath, Function.update_of_ne (by omega : j+s ≠ q.1),
      Function.update_of_ne (by omega : j+s ≠ t-1)]
  rw [hp] at hpin
  have ho₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFLeftShortPath,
      Function.update_of_ne (by omega : r-1-j ≠ q.1), Function.update_of_ne (by omega : r-1-j ≠ t-1)]
  have ho₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFLeftShortPath, Function.update_of_ne (by omega : j+t ≠ q.1),
      Function.update_of_ne (by omega : j+t ≠ t-1)]
  change _ * (krAlive _ _ _ r b (kernelReversePrefix h r) *
    (krAlive _ _ _ (s-r) b (fun j => h (j+r)) *
      (krAlive _ _ _ (t-s) b' (fun j => h (j+s)) *
        krAlive _ _ _ (k-t) b (fun j => h (j+t))))) = _
  rw [hleft, one_mul, ho₀, ho₃]
  dsimp only [kernelIFOuterSurvival]
  linear_combination
    krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) * hpin

theorem kernel_IF_right_short_sums {eps x : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFRightShortPath eps x q m g) q.2.1-
        gapKeys (kernelIFRightShortPath eps x q m g) q.1 =
          kernelFacetP eps q/kernelFacetQ eps q*x ∧
      gapKeys (kernelIFRightShortPath eps x q m g) q.2.2.1-
        gapKeys (kernelIFRightShortPath eps x q m g) q.2.1 = x := by
  constructor
  · unfold kernelIFRightShortPath
    rw [kernel_block_sum_update_outside _ hq.1.1.le (Or.inr le_rfl),
      kernel_block_sum_update_inside _ hm₁ hm₂]
    unfold kernelFacetRestLeft
    ring
  · rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ, kernelIFRightShortPath, Function.update_self]
    ring

theorem kernel_IF_right_short_pins {eps x : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (heps : 0 ≤ eps) (hx : 0 < x) (f : ℝ → ℝ) (g : ℕ → ℝ) :
    let a := kernelFacetQ eps q/x
    let r : ℕ := q.1
    let s : ℕ := q.2.1
    let b := eps-fluxFacetSign q*eps
    let b' := eps+fluxFacetSign q*eps
    f (kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q (s-1) g) *
      kernelIFSurvival eps a q (kernelIFRightShortPath eps x q (s-1) g) =
      a * (kernelIFOuterSurvival eps a q g *
        kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
          (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r))) := by
  dsimp only
  let r : ℕ := q.1
  let s : ℕ := q.2.1
  let t : ℕ := q.2.2.1
  let a := kernelFacetQ eps q/x
  let b := eps-fluxFacetSign q*eps
  let b' := eps+fluxFacetSign q*eps
  let h := kernelIFRightShortPath eps x q (s-1) g
  have hrs : r < s := hq.1.1
  have hst : s < t := hq.1.2
  have ha : 0 < a := div_pos hq.2.2 hx
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hQa : kernelFacetQ eps q/a = x := by dsimp [a]; field_simp
  have hPa : kernelFacetP eps q/a = kernelFacetP eps q/kernelFacetQ eps q*x := by
    dsimp [a]
    field_simp
  have hsums := kernel_IF_right_short_sums (x := x) hq hshort (m := s-1) (by omega) (by omega) g
  have hends := kernel_IF_bridge_endpoints hq ha h (hsums.1.trans hPa.symm) (hsums.2.trans hQa.symm)
  have hright : krAlive (Icc 0 (2*eps)) 1 a (t-s) b' (fun j => h (j+s)) = 1 := by
    have he : t-s = 1 := by omega
    rw [he] at hends ⊢
    rw [krAlive_succ_last (n := 0), hends.2, krAlive_zero]
    rw [indicator_of_mem (kernel_IF_contact_endpoints_mem heps q).2,
      indicator_of_mem (kernel_IF_contact_endpoints_mem heps q).1]
    norm_num
  have hn : s-r-1+1 = s-r := by omega
  have hpin := kernel_pin_density_factor_of_endpoint (Icc 0 (2*eps)) f ha.ne'
    1 b b' (s-r-1) (fun j => h (j+r)) (by simpa only [hn] using hends.1)
  have hv : h (s-r-1+r) = kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q (s-1) g := by
    have he : s-r-1+r = s-1 := by omega
    simp only [he, h, kernelIFRightShortPath, Function.update_of_ne (by omega : s-1 ≠ q.2.1),
      Function.update_self]
  rw [hv, hn, abs_of_pos ha] at hpin
  have hp : kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
      (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => h (j+r)) =
      kernelBlockTest (Icc 0 (2*eps)) 1 a (s-r-1) b
        (fun z => krKer (Icc 0 (2*eps)) f 1 a z b') (fun j => g (j+r)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [h, kernelIFRightShortPath, Function.update_of_ne (by omega : j+r ≠ q.2.1),
      Function.update_of_ne (by omega : j+r ≠ s-1)]
  rw [hp] at hpin
  have ho₀ : krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix h r) =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) := by
    apply kernel_krAlive_congr
    intro j hj
    simp only [kernelReversePrefix, h, kernelIFRightShortPath,
      Function.update_of_ne (by omega : r-1-j ≠ q.2.1), Function.update_of_ne (by omega : r-1-j ≠ s-1)]
  have ho₃ : krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => h (j+t)) =
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) := by
    apply kernel_krAlive_congr
    intro j _
    simp only [h, kernelIFRightShortPath, Function.update_of_ne (by omega : j+t ≠ q.2.1),
      Function.update_of_ne (by omega : j+t ≠ s-1)]
  change _ * (krAlive _ _ _ r b (kernelReversePrefix h r) *
    (krAlive _ _ _ (s-r) b (fun j => h (j+r)) *
      (krAlive _ _ _ (t-s) b' (fun j => h (j+s)) *
        krAlive _ _ _ (k-t) b (fun j => h (j+t))))) = _
  rw [hright, one_mul, ho₀, ho₃]
  dsimp only [kernelIFOuterSurvival]
  linear_combination
    krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
      krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)) * hpin

end
end PGM
