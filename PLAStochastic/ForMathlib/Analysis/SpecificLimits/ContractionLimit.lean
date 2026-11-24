import PLAStochastic.ForMathlib.Analysis.SpecificLimits.GeometricTracking

/-!
# Scalar limits on contracting orbits

A Lipschitz scalar on a class of finite diameter has the same limit along
any two orbits in that class. No completeness of the underlying class is needed.
-/

namespace PGM

open Filter Topology

/-- A scalar orbit converges, with a geometric bound on its limit error. -/
theorem contraction_scalar_limit {α : Type*} (Φ : α → α) (d : α → α → ℝ)
    (F : α → ℝ) (S : α → Prop) {Lc Dst : ℝ} (hLc : 0 ≤ Lc)
    (hcon : ∀ x y, S x → S y → d (Φ x) (Φ y) ≤ d x y / 2)
    (hdiam : ∀ x y, S x → S y → d x y ≤ Dst)
    (hlip : ∀ x y, S x → S y → |F x - F y| ≤ Lc * d x y)
    (x : α) (hx : ∀ i, S (Φ^[i] x)) :
    ∃ c, Tendsto (fun i : ℕ => F (Φ^[i] x)) atTop (𝓝 c) ∧
      ∀ i, |F (Φ^[i] x) - c| ≤ Lc * Dst / 2 ^ i := by
  apply geometric_cauchy_limit
  intro j k hjk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have hdist : ∀ i, d (Φ^[i] x) (Φ^[i] (Φ^[m] x)) ≤ d x (Φ^[m] x) / 2 ^ i := by
    apply orbit_contract
    intro i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply hcon _ _ (hx i)
    rw [← Function.iterate_add_apply]
    exact hx _
  have hdm : d x (Φ^[m] x) ≤ Dst := hdiam _ _ (hx 0) (hx m)
  have hym : S (Φ^[j] (Φ^[m] x)) := by
    rw [← Function.iterate_add_apply]
    exact hx _
  rw [Function.iterate_add_apply]
  calc
    |F (Φ^[j] x) - F (Φ^[j] (Φ^[m] x))| ≤
        Lc * d (Φ^[j] x) (Φ^[j] (Φ^[m] x)) := hlip _ _ (hx j) hym
    _ ≤ Lc * (d x (Φ^[m] x) / 2 ^ j) := mul_le_mul_of_nonneg_left (hdist j) hLc
    _ ≤ Lc * (Dst / 2 ^ j) := by gcongr
    _ = Lc * Dst / 2 ^ j := by ring

/-- All regular scalar orbits converge to the `limUnder` of any reference orbit. -/
theorem contraction_scalar_tendsto_reference {α : Type*} (Φ : α → α) (d : α → α → ℝ)
    (F : α → ℝ) (S : α → Prop) {Lc Dst : ℝ} (hLc : 0 ≤ Lc)
    (hcon : ∀ x y, S x → S y → d (Φ x) (Φ y) ≤ d x y / 2)
    (hdiam : ∀ x y, S x → S y → d x y ≤ Dst)
    (hlip : ∀ x y, S x → S y → |F x - F y| ≤ Lc * d x y)
    (x y : α) (hx : ∀ i, S (Φ^[i] x)) (hy : ∀ i, S (Φ^[i] y)) :
    Tendsto (fun i : ℕ => F (Φ^[i] y)) atTop
      (𝓝 (limUnder atTop (fun i : ℕ => F (Φ^[i] x)))) := by
  obtain ⟨c, hc, herror⟩ := contraction_scalar_limit Φ d F S hLc hcon hdiam hlip x hx
  rw [hc.limUnder_eq]
  have hyc (i : ℕ) : |F (Φ^[i] y) - c| ≤ 2 * (Lc * Dst) / 2 ^ i := by
    have hdist := orbit_contract Φ d y x (fun i => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hcon _ _ (hy i) (hx i)) i
    have hdm : d y x ≤ Dst := hdiam _ _ (hy 0) (hx 0)
    have hle : d (Φ^[i] y) (Φ^[i] x) ≤ Dst / 2 ^ i := by
      exact hdist.trans (by gcongr)
    have h1 := hlip _ _ (hy i) (hx i)
    have h2 := mul_le_mul_of_nonneg_left hle hLc
    have h3 := abs_sub_le (F (Φ^[i] y)) (F (Φ^[i] x)) c
    have h4 := herror i
    have he : 2 * (Lc * Dst) / 2 ^ i = Lc * (Dst / 2 ^ i) + Lc * Dst / 2 ^ i := by ring
    rw [he]
    linarith
  apply tendsto_iff_dist_tendsto_zero.2
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) hyc
  have hp : Tendsto (fun i : ℕ => (2 : ℝ) ^ i) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa using tendsto_const_nhds.div_atTop hp

end PGM
