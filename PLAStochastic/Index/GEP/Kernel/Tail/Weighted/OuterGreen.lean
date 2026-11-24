import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.ExtremeSlopeOuter
import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Bulk

/-! # Actual physical weights in both outer Green directions at all slopes -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

theorem measurable_kernelPhysicalSurv_param {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure ℝ) {J : Set ℝ} (hJ : MeasurableSet J)
    {β a s y : X → ℝ} (hβ : Measurable β) (ha : Measurable a)
    (hs : Measurable s) (hy : Measurable y) (n : ℕ) :
    Measurable (fun p => kernelPhysicalSurv J ν (β p) (a p) (s p) n (y p)) := by
  unfold kernelPhysicalSurv
  have hm : Measurable (fun q : X × (ℕ → ℝ) =>
      krAlive J (β q.1) (a q.1) n (y q.1) q.2 * Real.exp (s q.1 * gapKeys q.2 n)) :=
    (measurable_krAlive_param hJ (hβ.comp measurable_fst) (ha.comp measurable_fst)
      (hy.comp measurable_fst) measurable_snd n).mul
        (((hs.comp measurable_fst).mul ((rawAsm_measurable_gapKeys n).comp measurable_snd)).exp)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The exact endpoint constraint bounds the physical weight by the time
weight at slopes with a fixed positive floor. -/
theorem kernelPhysicalSurv_le_time (ν : ProbabilityMeasure ℝ)
    (α w a : ℝ) (ha : 0 < a) (β a' : ℝ)
    (hdir : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a))
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) (y : ℝ) :
    kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y ≤
      Real.exp (s * ((n : ℝ) + w) / a) * krSurv (Icc α (α + w)) (ν : Measure ℝ) β a' n y := by
  have hp (g : ℕ → ℝ) :
      krAlive (Icc α (α + w)) β a' n y g * Real.exp (s * gapKeys g n) ≤
        Real.exp (s * ((n : ℝ) + w) / a) * krAlive (Icc α (α + w)) β a' n y g := by
    by_cases hy : y ∈ Icc α (α + w)
    · by_cases hz : kWalk y β a' g n ∈ Icc α (α + w)
      · have hgap : a * gapKeys g n ≤ (n : ℝ) + w := by
          rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [mem_Icc, kWalk, mul_one] at hy hz
            linarith [hy.1, hy.2, hz.1, hz.2]
          · simp only [mem_Icc, kWalk] at hy hz
            nlinarith [hy.1, hy.2, hz.1, hz.2]
        have hh : s * gapKeys g n ≤ s * ((n : ℝ) + w) / a := by
          apply (le_div_iff₀ ha).mpr
          nlinarith [mul_le_mul_of_nonneg_left hgap hs]
        have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (krAlive_nonneg (J := Icc α (α + w)) (β := β) (a := a') n y g)
        simpa [mul_comm] using this
      · have he := krAlive_mul_indicator (J := Icc α (α + w)) (β := β) (a := a') n y g
        rw [indicator_of_notMem hz, mul_zero] at he
        rw [← he, zero_mul, mul_zero]
    · rw [krAlive_eq_zero_of_notMem hy, zero_mul, mul_zero]
  have hi := (kr_integrable_of_bdd (measurable_krAlive_right measurableSet_Icc β a' n y)
    (abs_krAlive_le_one (J := Icc α (α + w)) n y) :
      Integrable (fun g => krAlive (Icc α (α + w)) β a' n y g) (iidLaw ν))
  have hh := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun g => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _))
    (hi.const_mul (Real.exp (s * ((n : ℝ) + w) / a))) (Filter.Eventually.of_forall hp)
  simpa only [kernelPhysicalSurv, integral_const_mul, ← krSurv_eq_integral measurableSet_Icc] using hh

/-- With physical weight `s ≤ ρ/w²`, genuine outer Green sums keep the
unweighted fixed cubic width budget above slope one half. The constant `ρ`
is fixed solely by the regular-law class. -/
theorem kernel_regLaw_weighted_outer_green_large (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w a : ℝ, 1 ≤ w → 1 / 2 ≤ a →
      ∀ β a' : ℝ, (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a) →
      ∀ s : ℝ, 0 ≤ s → s ≤ ρ / w ^ 2 → ∀ y : ℝ,
        Summable (fun n : ℕ => kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y) ∧
        (∑' n : ℕ, kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y) ≤ K * w ^ 3 := by
  obtain ⟨c, K, hc, hK, hb⟩ := kernel_regLaw_surv_spectral_all D θ vlo vhi (1 / 2)
    hD hθ hvlo hv (by norm_num)
  refine ⟨min 1 (c / 4), Real.exp 2 * K * (1 + 2 / c),
    lt_min (by norm_num) (by positivity), by positivity, ?_⟩
  intro ν hν α w a hw ha β a' hdir s hs0 hs y
  have hw0 : 0 < w := by linarith
  have ha0 : 0 < a := by linarith
  have ha' : 1 / 2 ≤ |a'| := by
    rcases hdir with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simpa [abs_of_pos ha0] using ha
  have hs1 : s ≤ 1 / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  have hsc : s ≤ c / (4 * w ^ 2) := by
    apply hs.trans
    convert div_le_div_of_nonneg_right (min_le_right (1 : ℝ) (c / 4)) (sq_nonneg w) using 1
    ring
  let u := c / (2 * w ^ 2)
  have hu : 0 < u := by positivity
  have hmaj (n : ℕ) : kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y ≤
      (Real.exp 2 * K * w) * Real.exp (-u) ^ n := by
    have hh := mul_le_mul_of_nonneg_left (hb ν hν α w β a' hw ha' n y)
      (Real.exp_nonneg (s * ((n : ℝ) + w) / a))
    apply (kernelPhysicalSurv_le_time ν α w a ha0 β a' hdir hs0 n y).trans (hh.trans ?_)
    have hsw : 2 * s * w ≤ 2 := by
      have h := (le_div_iff₀ (sq_pos_of_pos hw0)).mp hs1
      nlinarith [mul_nonneg hs0 (show 0 ≤ w ^ 2 - w by nlinarith)]
    have hsn : 2 * s ≤ c / (2 * w ^ 2) :=
      (mul_le_mul_of_nonneg_left hsc (by norm_num : 0 ≤ (2 : ℝ))).trans_eq (by ring)
    have he : s * ((n : ℝ) + w) / a + (-c * n / w ^ 2) ≤ 2 + (-u) * n := by
      have hsa : s * ((n : ℝ) + w) / a ≤ 2 * s * ((n : ℝ) + w) := by
        apply (div_le_iff₀ ha0).mpr
        nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * s * ((n : ℝ) + w) by positivity)]
      have hn := mul_le_mul_of_nonneg_right hsn (Nat.cast_nonneg (α := ℝ) n)
      have heq : -c * (n : ℝ) / w ^ 2 = -(2 * (c / (2 * w ^ 2) * n)) := by ring
      rw [heq]
      dsimp [u]
      nlinarith
    have hpow : Real.exp (-u) ^ n = Real.exp ((-u) * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]
    calc
      _ = (K * w) * Real.exp (s * ((n : ℝ) + w) / a + (-c * n / w ^ 2)) := by rw [Real.exp_add]; ring
      _ ≤ (K * w) * Real.exp (2 + (-u) * n) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
      _ = _ := by rw [Real.exp_add]; ring
  have hr : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := (summable_geometric_of_lt_one (Real.exp_nonneg (-u)) hr).mul_left (Real.exp 2 * K * w)
  have hsum := Summable.of_nonneg_of_le (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) hmaj hgeom
  refine ⟨hsum, ?_⟩
  apply (hsum.tsum_le_tsum hmaj hgeom).trans
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) hr, ← one_div]
  apply (mul_le_mul_of_nonneg_left (kernel_one_div_one_sub_exp_neg_le hu) (by positivity : 0 ≤ Real.exp 2 * K * w)).trans
  dsimp [u]
  have he : 1 / (c / (2 * w ^ 2)) = 2 * w ^ 2 / c := by field_simp
  rw [he]
  have hw2 : 1 ≤ w ^ 2 := by nlinarith
  have hh : 1 + 2 * w ^ 2 / c ≤ (1 + 2 / c) * w ^ 2 := by
    calc
      _ ≤ w ^ 2 + 2 * w ^ 2 / c := by linarith
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp 2 * K * w by positivity)).trans_eq (by ring)

/-- The genuine exterior physical weights, with both endpoint orientations. -/
def kernelPhysicalOuterWeight (ν : ProbabilityMeasure ℝ) (w s a : ℝ) : ℝ :=
  (∑' n, kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s n 0) *
    (∑' n, kernelPhysicalSurv (Icc 0 w) ν 1 a s n 0) +
  (∑' n, kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s n w) *
    (∑' n, kernelPhysicalSurv (Icc 0 w) ν 1 a s n w)

theorem kernelPhysicalOuterWeight_nonneg (ν : ProbabilityMeasure ℝ) (w s a : ℝ) :
    0 ≤ kernelPhysicalOuterWeight ν w s a :=
  add_nonneg (mul_nonneg (tsum_nonneg fun _ => kernelPhysicalSurv_nonneg _ _ _ _ _ _ _)
      (tsum_nonneg fun _ => kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))
    (mul_nonneg (tsum_nonneg fun _ => kernelPhysicalSurv_nonneg _ _ _ _ _ _ _)
      (tsum_nonneg fun _ => kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))

theorem measurable_kernelPhysicalOuterWeight (ν : ProbabilityMeasure ℝ) (w s : ℝ) :
    Measurable (kernelPhysicalOuterWeight ν w s) := by
  unfold kernelPhysicalOuterWeight
  apply Measurable.add <;> apply Measurable.mul <;> apply Measurable.tsum <;>
    intro n <;> apply measurable_kernelPhysicalSurv_param ν measurableSet_Icc <;> fun_prop

/-- The allowed output exponent is fixed before any arbitrary input exponent.
At physical weight `s ≤ ρ/w²`, both actual outer directions have the same
polynomial budgets as their unweighted versions. -/
theorem kernel_regLaw_physical_outer_weight_bound (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ Ks Kl : ℝ, 0 < ρ ∧ 0 < Ks ∧ 0 < Kl ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w s a : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → 0 < a →
        kernelPhysicalOuterWeight ν w s a ≤
          if a ≤ 1 / 2 then Ks * w ^ 2 else Kl * w ^ 6 := by
  obtain ⟨ρs, Ks, hρs, hKs, hsmall⟩ :=
    kernel_regLaw_weighted_outer_green_extreme D θ vlo vhi hD hθ hvlo
  obtain ⟨ρl, Kl, hρl, hKl, hlarge⟩ :=
    kernel_regLaw_weighted_outer_green_large D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρl (min ρs 1), 2 * Ks ^ 2, 2 * Kl ^ 2,
    lt_min hρl (lt_min hρs (by norm_num)), by positivity, by positivity, ?_⟩
  intro ν hν w s a hw hs0 hs ha
  have hw0 : 0 < w := by linarith
  have hs' := (le_div_iff₀ (sq_pos_of_pos hw0)).mp hs
  have hsρ : s ≤ ρs := by
    have hh := (min_le_right ρl (min ρs 1)).trans (min_le_left _ _)
    have hsw := mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hs0
    nlinarith
  have hsw : s ≤ 1 / w := by
    apply (le_div_iff₀ hw0).mpr
    have hh := (min_le_right ρl (min ρs 1)).trans (min_le_right _ _)
    have hsw := mul_le_mul_of_nonneg_left (show w ≤ w ^ 2 by nlinarith) hs0
    linarith
  have hsl : s ≤ ρl / w ^ 2 := hs.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo]
    have hp (y : ℝ) := (hsmall ν hν 0 w a hw ha (Or.inl halo) 1 a (Or.inl ⟨rfl, rfl⟩) s hs0 hsρ hsw y).2
    have hm (y : ℝ) := (hsmall ν hν 0 w a hw ha (Or.inl halo) (-1) (-a) (Or.inr ⟨rfl, rfl⟩) s hs0 hsρ hsw y).2
    simp only [zero_add] at hp hm
    have hprod (y : ℝ) := mul_le_mul (hm y) (hp y)
      (tsum_nonneg fun n => kernelPhysicalSurv_nonneg (Icc 0 w) ν 1 a s n y)
      (show 0 ≤ Ks * w by positivity)
    exact (add_le_add (hprod 0) (hprod w)).trans_eq (by ring)
  · rw [if_neg halo]
    have hp (y : ℝ) := (hlarge ν hν 0 w a hw (le_of_lt (lt_of_not_ge halo)) 1 a (Or.inl ⟨rfl, rfl⟩) s hs0 hsl y).2
    have hm (y : ℝ) := (hlarge ν hν 0 w a hw (le_of_lt (lt_of_not_ge halo)) (-1) (-a) (Or.inr ⟨rfl, rfl⟩) s hs0 hsl y).2
    simp only [zero_add] at hp hm
    have hprod (y : ℝ) := mul_le_mul (hm y) (hp y)
      (tsum_nonneg fun n => kernelPhysicalSurv_nonneg (Icc 0 w) ν 1 a s n y)
      (show 0 ≤ Kl * w ^ 3 by positivity)
    exact (add_le_add (hprod 0) (hprod w)).trans_eq (by ring)

end
end PGM
