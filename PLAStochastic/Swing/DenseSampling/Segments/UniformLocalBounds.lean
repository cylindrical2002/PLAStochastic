import PLAStochastic.Swing.DenseSampling.Segments.FirstRecordingLimit
import PLAStochastic.Swing.Algorithm.RejectionDirection

/-!
# Uniform local bounds for native recordings

A line that reduces the carried anchor error linearly fits any fixed number
of sufficiently close new samples. This holds uniformly over all anchors in
a compact interval. The original rejection condition therefore forces the
number of accepted new samples to grow without bound as the mesh shrinks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's explicit candidate from an arbitrary fitted anchor. -/
theorem nativePrefix_feasible_of_small_displacements (y : ℕ → ℝ) {h ε q : ℝ}
    (hh : 0 < h) (s n : ℕ) (hn : 0 < n) (hq : |q - y s| ≤ ε)
    (hsmall : ∀ j ∈ Finset.Icc (s + 1) (s + n), |y j - y s| ≤ ε / (n : ℝ)) :
    nativePrefixFeasible (fun j => (j : ℝ) * h) y ε s (s + n) q := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hε : 0 ≤ ε := (abs_nonneg _).trans hq
  let η := q - y s
  refine ⟨-η / ((n : ℝ) * h), fun j hj => ?_⟩
  have hj' := Finset.mem_Icc.mp hj
  have hjlow : (s : ℝ) + 1 ≤ j := by exact_mod_cast hj'.1
  have hjup : (j : ℝ) ≤ (s : ℝ) + n := by exact_mod_cast hj'.2
  have hk0 : 1 ≤ (j : ℝ) - (s : ℝ) := by linarith
  have hkn : (j : ℝ) - (s : ℝ) ≤ (n : ℝ) := by linarith
  have hw0 : 0 ≤ 1 - ((j : ℝ) - s) / n := by
    exact sub_nonneg.mpr ((div_le_one hnR).mpr hkn)
  have hw1 : 1 - ((j : ℝ) - s) / n ≤ 1 := by
    have hdiv := div_nonneg (by linarith : 0 ≤ (j : ℝ) - s) hnR.le
    linarith
  have heq : y j - (q + (-η / ((n : ℝ) * h)) * ((j : ℝ) * h - (s : ℝ) * h)) =
      (y j - y s) - η * (1 - ((j : ℝ) - s) / n) := by
    dsimp only [η]
    field_simp [hnR.ne', hh.ne']
    ring
  change |y j - (q + (-η / ((n : ℝ) * h)) * ((j : ℝ) * h - (s : ℝ) * h))| ≤ ε
  rw [heq]
  calc
    _ ≤ |y j - y s| + |η * (1 - ((j : ℝ) - s) / n)| := abs_sub _ _
    _ ≤ ε / n + ε * (1 - ((j : ℝ) - s) / n) := by
      rw [abs_mul, abs_of_nonneg hw0]
      exact add_le_add (hsmall j hj) (mul_le_mul_of_nonneg_right hq hw0)
    _ ≤ ε := by
      have hm : ε / n ≤ ε * (((j : ℝ) - s) / n) := by
        have hratio : (1 : ℝ) / n ≤ ((j : ℝ) - s) / n :=
          (div_le_div_iff_of_pos_right hnR).mpr hk0
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hratio hε
      linarith

/-- Restricting the actual accepted prefix only removes constraints. -/
theorem nativePrefixFeasible_mono_end {t y : ℕ → ℝ} {ε q : ℝ} {s e E : ℕ}
    (h : nativePrefixFeasible t y ε s E q) (he : e ≤ E) : nativePrefixFeasible t y ε s e q := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun i hi => hm i ?_⟩
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans he⟩

/-- If n nearby new observations admit the explicit candidate, a true
rejection recording cannot contain fewer than n accepted new observations. -/
theorem native_rejection_span_ge_of_small_displacements (y : ℕ → ℝ) {h ε q : ℝ}
    (hh : 0 < h) (s e n : ℕ) (hn : 0 < n) (hse : s < e) (hq : |q - y s| ≤ ε)
    (hsmall : ∀ j ∈ Finset.Icc (s + 1) (s + n), |y j - y s| ≤ ε / (n : ℝ))
    (hreject : ¬ nativePrefixFeasible (fun j => (j : ℝ) * h) y ε s (e + 1) q) :
    n ≤ e - s := by
  by_contra h
  have he : e + 1 ≤ s + n := by omega
  exact hreject (nativePrefixFeasible_mono_end
    (nativePrefix_feasible_of_small_displacements y hh s n hn hq hsmall) he)

/-- The candidate is uniform over every fitted anchor in a fixed compact
interval. The path is already defined beyond the observation horizon, so EOF
cannot create an artificial short completed interval. -/
theorem exists_uniform_nativePrefix_mesh (f : C(ℝ, ℝ)) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 < ε) (n : ℕ) (hn : 0 < n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ s : ℕ, (s : ℝ) * h ≤ T →
      ∀ q : ℝ, |q - f ((s : ℝ) * h)| ≤ ε →
        nativePrefixFeasible (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε s (s + n) q := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous (f := f) f.continuous.continuousOn
    (s := Icc (0 : ℝ) (T + 1))
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / n) (div_pos hε hnR)
  let δ := min 1 d / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos (lt_min zero_lt_one hd) (by positivity)
  refine ⟨δ, hδ, fun h hh hhδ s hs q hq => ?_⟩
  apply nativePrefix_feasible_of_small_displacements _ hh s n hn hq
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hs0 : 0 ≤ (s : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hjs : (s : ℝ) ≤ j := by exact_mod_cast (show s ≤ j by omega)
  have hjn : (j : ℝ) ≤ (s : ℝ) + n := by exact_mod_cast hj'.2
  have hhmin : h * ((n : ℝ) + 1) < min 1 d := (lt_div_iff₀ (by positivity)).mp hhδ
  have hnh1 : (n : ℝ) * h < 1 := by have := min_le_left (1 : ℝ) d; nlinarith
  have hnhd : (n : ℝ) * h < d := by have := min_le_right (1 : ℝ) d; nlinarith
  have hmems : (s : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := ⟨hs0, by linarith⟩
  have hmemj : (j : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := by
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) hh.le
    · nlinarith
  have hdist : dist ((j : ℝ) * h) ((s : ℝ) * h) < d := by
    rw [Real.dist_eq, abs_of_nonneg (by nlinarith : 0 ≤ (j : ℝ) * h - (s : ℝ) * h)]
    nlinarith
  have hm := hmod _ hmemj _ hmems hdist
  have hm' : |f ((j : ℝ) * h) - f ((s : ℝ) * h)| < ε / n := by
    simpa only [Real.dist_eq] using hm
  exact hm'.le

/-- Every genuinely rejected interval on the compact horizon eventually has
at least n accepted new samples, uniformly in its anchor and chosen line. -/
theorem eventually_native_completed_spans_ge (f : C(ℝ, ℝ)) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) (n : ℕ) :
    ∀ᶠ i in l, ∀ s e : ℕ, s < e → (s : ℝ) * h i ≤ T → ∀ q : ℝ,
      |q - f ((s : ℝ) * h i)| ≤ ε →
      (¬ nativePrefixFeasible (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε s (e + 1) q) →
      n ≤ e - s := by
  by_cases hn : n = 0
  · subst n
    exact Eventually.of_forall (fun _ _ _ _ _ _ _ _ => Nat.zero_le _)
  obtain ⟨δ, hδ, hfit⟩ := exists_uniform_nativePrefix_mesh f hT hε n (Nat.pos_of_ne_zero hn)
  filter_upwards [hconv.eventually_lt_const hδ] with i hi
  intro s e hse hs q hq hr
  by_contra hsmall
  have he : e + 1 ≤ s + n := by omega
  exact hr (nativePrefixFeasible_mono_end (hfit (h i) (hh i) hi s hs q hq) he)

end SwingRepair
