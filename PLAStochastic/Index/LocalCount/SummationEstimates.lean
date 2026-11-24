import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Elementary summation estimates for the local-count base case

Pure real-analysis estimates used by the local-count argument:

* `lattice_min_sum`: a nonnegative function on a finite set of naturals bounded by `A` and by
  `B / (t - x)^2` has total mass at most `2 A + 6 √(A B)`.
* `renewal_series_le`: `∑_{T ≥ 1} √T · min(1, T / (T - a)^2) / T ≤ 30`, uniformly in `a ∈ ℝ`
  (written with `T / max T ((T - a)^2)`, which is `min 1 (T/(T-a)^2)` with value `1` at `T = a`).
* `dyadic_min_summable`, `dyadic_min_sum_le`: the dyadic estimate
  `∑_j min(C₁ a 2^j, C₂ e^{-c 2^j}) ≤ (2 C₁ max 1 (1/c) + C₂) a log(e/a)` for `0 < a ≤ 1`.
* `early_local_kernel_le`: the early-local summation kernel
  `∑_{1 ≤ t ≤ E} t^{-3/2} min(e^{-cE/t}, min(1, t/(t-x)^2)) ≤ (100/c + 16/c^2)/E` for every
  `E > 0` and real `x` (three ranges `t < x/2`, `t > 2x`, `x/2 ≤ t ≤ 2x`; the last one by
  `lattice_min_sum`).
-/

namespace PGM

open Finset

private lemma lcbs_sum_min_inv_sq {T : Finset ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 0 ∉ T) :
    ∑ j ∈ T, min A (B / (j : ℝ) ^ 2) ≤ 3 * Real.sqrt (A * B) := by
  rcases hA.eq_or_lt with rfl | hA'
  · calc ∑ j ∈ T, min (0 : ℝ) (B / (j : ℝ) ^ 2) ≤ ∑ j ∈ T, (0 : ℝ) :=
          Finset.sum_le_sum (fun j _ => min_le_left _ _)
      _ = 0 := by simp
      _ ≤ 3 * Real.sqrt (0 * B) := by positivity
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA'
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  set s := Real.sqrt B / Real.sqrt A with hs
  set J := ⌊s⌋₊ with hJ
  have hJs : (J : ℝ) ≤ s := Nat.floor_le (by positivity)
  have hsJ : s < J + 1 := Nat.lt_floor_add_one s
  have hBs : Real.sqrt B = s * Real.sqrt A := by rw [hs]; field_simp
  have hAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
  have hBB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  rw [← Finset.sum_filter_add_sum_filter_not T (fun j => j ≤ J)]
  have h1 : ∑ j ∈ T with j ≤ J, min A (B / (j : ℝ) ^ 2) ≤ Real.sqrt (A * B) := by
    have hsub : T.filter (fun j => j ≤ J) ⊆ Finset.Icc 1 J := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_Icc]
      refine ⟨Nat.one_le_iff_ne_zero.2 ?_, hj.2⟩
      rintro rfl
      exact hT hj.1
    have hcard : ((T.filter (fun j => j ≤ J)).card : ℝ) ≤ J := by
      have := Finset.card_le_card hsub
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    calc ∑ j ∈ T with j ≤ J, min A (B / (j : ℝ) ^ 2) ≤ ∑ j ∈ T with j ≤ J, A :=
          Finset.sum_le_sum (fun j _ => min_le_left _ _)
      _ = (T.filter (fun j => j ≤ J)).card * A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ J * A := by gcongr
      _ ≤ s * A := by gcongr
      _ = Real.sqrt (A * B) := by
          rw [hAB, hBs]; linear_combination (-s) * hAA
  have h2 : ∑ j ∈ T with ¬ j ≤ J, min A (B / (j : ℝ) ^ 2) ≤ 2 * Real.sqrt (A * B) := by
    set M := T.sup id + 1
    have hsub : T.filter (fun j => ¬ j ≤ J) ⊆ Finset.Ioo J M := by
      intro j hj
      simp only [Finset.mem_filter, not_le] at hj
      simp only [Finset.mem_Ioo]
      refine ⟨hj.2, Nat.lt_succ_of_le ?_⟩
      exact Finset.le_sup (f := id) hj.1
    calc ∑ j ∈ T with ¬ j ≤ J, min A (B / (j : ℝ) ^ 2)
        ≤ ∑ j ∈ T with ¬ j ≤ J, B * ((j : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum (fun j _ => (min_le_right _ _).trans (le_of_eq (div_eq_mul_inv _ _)))
      _ ≤ ∑ j ∈ Finset.Ioo J M, B * ((j : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ = B * ∑ j ∈ Finset.Ioo J M, ((j : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ B * (2 / (J + 1)) := by gcongr; exact sum_Ioo_inv_sq_le J M
      _ ≤ 2 * Real.sqrt (A * B) := by
          rw [hAB, mul_div_assoc', div_le_iff₀ (by positivity)]
          have : Real.sqrt B ≤ (J + 1) * Real.sqrt A := by
            rw [hBs]; gcongr
          have := mul_le_mul_of_nonneg_left this hsB
          nlinarith
  linarith

private lemma lcbs_half {S : Finset ℕ} {f : ℕ → ℝ} {A B : ℝ} (φ : ℕ → ℕ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hφ : Set.InjOn φ S) (hfA : ∀ t ∈ S, f t ≤ A)
    (hfB : ∀ t ∈ S, f t * (φ t : ℝ) ^ 2 ≤ B) :
    ∑ t ∈ S, f t ≤ A + 3 * Real.sqrt (A * B) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun t => φ t = 0)]
  gcongr ?_ + ?_
  · have hcard : (S.filter (fun t => φ t = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact hφ ha.1 hb.1 (ha.2.trans hb.2.symm)
    calc ∑ t ∈ S with φ t = 0, f t ≤ ∑ t ∈ S with φ t = 0, A :=
          Finset.sum_le_sum (fun t ht => hfA t (Finset.mem_filter.1 ht).1)
      _ = (S.filter (fun t => φ t = 0)).card * A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * A := by gcongr; exact_mod_cast hcard
      _ = A := one_mul A
  · calc ∑ t ∈ S with ¬ φ t = 0, f t
        ≤ ∑ t ∈ S with ¬ φ t = 0, min A (B / (φ t : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨htS, ht0⟩ := Finset.mem_filter.1 ht
          have hpos : (0 : ℝ) < (φ t : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero ht0)) 2
          exact le_min (hfA t htS) ((le_div_iff₀ hpos).2 (hfB t htS))
      _ = ∑ j ∈ (S.filter (fun t => ¬ φ t = 0)).image φ, min A (B / (j : ℝ) ^ 2) := by
          rw [Finset.sum_image]
          exact hφ.mono (by intro t ht; exact (Finset.mem_filter.1 ht).1)
      _ ≤ 3 * Real.sqrt (A * B) := by
          apply lcbs_sum_min_inv_sq hA hB
          simp

/-- Lattice minimum sum (hypothesis form of `∑_t min(A, B/(t-x)^2) ≤ 2A + 6√(AB)`). -/
theorem lattice_min_sum {S : Finset ℕ} {f : ℕ → ℝ} {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hfA : ∀ t ∈ S, f t ≤ A)
    (hfB : ∀ t ∈ S, f t * ((t : ℝ) - x) ^ 2 ≤ B) :
    ∑ t ∈ S, f t ≤ 2 * A + 6 * Real.sqrt (A * B) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun t : ℕ => x ≤ (t : ℝ))]
  have h1 : ∑ t ∈ S.filter (fun t : ℕ => x ≤ (t : ℝ)), f t ≤ A + 3 * Real.sqrt (A * B) := by
    apply lcbs_half (fun t => t - ⌈x⌉₊) hA hB
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      have ha' : ⌈x⌉₊ ≤ a := Nat.ceil_le.2 ha.2
      have hb' : ⌈x⌉₊ ≤ b := Nat.ceil_le.2 hb.2
      simp only at hab
      omega
    · intro t ht
      exact hfA t (Finset.mem_filter.1 ht).1
    · intro t ht
      obtain ⟨htS, hxt⟩ := Finset.mem_filter.1 ht
      have hc : ⌈x⌉₊ ≤ t := Nat.ceil_le.2 hxt
      have hcast : ((t - ⌈x⌉₊ : ℕ) : ℝ) = t - ⌈x⌉₊ := Nat.cast_sub hc
      have hle : x ≤ ⌈x⌉₊ := Nat.le_ceil x
      have hc' : (⌈x⌉₊ : ℝ) ≤ t := by exact_mod_cast hc
      calc f t * ((t - ⌈x⌉₊ : ℕ) : ℝ) ^ 2 ≤ f t * ((t : ℝ) - x) ^ 2 := by
            rw [hcast]
            have hsq : ((t : ℝ) - ⌈x⌉₊) ^ 2 ≤ ((t : ℝ) - x) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_left hsq (hf0 t htS)
        _ ≤ B := hfB t htS
  have h2 : ∑ t ∈ S.filter (fun t : ℕ => ¬ x ≤ (t : ℝ)), f t ≤ A + 3 * Real.sqrt (A * B) := by
    apply lcbs_half (fun t => ⌈x⌉₊ - (1 + t)) hA hB
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, not_le] at ha hb
      have ha' : a < ⌈x⌉₊ := Nat.lt_ceil.2 ha.2
      have hb' : b < ⌈x⌉₊ := Nat.lt_ceil.2 hb.2
      simp only at hab
      omega
    · intro t ht
      exact hfA t (Finset.mem_filter.1 ht).1
    · intro t ht
      obtain ⟨htS, hxt⟩ := Finset.mem_filter.1 ht
      rw [not_le] at hxt
      have hc : 1 + t ≤ ⌈x⌉₊ := by have := Nat.lt_ceil.2 hxt; omega
      have hcast : ((⌈x⌉₊ - (1 + t) : ℕ) : ℝ) = ⌈x⌉₊ - (1 + t) := by
        rw [Nat.cast_sub hc]; push_cast; ring
      have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg t) hxt.le
      have hlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
      have hc' : (1 + t : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast hc
      calc f t * ((⌈x⌉₊ - (1 + t) : ℕ) : ℝ) ^ 2 ≤ f t * ((t : ℝ) - x) ^ 2 := by
            rw [hcast]
            have hsq : ((⌈x⌉₊ : ℝ) - (1 + t)) ^ 2 ≤ ((t : ℝ) - x) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_left hsq (hf0 t htS)
        _ ≤ B := hfB t htS
  linarith

private lemma lcbs_inv_sqrt_cube_step (n : ℕ) :
    ((Real.sqrt ((n : ℝ) + 2)) ^ 3)⁻¹ + 2 / Real.sqrt ((n : ℝ) + 2) ≤
      2 / Real.sqrt ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set p := Real.sqrt ((n : ℝ) + 1) with hp
  set q := Real.sqrt ((n : ℝ) + 2) with hq
  have hp2 : p ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hq2 : q ^ 2 = n + 2 := Real.sq_sqrt (by positivity)
  have hp1 : 1 ≤ p := by
    rw [hp, Real.one_le_sqrt]; linarith
  have hpq : p ≤ q := Real.sqrt_le_sqrt (by linarith)
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  rw [inv_eq_one_div, div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have key : 2 * (q ^ 3 * q) - (1 * q + q ^ 3 * 2) * p =
      q * (q - p) ^ 2 * (2 * q + p) + p * q * (q ^ 2 - p ^ 2 - 1) := by ring
  have h0 : q ^ 2 - p ^ 2 - 1 = 0 := by rw [hp2, hq2]; ring
  rw [h0, mul_zero, add_zero] at key
  have : 0 ≤ q * (q - p) ^ 2 * (2 * q + p) := by positivity
  linarith

private lemma lcbs_sum_inv_sqrt_cube_aux (n : ℕ) :
    ∑ t ∈ range (n + 1), ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ ≤
      3 - 2 / Real.sqrt ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := lcbs_inv_sqrt_cube_step n
    push_cast
    have e : (n : ℝ) + 1 + 1 = n + 2 := by ring
    rw [e]
    linarith

private lemma lcbs_sum_inv_sqrt_cube_le (N : ℕ) :
    ∑ t ∈ range N, ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ ≤ 3 := by
  rcases N with _ | n
  · simp
  · have := lcbs_sum_inv_sqrt_cube_aux n
    have : 0 ≤ 2 / Real.sqrt ((n : ℝ) + 1) := by positivity
    linarith

private lemma lcbs_renewal_far (a : ℝ) (t : ℕ) (h : 2 * a ≤ (t : ℝ) + 1) :
    Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) ≤
      4 * ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set T : ℝ := (t : ℝ) + 1 with hT
  have hT1 : 1 ≤ T := by linarith
  set σ := Real.sqrt T with hσ
  have hσ2 : σ ^ 2 = T := Real.sq_sqrt (by linarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith)
  have hM1 : T ≤ max T ((T - a) ^ 2) := le_max_left _ _
  have hM2 : (T - a) ^ 2 ≤ max T ((T - a) ^ 2) := le_max_right _ _
  have hM0 : 0 < max T ((T - a) ^ 2) := by linarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ hM0 (by positivity)]
  have h4 : T ^ 2 ≤ 4 * (T - a) ^ 2 := by nlinarith
  have : σ * σ ^ 3 = T ^ 2 := by rw [← hσ2]; ring
  nlinarith

private lemma lcbs_renewal_near_A (a : ℝ) (t : ℕ) (h : ¬ 2 * a ≤ (t : ℝ) + 1) :
    Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) ≤
      2 / Real.sqrt a := by
  rw [not_le] at h
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set T : ℝ := (t : ℝ) + 1 with hT
  have hT1 : 1 ≤ T := by linarith
  have ha : 0 < a := by linarith
  set σ := Real.sqrt T with hσ
  have hσ2 : σ ^ 2 = T := Real.sq_sqrt (by linarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith)
  set r := Real.sqrt a with hr
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  have hr0 : 0 < r := Real.sqrt_pos.2 ha
  have hM1 : T ≤ max T ((T - a) ^ 2) := le_max_left _ _
  have hM2 : (T - a) ^ 2 ≤ max T ((T - a) ^ 2) := le_max_right _ _
  have hM0 : 0 < max T ((T - a) ^ 2) := by linarith
  rw [div_le_div_iff₀ hM0 hr0]
  rcases le_or_gt (a / 2) T with hTa | hTa
  · -- `r ≤ 2 σ`
    have hr2σ : r ≤ 2 * σ := by nlinarith
    nlinarith
  · have hσr : σ ≤ r := by nlinarith
    have hr2' : 2 ≤ r ^ 2 := by linarith
    have hsq : r ^ 4 / 4 ≤ (T - a) ^ 2 := by nlinarith
    nlinarith

private lemma lcbs_renewal_near_B (a : ℝ) (t : ℕ) (h : ¬ 2 * a ≤ (t : ℝ) + 1) :
    Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) *
        ((t : ℝ) - (a - 1)) ^ 2 ≤ 2 * Real.sqrt a := by
  rw [not_le] at h
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have e : (t : ℝ) - (a - 1) = (t : ℝ) + 1 - a := by ring
  rw [e]
  set T : ℝ := (t : ℝ) + 1 with hT
  have hT1 : 1 ≤ T := by linarith
  have ha : 0 < a := by linarith
  set σ := Real.sqrt T with hσ
  have hσ2 : σ ^ 2 = T := Real.sq_sqrt (by linarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith)
  set r := Real.sqrt a with hr
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  have hr0 : 0 < r := Real.sqrt_pos.2 ha
  have hM1 : T ≤ max T ((T - a) ^ 2) := le_max_left _ _
  have hM2 : (T - a) ^ 2 ≤ max T ((T - a) ^ 2) := le_max_right _ _
  have hM0 : 0 < max T ((T - a) ^ 2) := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
  have hσr : σ ≤ 2 * r := by nlinarith
  have := mul_le_mul_of_nonneg_left hM2 hσ0.le
  have := mul_le_mul_of_nonneg_right hσr hM0.le
  nlinarith

/-- The renewal series, uniformly in the real shift `a`. -/
theorem renewal_series_le (a : ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range N, Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2)
      ≤ 30 := by
  rw [← Finset.sum_filter_add_sum_filter_not (range N) (fun t : ℕ => 2 * a ≤ (t : ℝ) + 1)]
  have h1 : ∑ t ∈ (range N).filter (fun t : ℕ => 2 * a ≤ (t : ℝ) + 1),
      Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) ≤ 12 := by
    calc _ ≤ ∑ t ∈ (range N).filter (fun t : ℕ => 2 * a ≤ (t : ℝ) + 1),
          4 * ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ :=
          Finset.sum_le_sum (fun t ht => lcbs_renewal_far a t (Finset.mem_filter.1 ht).2)
      _ ≤ ∑ t ∈ range N, 4 * ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = 4 * ∑ t ∈ range N, ((Real.sqrt ((t : ℝ) + 1)) ^ 3)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 4 * 3 := by gcongr; exact lcbs_sum_inv_sqrt_cube_le N
      _ = 12 := by norm_num
  have h2 : ∑ t ∈ (range N).filter (fun t : ℕ => ¬ 2 * a ≤ (t : ℝ) + 1),
      Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) ≤ 18 := by
    rcases le_or_gt a (1 / 2) with ha | ha
    · rw [Finset.sum_eq_zero]
      · norm_num
      · intro t ht
        have hP := (Finset.mem_filter.1 ht).2
        exfalso
        apply hP
        have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
        linarith
    · have hr0 : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
      have hr2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
      have hlat := lattice_min_sum (S := (range N).filter (fun t : ℕ => ¬ 2 * a ≤ (t : ℝ) + 1))
        (f := fun t : ℕ =>
          Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2))
        (x := a - 1) (A := 2 / Real.sqrt a) (B := 2 * Real.sqrt a) (by positivity) (by positivity)
        (fun t _ => by positivity)
        (fun t ht => lcbs_renewal_near_A a t (Finset.mem_filter.1 ht).2)
        (fun t ht => lcbs_renewal_near_B a t (Finset.mem_filter.1 ht).2)
      have hsq : Real.sqrt (2 / Real.sqrt a * (2 * Real.sqrt a)) = 2 := by
        rw [show 2 / Real.sqrt a * (2 * Real.sqrt a) = (2 : ℝ) ^ 2 by field_simp]
        exact Real.sqrt_sq (by norm_num)
      rw [hsq] at hlat
      have : 4 / Real.sqrt a ≤ 6 := by rw [div_le_iff₀ hr0]; nlinarith
      have e : 2 * (2 / Real.sqrt a) = 4 / Real.sqrt a := by ring
      linarith
  linarith

/-- Dyadic estimate (klc:eq:dyadic-sum): summability. -/
theorem dyadic_min_summable {C₁ C₂ c a : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc : 0 < c)
    (ha : 0 < a) :
    Summable (fun j : ℕ => min (C₁ * a * 2 ^ j) (C₂ * Real.exp (-(c * 2 ^ j)))) := by
  have hg : Summable (fun j : ℕ => C₂ * Real.exp (-c) ^ j) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left C₂
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
  · exact le_min (by positivity) (by positivity)
  · refine (min_le_right _ _).trans ?_
    rw [← Real.exp_nat_mul]
    gcongr
    have : (j : ℝ) ≤ 2 ^ j := by exact_mod_cast j.lt_two_pow_self.le
    nlinarith

/-- Dyadic estimate (klc:eq:dyadic-sum). -/
theorem dyadic_min_sum_le {C₁ C₂ c a : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∑' j : ℕ, min (C₁ * a * 2 ^ j) (C₂ * Real.exp (-(c * 2 ^ j))) ≤
      (2 * C₁ * max 1 (1 / c) + C₂) * a * Real.log (Real.exp 1 / a) := by
  have hs := dyadic_min_summable hC₁ hC₂ hc ha
  set L := Real.log (Real.exp 1 / a) with hLdef
  have hL : L = 1 - Real.log a := by
    rw [hLdef, Real.log_div (Real.exp_pos 1).ne' ha.ne', Real.log_exp]
  have hL1 : 1 ≤ L := by rw [hL]; linarith [Real.log_nonpos ha.le ha1]
  have hex : ∃ j : ℕ, L / c ≤ 2 ^ j :=
    (pow_unbounded_of_one_lt (L / c) (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le
  classical
  set j₀ := Nat.find hex with hj₀def
  have hj₀ : L / c ≤ 2 ^ j₀ := Nat.find_spec hex
  rw [← hs.sum_add_tsum_nat_add j₀]
  have hhead : ∑ i ∈ range j₀, min (C₁ * a * 2 ^ i) (C₂ * Real.exp (-(c * 2 ^ i))) ≤
      2 * C₁ * a * (L / c) := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · rw [h0, Finset.range_zero, Finset.sum_empty]
      have : 0 ≤ L / c := by positivity
      positivity
    · have hlt : (2 : ℝ) ^ (j₀ - 1) < L / c := by
        exact not_le.1 (Nat.find_min hex (Nat.sub_lt hpos one_pos))
      have h2 : (2 : ℝ) ^ j₀ = 2 * 2 ^ (j₀ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      calc ∑ i ∈ range j₀, min (C₁ * a * 2 ^ i) (C₂ * Real.exp (-(c * 2 ^ i)))
          ≤ ∑ i ∈ range j₀, C₁ * a * (2 : ℝ) ^ i :=
            Finset.sum_le_sum (fun i _ => min_le_left _ _)
        _ = C₁ * a * ∑ i ∈ range j₀, (2 : ℝ) ^ i := by rw [Finset.mul_sum]
        _ = C₁ * a * (2 ^ j₀ - 1) := by
            rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
            norm_num
        _ ≤ C₁ * a * 2 ^ j₀ := by
            have : 0 ≤ C₁ * a := by positivity
            nlinarith
        _ = 2 * C₁ * a * 2 ^ (j₀ - 1) := by rw [h2]; ring
        _ ≤ 2 * C₁ * a * (L / c) := by gcongr
  have htail : ∑' i : ℕ, min (C₁ * a * 2 ^ (i + j₀)) (C₂ * Real.exp (-(c * 2 ^ (i + j₀)))) ≤
      C₂ * a := by
    have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have hgeom : Summable (fun i : ℕ => C₂ * (a / Real.exp 1) * Real.exp (-1) ^ i) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le he1).mul_left _
    have hcj : L ≤ c * 2 ^ j₀ := by
      rw [div_le_iff₀ hc] at hj₀
      linarith
    calc ∑' i : ℕ, min (C₁ * a * 2 ^ (i + j₀)) (C₂ * Real.exp (-(c * 2 ^ (i + j₀))))
        ≤ ∑' i : ℕ, C₂ * (a / Real.exp 1) * Real.exp (-1) ^ i := by
          refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff j₀).2 hs) hgeom
          refine (min_le_right _ _).trans ?_
          rw [mul_assoc]
          gcongr
          have hi : (i : ℝ) + 1 ≤ 2 ^ i := by exact_mod_cast i.lt_two_pow_self
          have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
          calc Real.exp (-(c * 2 ^ (i + j₀))) ≤ Real.exp (Real.log a - 1 - i) := by
                apply Real.exp_le_exp.2
                have e : c * (2 : ℝ) ^ (i + j₀) = (c * 2 ^ j₀) * 2 ^ i := by ring
                rw [e]
                have h1 : L * ((i : ℝ) + 1) ≤ (c * 2 ^ j₀) * 2 ^ i := by
                  have : 0 ≤ c * (2 : ℝ) ^ j₀ := by positivity
                  nlinarith
                nlinarith
            _ = a / Real.exp 1 * Real.exp (-1) ^ i := by
                rw [← Real.exp_nat_mul, sub_eq_add_neg (Real.log a - 1), Real.exp_add,
                  Real.exp_sub, Real.exp_log ha]
                ring_nf
      _ = C₂ * (a / Real.exp 1) * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le he1]
      _ ≤ C₂ * a := by
          rw [mul_assoc]
          gcongr
          have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
          have hx : a / Real.exp 1 * (1 - Real.exp (-1))⁻¹ = a / (Real.exp 1 - 1) := by
            rw [Real.exp_neg]
            have : Real.exp 1 - 1 ≠ 0 := by linarith
            field_simp
          rw [hx]
          exact div_le_self ha.le (by linarith)
  have h1 : 2 * C₁ * a * (L / c) ≤ 2 * C₁ * max 1 (1 / c) * a * L := by
    have : L / c ≤ max 1 (1 / c) * L := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    calc 2 * C₁ * a * (L / c) ≤ 2 * C₁ * a * (max 1 (1 / c) * L) := by gcongr
      _ = 2 * C₁ * max 1 (1 / c) * a * L := by ring
  have h2 : C₂ * a ≤ C₂ * a * L := le_mul_of_one_le_right (by positivity) hL1
  have e : (2 * C₁ * max 1 (1 / c) + C₂) * a * L =
      2 * C₁ * max 1 (1 / c) * a * L + C₂ * a * L := by ring
  rw [e]
  linarith

/-! ## The early-local summation kernel -/

private lemma lcbs_exp_neg_le_inv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hy (by linarith [Real.add_one_le_exp y])

private lemma lcbs_exp_neg_le_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  have := Real.quadratic_le_exp_of_nonneg hy.le
  nlinarith

private lemma lcbs_min_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a ^ 2) b ≤ a * Real.sqrt b := by
  rcases le_total (a ^ 2) b with h | h
  · rw [min_eq_left h]
    have : a ≤ Real.sqrt b := Real.le_sqrt_of_sq_le h
    nlinarith
  · rw [min_eq_right h]
    have : Real.sqrt b ≤ a := Real.sqrt_le_iff.2 ⟨ha, h⟩
    have hs := Real.mul_self_sqrt hb
    nlinarith [Real.sqrt_nonneg b]

private lemma lcbs_rpow_three_halves {t : ℝ} (ht : 0 < t) :
    (t ^ (3 / 2 : ℝ))⁻¹ = 1 / (t * Real.sqrt t) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    Real.sqrt_eq_rpow]
  exact (one_div _).symm

private lemma lcbs_exp_sq (y : ℝ) : Real.exp (-y) = Real.exp (-(y / 2)) ^ 2 := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Range `t < x/2` of the early-local kernel. -/
private lemma lcbs_kernel_left {c E x t : ℝ} (hc : 0 < c) (hE : 0 < E) (ht : 1 ≤ t)
    (htx : t < x / 2) :
    1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) ≤
      4 / (c * x * E) := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set w := Real.exp (-(c * E / t / 2)) with hw
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hv : t / max t ((t - x) ^ 2) ≤ 4 * t / x ^ 2 := by
    have h1 : x ^ 2 / 4 ≤ max t ((t - x) ^ 2) := le_max_of_le_right (by nlinarith)
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h1) (by positivity)]
    nlinarith
  have hv0 : 0 ≤ t / max t ((t - x) ^ 2) := div_nonneg ht0.le (le_max_of_le_left ht0.le)
  have hmin : min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) ≤
      w * (2 * Real.sqrt t / x) := by
    rw [lcbs_exp_sq]
    refine (lcbs_min_sq_le hw0 hv0).trans (mul_le_mul_of_nonneg_left ?_ hw0)
    calc Real.sqrt (t / max t ((t - x) ^ 2)) ≤ Real.sqrt (4 * t / x ^ 2) :=
          Real.sqrt_le_sqrt hv
      _ = 2 * Real.sqrt t / x := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num),
            Real.sqrt_sq hx0.le, show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hwle : w ≤ 2 * t / (c * E) := by
    have := lcbs_exp_neg_le_inv (show 0 < c * E / t / 2 by positivity)
    calc w ≤ 1 / (c * E / t / 2) := this
      _ = 2 * t / (c * E) := by field_simp
  calc 1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2))
      ≤ 1 / (t * Real.sqrt t) * (w * (2 * Real.sqrt t / x)) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = 2 * w / (t * x) := by field_simp
    _ ≤ 2 * (2 * t / (c * E)) / (t * x) := by gcongr
    _ = 4 / (c * x * E) := by field_simp; ring

/-- Range `t > 2x` of the early-local kernel. -/
private lemma lcbs_kernel_right {c E x t : ℝ} (hc : 0 < c) (hE : 0 < E) (ht : 1 ≤ t)
    (htx : 2 * x < t) :
    1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) ≤
      16 / (c ^ 2 * E ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set w := Real.exp (-(c * E / t / 2)) with hw
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hv : t / max t ((t - x) ^ 2) ≤ 4 / t := by
    have h1 : t ^ 2 / 4 ≤ max t ((t - x) ^ 2) := le_max_of_le_right (by nlinarith)
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h1) ht0]
    nlinarith
  have hv0 : 0 ≤ t / max t ((t - x) ^ 2) := div_nonneg ht0.le (le_max_of_le_left ht0.le)
  have hmin : min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) ≤
      w * (2 / Real.sqrt t) := by
    rw [lcbs_exp_sq]
    refine (lcbs_min_sq_le hw0 hv0).trans (mul_le_mul_of_nonneg_left ?_ hw0)
    calc Real.sqrt (t / max t ((t - x) ^ 2)) ≤ Real.sqrt (4 / t) := Real.sqrt_le_sqrt hv
      _ = 2 / Real.sqrt t := by
          rw [Real.sqrt_div' _ ht0.le, show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hwle : w ≤ 8 * t ^ 2 / (c ^ 2 * E ^ 2) := by
    have := lcbs_exp_neg_le_sq (show 0 < c * E / t / 2 by positivity)
    calc w ≤ 2 / (c * E / t / 2) ^ 2 := this
      _ = 8 * t ^ 2 / (c ^ 2 * E ^ 2) := by field_simp; ring
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  calc 1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2))
      ≤ 1 / (t * Real.sqrt t) * (w * (2 / Real.sqrt t)) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = 2 * w / (t * (Real.sqrt t * Real.sqrt t)) := by field_simp
    _ = 2 * w / t ^ 2 := by rw [htt, pow_two]
    _ ≤ 2 * (8 * t ^ 2 / (c ^ 2 * E ^ 2)) / t ^ 2 := by gcongr
    _ = 16 / (c ^ 2 * E ^ 2) := by field_simp; ring

/-- Range `x/2 ≤ t ≤ 2x` of the early-local kernel: bounds in the form used by
`lattice_min_sum`, with `σ = √(2/x)` and `q = e^{-cE/(4x)}`. -/
private lemma lcbs_kernel_mid {c E x t : ℝ} (hc : 0 < c) (hE : 0 < E) (ht : 1 ≤ t)
    (htx1 : x / 2 ≤ t) (htx2 : t ≤ 2 * x) :
    1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) ≤
        Real.exp (-(c * E / (4 * x))) ^ 2 * Real.sqrt (2 / x) ^ 3 ∧
      1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) *
        (t - x) ^ 2 ≤ Real.sqrt (2 / x) := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set σ := Real.sqrt (2 / x) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = 2 / x := Real.sq_sqrt (by positivity)
  have hinvt : 1 / t ≤ σ ^ 2 := by
    rw [hσ2, div_le_div_iff₀ ht0 hx0]; linarith
  have hinvs : 1 / Real.sqrt t ≤ σ := by
    rw [← Real.sqrt_one, ← Real.sqrt_div' _ ht0.le, hσ]
    exact Real.sqrt_le_sqrt (by rw [← hσ2]; exact hinvt)
  have hpre : 1 / (t * Real.sqrt t) ≤ σ ^ 3 := by
    rw [show 1 / (t * Real.sqrt t) = 1 / t * (1 / Real.sqrt t) by field_simp,
      show σ ^ 3 = σ ^ 2 * σ by ring]
    exact mul_le_mul hinvt hinvs (by positivity) (by positivity)
  have hv0 : 0 ≤ t / max t ((t - x) ^ 2) := div_nonneg ht0.le (le_max_of_le_left ht0.le)
  have hF0 : 0 ≤ min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) :=
    le_min (Real.exp_pos _).le hv0
  constructor
  · have hA : Real.exp (-(c * E / t)) ≤ Real.exp (-(c * E / (4 * x))) ^ 2 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have : c * E / (2 * x) ≤ c * E / t :=
        div_le_div_of_nonneg_left (by positivity) ht0 htx2
      have e : ((2 : ℕ) : ℝ) * -(c * E / (4 * x)) = -(c * E / (2 * x)) := by
        push_cast; field_simp; ring
      rw [e]; linarith
    calc 1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2))
        ≤ σ ^ 3 * Real.exp (-(c * E / (4 * x))) ^ 2 :=
          mul_le_mul hpre ((min_le_left _ _).trans hA) hF0 (by positivity)
      _ = _ := by ring
  · have hFv : min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) * (t - x) ^ 2 ≤ t := by
      refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ (lt_max_of_lt_left ht0)]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) ht0.le
    calc 1 / (t * Real.sqrt t) * min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) *
          (t - x) ^ 2
        = 1 / (t * Real.sqrt t) *
            (min (Real.exp (-(c * E / t))) (t / max t ((t - x) ^ 2)) * (t - x) ^ 2) := by ring
      _ ≤ 1 / (t * Real.sqrt t) * t := mul_le_mul_of_nonneg_left hFv (by positivity)
      _ = 1 / Real.sqrt t := by field_simp
      _ ≤ σ := hinvs

/-- **Early-local summation kernel** (klc:eq:early-local-kernel): for `c > 0`, `E > 0` and
every real `x`,
`∑_{1 ≤ t ≤ E} t^{-3/2} min(e^{-cE/t}, 1, t/(t-x)²) ≤ (100/c + 16/c²)/E`, where
`min(1, t/(t-x)²)` (value `1` at `t = x`) is written `t / max t ((t - x)²)`. -/
theorem early_local_kernel_le {c : ℝ} (hc : 0 < c) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    ∑ t ∈ Finset.Icc 1 ⌊E⌋₊, ((t : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
        min (Real.exp (-(c * E / t))) ((t : ℝ) / max (t : ℝ) (((t : ℝ) - x) ^ 2)) ≤
      (100 / c + 16 / c ^ 2) / E := by
  set S := Finset.Icc 1 ⌊E⌋₊ with hSdef
  set f : ℕ → ℝ := fun t => 1 / ((t : ℝ) * Real.sqrt t) *
    min (Real.exp (-(c * E / t))) ((t : ℝ) / max (t : ℝ) (((t : ℝ) - x) ^ 2)) with hfdef
  have hS : ∀ t ∈ S, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ E := fun t ht => by
    rw [hSdef, Finset.mem_Icc] at ht
    exact ⟨by exact_mod_cast ht.1, (Nat.cast_le.2 ht.2).trans (Nat.floor_le hE.le)⟩
  have hf0 : ∀ t ∈ S, 0 ≤ f t := fun t ht => by
    have ht0 : (0 : ℝ) < t := by linarith [(hS t ht).1]
    exact mul_nonneg (by positivity) (le_min (Real.exp_pos _).le
      (div_nonneg ht0.le (le_max_of_le_left ht0.le)))
  rw [Finset.sum_congr rfl (g := f) (fun t ht => by
    rw [lcbs_rpow_three_halves (by linarith [(hS t ht).1])])]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun t : ℕ => (t : ℝ) < x / 2),
    ← Finset.sum_filter_add_sum_filter_not (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2)
      (fun t : ℕ => 2 * x < (t : ℝ))]
  -- `t < x/2`
  have h1 : ∑ t ∈ S.filter (fun t : ℕ => (t : ℝ) < x / 2), f t ≤ 2 / (c * E) := by
    rcases (S.filter fun t : ℕ => (t : ℝ) < x / 2).eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
    · rw [he, Finset.sum_empty]; positivity
    · obtain ⟨ht₀S, ht₀x⟩ := Finset.mem_filter.1 ht₀
      have hx2 : 2 < x := by linarith [(hS t₀ ht₀S).1]
      have hcard : ((S.filter fun t : ℕ => (t : ℝ) < x / 2).card : ℝ) ≤ x / 2 := by
        have hsub : S.filter (fun t : ℕ => (t : ℝ) < x / 2) ⊆ Finset.Icc 1 ⌊x / 2⌋₊ := by
          intro t ht
          obtain ⟨htS, htx⟩ := Finset.mem_filter.1 ht
          rw [hSdef, Finset.mem_Icc] at htS
          rw [Finset.mem_Icc]
          exact ⟨htS.1, Nat.le_floor htx.le⟩
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc, Nat.add_sub_cancel] at this
        calc ((S.filter fun t : ℕ => (t : ℝ) < x / 2).card : ℝ) ≤ (⌊x / 2⌋₊ : ℝ) := by
              exact_mod_cast this
          _ ≤ x / 2 := Nat.floor_le (by linarith)
      calc ∑ t ∈ S.filter (fun t : ℕ => (t : ℝ) < x / 2), f t
          ≤ ∑ t ∈ S.filter (fun t : ℕ => (t : ℝ) < x / 2), 4 / (c * x * E) :=
            Finset.sum_le_sum fun t ht => by
              obtain ⟨htS, htx⟩ := Finset.mem_filter.1 ht
              exact lcbs_kernel_left hc hE (hS t htS).1 htx
        _ = ((S.filter fun t : ℕ => (t : ℝ) < x / 2).card : ℝ) * (4 / (c * x * E)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ x / 2 * (4 / (c * x * E)) := by gcongr
        _ = 2 / (c * E) := by field_simp; ring
  -- `t > 2x`
  have h2 : ∑ t ∈ (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
      (fun t : ℕ => 2 * x < (t : ℝ)), f t ≤ 16 / (c ^ 2 * E) := by
    have hcard : (((S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
        (fun t : ℕ => 2 * x < (t : ℝ))).card : ℝ) ≤ E := by
      have h := (Finset.card_le_card ((Finset.filter_subset (fun t : ℕ => 2 * x < (t : ℝ)) _).trans
        (Finset.filter_subset (fun t : ℕ => ¬ (t : ℝ) < x / 2) S)))
      rw [hSdef, Nat.card_Icc, Nat.add_sub_cancel] at h
      calc (((S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
            (fun t : ℕ => 2 * x < (t : ℝ))).card : ℝ) ≤ (⌊E⌋₊ : ℝ) := by exact_mod_cast h
        _ ≤ E := Nat.floor_le hE.le
    calc ∑ t ∈ (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
          (fun t : ℕ => 2 * x < (t : ℝ)), f t
        ≤ ∑ t ∈ (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
          (fun t : ℕ => 2 * x < (t : ℝ)), 16 / (c ^ 2 * E ^ 2) :=
          Finset.sum_le_sum fun t ht => by
            obtain ⟨ht', htx⟩ := Finset.mem_filter.1 ht
            exact lcbs_kernel_right hc hE (hS t (Finset.mem_filter.1 ht').1).1 htx
      _ = (((S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
            (fun t : ℕ => 2 * x < (t : ℝ))).card : ℝ) * (16 / (c ^ 2 * E ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ E * (16 / (c ^ 2 * E ^ 2)) := by gcongr
      _ = 16 / (c ^ 2 * E) := by field_simp
  -- `x/2 ≤ t ≤ 2x`
  have h3 : ∑ t ∈ (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
      (fun t : ℕ => ¬ 2 * x < (t : ℝ)), f t ≤ 80 / (c * E) := by
    set S3 := (S.filter fun t : ℕ => ¬ (t : ℝ) < x / 2).filter
      (fun t : ℕ => ¬ 2 * x < (t : ℝ)) with hS3
    have hmem : ∀ t ∈ S3, t ∈ S ∧ x / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2 * x := fun t ht => by
      obtain ⟨ht', htx2⟩ := Finset.mem_filter.1 ht
      obtain ⟨htS, htx1⟩ := Finset.mem_filter.1 ht'
      exact ⟨htS, not_lt.1 htx1, not_lt.1 htx2⟩
    rcases S3.eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
    · rw [he, Finset.sum_empty]; positivity
    · obtain ⟨ht₀S, -, ht₀x⟩ := hmem t₀ ht₀
      have hx : 1 / 2 ≤ x := by linarith [(hS t₀ ht₀S).1]
      have hx0 : 0 < x := by linarith
      set σ := Real.sqrt (2 / x) with hσ
      set q := Real.exp (-(c * E / (4 * x))) with hq
      have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
      have hσ2 : σ ^ 2 = 2 / x := Real.sq_sqrt (by positivity)
      have hσle : σ ≤ 2 :=
        Real.sqrt_le_iff.2 ⟨by norm_num, by rw [div_le_iff₀ hx0]; linarith⟩
      have hq0 : 0 < q := Real.exp_pos _
      have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 < c * E / (4 * x) := by positivity
        linarith)
      have hqle : q ≤ 4 * x / (c * E) := by
        have := lcbs_exp_neg_le_inv (show 0 < c * E / (4 * x) by positivity)
        calc q ≤ 1 / (c * E / (4 * x)) := this
          _ = 4 * x / (c * E) := by field_simp
      have hlat := lattice_min_sum (S := S3) (f := f) (x := x) (A := q ^ 2 * σ ^ 3) (B := σ)
        (by positivity) hσ0 (fun t ht => hf0 t (hmem t ht).1)
        (fun t ht => (lcbs_kernel_mid hc hE (hS t (hmem t ht).1).1 (hmem t ht).2.1
          (hmem t ht).2.2).1)
        (fun t ht => (lcbs_kernel_mid hc hE (hS t (hmem t ht).1).1 (hmem t ht).2.1
          (hmem t ht).2.2).2)
      have hsq : Real.sqrt (q ^ 2 * σ ^ 3 * σ) = q * σ ^ 2 := by
        rw [show q ^ 2 * σ ^ 3 * σ = (q * σ ^ 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [hsq] at hlat
      have hq2 : q ^ 2 * σ ^ 3 ≤ 2 * (q * σ ^ 2) := by
        have h1 : q ^ 2 ≤ q := by nlinarith
        have h2 : q ^ 2 * σ ^ 3 = q ^ 2 * σ * σ ^ 2 := by ring
        rw [h2]
        have h3 : q ^ 2 * σ ≤ q * 2 := mul_le_mul h1 hσle hσ0 hq0.le
        nlinarith [sq_nonneg σ]
      calc ∑ t ∈ S3, f t ≤ 2 * (q ^ 2 * σ ^ 3) + 6 * (q * σ ^ 2) := hlat
        _ ≤ 10 * (q * σ ^ 2) := by linarith
        _ = 20 * q / x := by rw [hσ2]; field_simp; ring
        _ ≤ 20 * (4 * x / (c * E)) / x := by gcongr
        _ = 80 / (c * E) := by field_simp; ring
  have e : (100 / c + 16 / c ^ 2) / E = 100 / (c * E) + 16 / (c ^ 2 * E) := by ring
  have h82 : 2 / (c * E) + 80 / (c * E) ≤ 100 / (c * E) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rw [e]
  linarith

end PGM
