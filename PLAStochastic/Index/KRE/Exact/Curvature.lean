import PLAStochastic.Index.KRE.Uniform.LayerBounds
import PLAStochastic.Index.KRE.Uniform.CurvaturePhase

/-!
# Exact stopping and logarithmic recursion in a curvature layer

These lemmas concern the actual rank-promotion algorithm.  The small-layer
lemma proves that the whole input is feasible, rather than merely bounding
the number of output segments by a constant.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory

/-- A whole curved layer is feasible once its size in reference units is
small compared with the tolerance. -/
theorem kre_exact_small_layer {c : DensityClassParams} {n : ℕ} {eps : ℝ}
    {f : ℝ → ℝ} {ω : ℕ → ℝ} (hf : c.Mem 1 f) (hc : UnifCond c n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n))
    (hbig : 102400 * Real.log n ≤ (n : ℝ)) {ℓ : ℕ}
    (h2 : 2 ≤ reSize eps (renyiKeys f n ω) n ℓ)
    (hs : (1 + 24 * unifKappa c) * ((n : ℝ) /
      reDelta eps (renyiKeys f n ω) n ℓ) ≤ eps) :
    reSize eps (renyiKeys f n ω) n (ℓ + 1) = 1 := by
  have he := hc.one_le_eps
  have hn := hc.one_le
  have hY := hc.one_le_log
  have hD : effDelta n (1 : ℝ) = 1 := max_eq_left (by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hn'))
  have H := krePath_unif hf hc.n_ge hω
  rw [hD] at H
  simp only [one_mul] at H
  have HC := H.curvedLattice he hn ℓ
  let p := renyiKeys f n ω
  let Δ := reDelta eps p n ℓ
  let K := reSize eps p n ℓ
  let Y := Real.log n
  let s := (n : ℝ) / Δ
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hΔ : (0 : ℝ) < Δ := reDelta_pos he hn ℓ
  have hΔn : (Δ : ℝ) < n := by exact_mod_cast reDelta_lt he hn h2
  have hK1 : 1 ≤ K := one_le_reSize he hn ℓ
  have hs0 : 0 < s := div_pos hN hΔ
  have hsΔ : s * Δ = n := div_mul_cancel₀ _ hΔ.ne'
  have hcov : ((K : ℝ) - 1) * Δ < n := by
    have h := (re_cover (p := p) he hn ℓ).1
    have hr : ((K - 1 : ℕ) : ℝ) * Δ < n := by exact_mod_cast h
    rwa [Nat.cast_sub hK1, Nat.cast_one] at hr
  have hKD : (K : ℝ) * Δ ≤ 2 * n := by nlinarith
  have hK : (K : ℝ) ≤ 2 * s := by
    have hs1 : 1 ≤ s := (le_div_iff₀ hΔ).2 (by simpa using hΔn.le)
    have hlt : (K : ℝ) - 1 < s := by
      exact lt_of_mul_lt_mul_right (by rw [hsΔ]; exact hcov) hΔ.le
    linarith
  let x := 80 * (Real.sqrt ((K : ℝ) * Δ * Y) + Y)
  have hY0 : 0 ≤ Y := by dsimp [Y]; linarith
  have hYn : Y ≤ (n : ℝ) := by dsimp [Y]; linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxN : x ≤ (n : ℝ) := by
    have hsq : Real.sqrt (2 * (n : ℝ) * Y) ≤ n / 160 := by
      rw [Real.sqrt_le_left (by positivity)]
      dsimp [Y] at *
      nlinarith
    have hsq' := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hKD hY0)
    dsimp [x, Y] at *
    linarith
  have hxS : x / Δ ≤ s := (div_le_div_of_nonneg_right hxN hΔ.le)
  have hκ := (unifKappa_pos c).le
  have hL : 0 ≤ c.L / c.fmin ^ 3 / (2 * (1 / c.fmax)) := by
    have := c.L_pos
    have := c.fmin_pos
    have : 0 < c.fmax := lt_of_lt_of_le one_pos c.one_le_fmax
    positivity
  have hκeq : (c.L / c.fmin ^ 3 / (2 * (1 / c.fmax))) * 80 = unifKappa c := by
    simpa only [one_mul, kreLam] using (show kreLam (1 * c.L / c.fmin ^ 3) (1 / c.fmax) = 1 * unifKappa c from kreLam_unif c 1)
  have hcost : x / Δ + ((K : ℝ) + 2 * (x / Δ)) *
      (c.L / c.fmin ^ 3 / (2 * (1 / c.fmax))) *
      (80 * ((K : ℝ) * Δ + Real.log n)) / ((n : ℝ) / 2) ≤ eps := by
    have hnum : ((K : ℝ) + 2 * (x / Δ)) *
        (c.L / c.fmin ^ 3 / (2 * (1 / c.fmax))) *
        (80 * ((K : ℝ) * Δ + Real.log n)) ≤ 12 * s * unifKappa c * n := by
      calc
        _ ≤ (4 * s) * (c.L / c.fmin ^ 3 / (2 * (1 / c.fmax))) * (80 * (3 * n)) := by
          gcongr <;> linarith
        _ = 12 * s * unifKappa c * n := by rw [← hκeq]; ring
    have hdiv : ((K : ℝ) + 2 * (x / Δ)) *
        (c.L / c.fmin ^ 3 / (2 * (1 / c.fmax))) *
        (80 * ((K : ℝ) * Δ + Real.log n)) / ((n : ℝ) / 2) ≤ 24 * s * unifKappa c := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hnum]
    change (1 + 24 * unifKappa c) * s ≤ eps at hs
    nlinarith
  have hfeas := HC.curved_short_feasible H.tube (τb := K) (x := x) le_rfl hcost
    0 K (by simp only [zero_add]; unfold K p renyiKeys; exact le_rfl) le_rfl
  change prefixAffineFeasible eps (shiftSeq (fun j => p (j * Δ)) 0) K at hfeas
  have hM : reSegs eps p n ℓ = 1 := by
    change finSegCount eps (fun j => p (j * Δ)) K = 1
    refine le_antisymm ?_ (one_le_finSegCount _ hK1)
    apply finSegCount_le_of_partition (m := 1) (c := fun i => i * K)
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      simpa using (show 0 < K by omega)
    · intro i hi
      obtain rfl : i = 0 := by omega
      simpa only [windowFeasible, zero_mul, zero_add, one_mul, Nat.sub_zero] using hfeas
  exact reSize_succ_eq_one_of_reSegs he hn hM

/-- On a sufficiently large curvature layer the actual next layer remains
nontrivial and its logarithmic size follows the halving recursion. -/
theorem kre_exact_curvature_step {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    {cN CN Cu C0 c1 c2 c3 KL c G C : ℝ}
    (hF : UniformLayerFacts p n eps 1 cN CN Cu C0 c1 c2 c3 KL)
    (he : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n)
    (hc : 0 < c) (h1 : c ≤ c1) (h2 : c ≤ c2) (h3 : c ≤ c3)
    (hCu : 0 < Cu) (hC0 : 0 ≤ C0) (hG : 2 * (Cu + C0) ≤ G)
    (hC : 1 ≤ C) (hCc : 16 ≤ c ^ 2 * C) (hCK : KL ≤ C)
    {ℓ : ℕ} (hN : 2 ≤ reSize eps p n ℓ) (hcurv : UCurv eps p n 1 ℓ)
    (hΔ : Real.log n ^ 2 ≤ (reDelta eps p n ℓ : ℝ))
    (hs : C * eps ≤ (n : ℝ) / reDelta eps p n ℓ) :
    2 ≤ reSize eps p n (ℓ + 1) ∧
      Real.log (c / 2) ≤ Real.log (eps * ((n : ℝ) / reDelta eps p n (ℓ + 1))) -
        Real.log (eps * ((n : ℝ) / reDelta eps p n ℓ)) / 2 ∧
      Real.log (eps * ((n : ℝ) / reDelta eps p n (ℓ + 1))) -
        Real.log (eps * ((n : ℝ) / reDelta eps p n ℓ)) / 2 ≤ Real.log G := by
  have he0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hD : effDelta n (1 : ℝ) = 1 := max_eq_left (by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hn'))
  have hsK : KL ≤ (n : ℝ) / reDelta eps p n ℓ := by nlinarith
  have hlo := curvLow_layer hF he hn hY one_pos le_rfl hD hc.le h1 h2 h3 hN hcurv hΔ hsK
  simp only [one_mul] at hlo
  let s := (n : ℝ) / reDelta eps p n ℓ
  let s' := (n : ℝ) / reDelta eps p n (ℓ + 1)
  have hΔ0 := reDelta_pos (p := p) he hn ℓ
  have hs0 : 0 < s := div_pos hn0 hΔ0
  have hs'0 : 0 < s' := div_pos hn0 (reDelta_pos he hn (ℓ + 1))
  have hsq : 4 ≤ c * Real.sqrt (s / eps) := by
    have hsC : C ≤ s / eps := (le_div_iff₀ he0).2 hs
    have hpow := Real.sq_sqrt (div_nonneg hs0.le he0.le)
    have hcc : 16 ≤ c ^ 2 * (s / eps) := hCc.trans
      (mul_le_mul_of_nonneg_left hsC (sq_nonneg _))
    have heq : (c * Real.sqrt (s / eps)) ^ 2 = c ^ 2 * (s / eps) := by
      rw [mul_pow, hpow]
    nlinarith [mul_nonneg hc.le (Real.sqrt_nonneg (s / eps))]
  have hM : 2 ≤ reSegs eps p n ℓ := by
    have : (4 : ℝ) ≤ reSegs eps p n ℓ := hsq.trans hlo
    exact_mod_cast (show (2 : ℝ) ≤ reSegs eps p n ℓ by linarith)
  have hslo : c / 2 * Real.sqrt (s / eps) ≤ s' := by
    have hsm := reSegs_sub_one_lt (p := p) he hn (ℓ := ℓ)
    have hmr : (2 : ℝ) ≤ reSegs eps p n ℓ := by exact_mod_cast hM
    dsimp [s']
    nlinarith
  have hsup : s' ≤ G * Real.sqrt (s / eps) := by
    have hs1 : 1 ≤ s / eps := hC.trans ((le_div_iff₀ he0).2 hs)
    have hsq1 : 1 ≤ Real.sqrt (s / eps) := Real.one_le_sqrt.2 hs1
    have hup := hF.curvUp ℓ hN hcurv
    rw [hD, one_mul] at hup
    have hmup := div_reDelta_succ_le (p := p) he hn ℓ
    have hGsq := mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg (s / eps))
    have hC0sq := le_mul_of_one_le_right hC0 hsq1
    change s' ≤ G * Real.sqrt (s / eps)
    nlinarith
  have hlog : Real.log (Real.sqrt (s / eps)) = (Real.log s - Real.log eps) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_div hs0.ne' he0.ne']
  have hl := Real.log_le_log (by positivity : 0 < c / 2 * Real.sqrt (s / eps)) hslo
  have hu := Real.log_le_log hs'0 hsup
  rw [Real.log_mul (by positivity) (by positivity), hlog] at hl
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity : 0 < 2 * (Cu + C0)) hG
  rw [Real.log_mul hG0.ne' (by positivity), hlog] at hu
  refine ⟨hM.trans (reSize_succ_bounds (p := p) he hn ℓ).1, ?_, ?_⟩
  all_goals
    rw [Real.log_mul he0.ne' hs'0.ne', Real.log_mul he0.ne' hs0.ne']
    linarith

end
end PGM
