import PLAStochastic.Index.CEPS.Output.Defs
import PLAStochastic.ForMathlib.Analysis.Fourier.DerivativeDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Track O: derivatives of the radial density along a ray

Fix a direction `w : Fin (k + 1) → ℝ` and put `F_j(s) = s^{k-j} · outRadial f j (s • w)`.
Then `F_0(s) = s^k ∏_l f(s w_l)` is the radial density along the ray (`rayF_zero`), and for
`j < r ≤ k` the derivative of `F_j` is `F_{j+1}` (`hasDerivAt_rayF`): this is
`smoothing.md` (S4)–(S6) for one fixed ray, proved by the one-variable product rule
`s ∂_s ∏_l h_l(s w_l) = ∑_l [h_l ↦ mellinOp h_l] - n ∏_l h_l(s w_l)` and the reindexing
`(l, c) ↦ Fin.cons l c` of insertion sequences.

With an envelope `|mellinOp^[a] f| ≤ E e^{-κ|x|}` (`a ≤ r`) and `w l₀ = 1`, every `F_j`,
`j ≤ r`, is integrable (`integrable_rayF`), so repeated integration by parts gives
`|β|^r |∫ e^{iβs} F_0(s) ds| ≤ ∫ |F_r|` (`norm_integral_rayF_le`).
-/

noncomputable section

open Finset Set MeasureTheory Filter

namespace PGM

variable {n : ℕ}

/-- The derivative of a monomial along the ray `s ↦ s • w`. -/
def outMonDeriv (f : ℝ → ℝ) (α : Fin n → ℕ) (w : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ l, (∏ l' ∈ univ.erase l, mellinOp^[α l'] f (s * w l')) *
    (deriv (mellinOp^[α l] f) (s * w l) * w l)

theorem hasDerivAt_outMon {f : ℝ → ℝ} {α : Fin n → ℕ}
    (hd : ∀ l, Differentiable ℝ (mellinOp^[α l] f)) (w : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s => outMon f α (s • w)) (outMonDeriv f α w s) s := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := univ) (x := s)
    (f := fun l s => mellinOp^[α l] f (s * w l))
    (f' := fun l => deriv (mellinOp^[α l] f) (s * w l) * w l) fun l _ => by
      have h1 : HasDerivAt (fun s => s * w l) (w l) s := by
        simpa using (hasDerivAt_id s).mul_const (w l)
      exact (hd l (s * w l)).hasDerivAt.comp s h1
  simpa [outMon, outMonDeriv, smul_eq_mul] using h

/-- `s ∂_s` of a monomial along a ray. -/
theorem mul_outMonDeriv (f : ℝ → ℝ) (α : Fin n → ℕ) (w : Fin n → ℝ) (s : ℝ) :
    s * outMonDeriv f α w s =
      ∑ l, outMon f (Function.update α l (α l + 1)) (s • w) - n * outMon f α (s • w) := by
  classical
  have hterm : ∀ l, s * ((∏ l' ∈ univ.erase l, mellinOp^[α l'] f (s * w l')) *
      (deriv (mellinOp^[α l] f) (s * w l) * w l)) =
      outMon f (Function.update α l (α l + 1)) (s • w) - outMon f α (s • w) := by
    intro l
    have hupd : outMon f (Function.update α l (α l + 1)) (s • w) =
        mellinOp^[α l + 1] f (s * w l) * ∏ l' ∈ univ.erase l, mellinOp^[α l'] f (s * w l') := by
      rw [outMon, ← Finset.mul_prod_erase univ _ (Finset.mem_univ l)]
      simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun l' hl' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl')]
    have hmon : outMon f α (s • w) =
        mellinOp^[α l] f (s * w l) * ∏ l' ∈ univ.erase l, mellinOp^[α l'] f (s * w l') := by
      rw [outMon, ← Finset.mul_prod_erase univ _ (Finset.mem_univ l)]
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hupd, hmon, Function.iterate_succ_apply', mellinOp_apply]
    ring
  rw [outMonDeriv, Finset.mul_sum]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem update_outCount {j : ℕ} (c : Fin j → Fin n) (l : Fin n) :
    Function.update (outCount c) l (outCount c l + 1) = outCount (Fin.cons l c : Fin (j + 1) → Fin n) := by
  funext l'
  rw [outCount_cons]
  by_cases h : l' = l
  · subst h; simp
  · rw [Function.update_of_ne h, if_neg (Ne.symm h), add_zero]

/-- The derivative of `outMonSum` along a ray. -/
def outMonSumDeriv (f : ℝ → ℝ) (i : ℕ) (w : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ c : Fin i → Fin n, outMonDeriv f (outCount c) w s

theorem hasDerivAt_outMonSum {f : ℝ → ℝ} {r : ℕ} (hd : ∀ a < r, Differentiable ℝ (mellinOp^[a] f))
    {i : ℕ} (hi : i < r) (w : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s => outMonSum f i (s • w)) (outMonSumDeriv f i w s) s := by
  have h := HasDerivAt.fun_sum (u := univ) (x := s)
    (A := fun c (s : ℝ) => outMon f (outCount c) (s • w))
    (A' := fun c => outMonDeriv f (outCount c) w s) fun c _ =>
      hasDerivAt_outMon (fun l => hd _ ((outCount_le c l).trans_lt hi)) w s
  simpa [outMonSum, outMonSumDeriv] using h

theorem mul_outMonSumDeriv (f : ℝ → ℝ) (i : ℕ) (w : Fin n → ℝ) (s : ℝ) :
    s * outMonSumDeriv f i w s = outMonSum f (i + 1) (s • w) - n * outMonSum f i (s • w) := by
  rw [outMonSumDeriv, Finset.mul_sum]
  simp_rw [mul_outMonDeriv, update_outCount]
  rw [Finset.sum_sub_distrib, outMonSum, outMonSum, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  rw [← (Fin.consEquiv fun _ : Fin (i + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The radial density and its derivatives along the ray `s ↦ s • w`. -/
def rayF (f : ℝ → ℝ) (k j : ℕ) (w : Fin (k + 1) → ℝ) (s : ℝ) : ℝ :=
  s ^ (k - j) * outRadial f j (s • w)

theorem rayF_zero (f : ℝ → ℝ) (k : ℕ) (w : Fin (k + 1) → ℝ) (s : ℝ) :
    rayF f k 0 w s = s ^ k * ∏ l, f (s * w l) := by
  simp [rayF, outRadial_zero]

/-- **The ray derivative chain**: `F_j' = F_{j+1}` for `j < r ≤ k`. -/
theorem hasDerivAt_rayF {f : ℝ → ℝ} {r k : ℕ} (hd : ∀ a < r, Differentiable ℝ (mellinOp^[a] f))
    (hrk : r ≤ k) {j : ℕ} (hj : j < r) (w : Fin (k + 1) → ℝ) (s : ℝ) :
    HasDerivAt (rayF f k j w) (rayF f k (j + 1) w s) s := by
  set G' : ℝ := ∑ i ∈ range (j + 1), outCoeff j i * outMonSumDeriv f i w s with hG'
  have hG : HasDerivAt (fun s => outRadial f j (s • w)) G' s := by
    have := HasDerivAt.fun_sum (u := range (j + 1)) (x := s)
      (A := fun i (s : ℝ) => outCoeff j i * outMonSum f i (s • w))
      (A' := fun i => outCoeff j i * outMonSumDeriv f i w s) fun i hi =>
        (hasDerivAt_outMonSum hd (by rw [Finset.mem_range] at hi; omega) w s).const_mul _
    simpa [outRadial, hG'] using this
  have hp : HasDerivAt (fun s : ℝ => s ^ (k - j)) ((k - j : ℕ) * s ^ (k - j - 1)) s := by
    simpa using hasDerivAt_pow (k - j) s
  have h := hp.fun_mul hG
  have hkj : k - j = (k - (j + 1)) + 1 := by omega
  have h' : HasDerivAt (rayF f k j w)
      (((k - j : ℕ) : ℝ) * s ^ (k - j - 1) * outRadial f j (s • w) + s ^ (k - j) * G') s := h
  refine h'.congr_deriv ?_
  have hsG : s * G' = ∑ i ∈ range (j + 1), outCoeff j i *
      (outMonSum f (i + 1) (s • w) - ((k : ℝ) + 1) * outMonSum f i (s • w)) := by
    rw [hG', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := mul_outMonSumDeriv f i w s
    push_cast at this
    rw [mul_left_comm, this]
  have hrec := outCoeff_succ_sum j (fun i => outMonSum f i (s • w))
  have hsplit : ∑ i ∈ range (j + 1), outCoeff j i *
      (outMonSum f (i + 1) (s • w) - ((k : ℝ) + 1) * outMonSum f i (s • w)) =
      ∑ i ∈ range (j + 1), outCoeff j i *
        (outMonSum f (i + 1) (s • w) - ((j : ℝ) + 1) * outMonSum f i (s • w)) -
      ((k - j : ℕ) : ℝ) * outRadial f j (s • w) := by
    rw [outRadial, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by
      rw [Nat.cast_sub (by omega)]
    rw [this]
    ring
  symm
  simp only [rayF]
  have e1 : k - j - 1 = k - (j + 1) := by omega
  have e2 : s ^ (k - j) = s ^ (k - (j + 1)) * s := by rw [hkj, pow_succ]
  rw [e1, e2]
  have e : ((k - j : ℕ) : ℝ) * s ^ (k - (j + 1)) * outRadial f j (s • w) +
      s ^ (k - (j + 1)) * s * G' =
      s ^ (k - (j + 1)) * (((k - j : ℕ) : ℝ) * outRadial f j (s • w) + s * G') := by ring
  rw [e, hsG, hsplit, hrec]
  simp only [outRadial]
  ring

/-! ## Envelopes and integrability -/

theorem abs_outMon_le {f : ℝ → ℝ} {E κ : ℝ} {α : Fin n → ℕ} (hE : 0 ≤ E)
    (henv : ∀ l, ∀ x, |mellinOp^[α l] f x| ≤ E * Real.exp (-κ * |x|)) (hκ : 0 ≤ κ)
    {w : Fin n → ℝ} {l₀ : Fin n} (hw : w l₀ = 1) (s : ℝ) :
    |outMon f α (s • w)| ≤ E ^ n * Real.exp (-κ * |s|) := by
  classical
  rw [outMon, Finset.abs_prod, ← Finset.mul_prod_erase univ _ (Finset.mem_univ l₀)]
  have h0 : |mellinOp^[α l₀] f ((s • w) l₀)| ≤ E * Real.exp (-κ * |s|) := by
    simpa [hw] using henv l₀ ((s • w) l₀)
  have h1 : ∏ l ∈ univ.erase l₀, |mellinOp^[α l] f ((s • w) l)| ≤ E ^ (n - 1) := by
    calc ∏ l ∈ univ.erase l₀, |mellinOp^[α l] f ((s • w) l)| ≤ ∏ _l ∈ univ.erase l₀, E :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l _ =>
            (henv l _).trans (mul_le_of_le_one_right hE (Real.exp_le_one_iff.mpr
              (by nlinarith [abs_nonneg ((s • w) l)])))
      _ = E ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  have hn : n = (n - 1) + 1 := by
    have : 0 < n := Fin.pos l₀
    omega
  calc |mellinOp^[α l₀] f ((s • w) l₀)| * ∏ l ∈ univ.erase l₀, |mellinOp^[α l] f ((s • w) l)|
      ≤ E * Real.exp (-κ * |s|) * E ^ (n - 1) :=
        mul_le_mul h0 h1 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = E ^ n * Real.exp (-κ * |s|) := by
        conv_rhs => rw [hn, pow_succ]
        ring

/-- The constant of the envelope of `outRadial`. -/
def outRadialConst (n j : ℕ) (E : ℝ) : ℝ :=
  ∑ i ∈ range (j + 1), |outCoeff j i| * ((n : ℝ) ^ i * E ^ n)

theorem abs_outRadial_le {f : ℝ → ℝ} {E κ : ℝ} {r : ℕ} (hE : 0 ≤ E) (hκ : 0 ≤ κ)
    (henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|))
    {j : ℕ} (hj : j ≤ r) {w : Fin n → ℝ} {l₀ : Fin n} (hw : w l₀ = 1) (s : ℝ) :
    |outRadial f j (s • w)| ≤ outRadialConst n j E * Real.exp (-κ * |s|) := by
  rw [outRadial, outRadialConst, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [outMonSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hi' : i ≤ r := by rw [Finset.mem_range] at hi; omega
  calc ∑ c : Fin i → Fin n, |outMon f (outCount c) (s • w)|
      ≤ ∑ _c : Fin i → Fin n, E ^ n * Real.exp (-κ * |s|) :=
        Finset.sum_le_sum fun c _ => abs_outMon_le hE
          (fun l => henv _ ((outCount_le c l).trans hi')) hκ hw s
    _ = (n : ℝ) ^ i * E ^ n * Real.exp (-κ * |s|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem outRadialConst_nonneg (n j : ℕ) {E : ℝ} (hE : 0 ≤ E) : 0 ≤ outRadialConst n j E :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_outRadial {f : ℝ → ℝ} {r : ℕ} (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f))
    {j : ℕ} (hj : j ≤ r) : Continuous (outRadial f j : (Fin n → ℝ) → ℝ) := by
  refine continuous_finsetSum _ fun i hi => continuous_const.mul ?_
  refine continuous_finsetSum _ fun c _ => ?_
  have hi' : i ≤ r := by rw [Finset.mem_range] at hi; omega
  exact continuous_finsetProd _ fun l _ =>
    (hc _ ((outCount_le c l).trans hi')).comp (continuous_apply l)

theorem rayF_eq_zero {f : ℝ → ℝ} (hf0 : ∀ x ≤ 0, f x = 0) {k j : ℕ} {w : Fin (k + 1) → ℝ}
    {l₀ : Fin (k + 1)} (hw : w l₀ = 1) {s : ℝ} (hs : s ≤ 0) : rayF f k j w s = 0 := by
  rw [rayF, outRadial_eq_zero hf0 j (l := l₀) (by simpa [hw] using hs), mul_zero]

/-- Every ray derivative `F_j`, `j ≤ r`, is integrable. -/
theorem integrable_rayF {f : ℝ → ℝ} {E κ : ℝ} {r k : ℕ} (hE : 0 ≤ E) (hκ : 0 < κ)
    (hf0 : ∀ x ≤ 0, f x = 0) (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f))
    (henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|))
    {j : ℕ} (hj : j ≤ r) {w : Fin (k + 1) → ℝ} {l₀ : Fin (k + 1)} (hw : w l₀ = 1) :
    Integrable (rayF f k j w) := by
  have hcont : Continuous (rayF f k j w) :=
    (continuous_pow _).mul ((continuous_outRadial hc hj).comp (continuous_id.smul continuous_const))
  set g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun s =>
    outRadialConst (k + 1) j E * (s ^ ((k - j : ℕ) : ℝ) * Real.exp (-κ * s ^ (1 : ℝ))) with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have : (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) one_pos hκ).const_mul _
  refine hgi.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, hg]
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), Real.rpow_natCast, Real.rpow_one,
      rayF, abs_mul, abs_pow, abs_of_pos hs]
    have := abs_outRadial_le hE hκ.le henv hj hw s
    rw [abs_of_pos hs] at this
    calc s ^ (k - j) * |outRadial f j (s • w)|
        ≤ s ^ (k - j) * (outRadialConst (k + 1) j E * Real.exp (-κ * s)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), rayF_eq_zero hf0 hw (not_lt.mp hs),
      abs_zero]

/-- **Repeated integration by parts along a ray.** -/
theorem norm_integral_rayF_le {f : ℝ → ℝ} {E κ : ℝ} {r k : ℕ} (hE : 0 ≤ E) (hκ : 0 < κ)
    (hrk : r ≤ k) (hf0 : ∀ x ≤ 0, f x = 0) (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f))
    (hd : ∀ a < r, Differentiable ℝ (mellinOp^[a] f))
    (henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|))
    {w : Fin (k + 1) → ℝ} {l₀ : Fin (k + 1)} (hw : w l₀ = 1) (β : ℝ) :
    |β| ^ r * ‖∫ s : ℝ, Complex.exp (↑(β * s) * Complex.I) * (rayF f k 0 w s : ℂ)‖ ≤
      ∫ s, |rayF f k r w s| :=
  abs_pow_mul_norm_integral_exp_le (F := fun j => rayF f k j w)
    (fun _ hj s => hasDerivAt_rayF hd hrk hj w s)
    (fun _ hj => integrable_rayF hE hκ hf0 hc henv hj hw) β

end PGM
