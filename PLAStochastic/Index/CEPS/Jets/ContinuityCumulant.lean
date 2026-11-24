import PLAStochastic.Index.CEPS.Jets.JF

/-!
# X8: local Lipschitz continuity of the cumulant jets

The cumulant `κ_n = cepsCumRec m n` is a polynomial in the moments `m 1, …, m n`
(`cepsCumRec_congr`), hence `C¹` in them and Lipschitz near any moment sequence
(`cepsCumRec_local_lipschitz`). The moments of a density in the exponentially weighted Sobolev
class differ from those of `f_Λ` by at most a constant times `‖f - f_Λ‖_{m,η}`, so the cumulants
are Lipschitz in the Sobolev distance to `f_Λ` near `f_Λ` (`cepsCumulant_lipschitz`).
-/

noncomputable section

open MeasureTheory

namespace PGM

/-- `cepsCumRec m n` reads only the entries `m 1, …, m n`. -/
theorem cepsCumRec_congr {R : Type*} [CommRing R] {m m' : ℕ → R} {n : ℕ}
    (h : ∀ i, i ≤ n → m i = m' i) : cepsCumRec m n = cepsCumRec m' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp only [cepsCumRec_zero]
    · rw [cepsCumRec_succ, cepsCumRec_succ, h (n + 1) le_rfl]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      rw [ih (k + 1) (by omega) (fun i hi => h i (by omega)), h (n - k) (by omega)]

/-- The extension by zero of a finite vector to a sequence. -/
def cepsMomentExt {K : ℕ} (v : Fin K → ℝ) (i : ℕ) : ℝ :=
  if h : i < K then v ⟨i, h⟩ else 0

theorem contDiff_cepsMomentExt (K i : ℕ) :
    ContDiff ℝ 1 (fun v : Fin K → ℝ => cepsMomentExt v i) := by
  unfold cepsMomentExt
  split_ifs with h
  · exact contDiff_apply ℝ ℝ (⟨i, h⟩ : Fin K)
  · exact contDiff_const

/-- The cumulants are `C¹` (indeed polynomial) functions of finitely many moments. -/
theorem contDiff_cepsCumRec_ext (K n : ℕ) :
    ContDiff ℝ 1 (fun v : Fin K → ℝ => cepsCumRec (cepsMomentExt v) n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp only [cepsCumRec_zero]
      exact contDiff_const
    · have e : (fun v : Fin K → ℝ => cepsCumRec (cepsMomentExt v) (n + 1)) = fun v =>
          cepsMomentExt v (n + 1) - ∑ k ∈ Finset.range n,
            (n.choose k : ℝ) * cepsCumRec (cepsMomentExt v) (k + 1) * cepsMomentExt v (n - k) :=
        funext fun v => cepsCumRec_succ _ n
      rw [e]
      refine (contDiff_cepsMomentExt K (n + 1)).sub (ContDiff.sum fun k hk => ?_)
      have hk := Finset.mem_range.mp hk
      exact (contDiff_const.mul (ih (k + 1) (by omega))).mul (contDiff_cepsMomentExt K (n - k))

/-- **Local Lipschitz continuity of the cumulants in the moments.** Near a moment sequence `m₀`,
the cumulant of order `n` moves by at most `L ε` when the moments `1, …, n` move by at most
`ε < δ`. -/
theorem cepsCumRec_local_lipschitz (n : ℕ) (m₀ : ℕ → ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ ∀ (m : ℕ → ℝ) (ε : ℝ), ε < δ →
      (∀ i, i ≤ n → |m i - m₀ i| ≤ ε) → |cepsCumRec m n - cepsCumRec m₀ n| ≤ L * ε := by
  set g : (Fin (n + 1) → ℝ) → ℝ := fun v => cepsCumRec (cepsMomentExt v) n with hg
  set v₀ : Fin (n + 1) → ℝ := fun i => m₀ i with hv₀
  obtain ⟨L, t, ht, hlip⟩ :=
    ((contDiff_cepsCumRec_ext (n + 1) n).contDiffAt (x := v₀)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hval : ∀ m : ℕ → ℝ, cepsCumRec m n = g (fun i : Fin (n + 1) => m i) := by
    intro m
    refine cepsCumRec_congr fun i hi => ?_
    simp only [cepsMomentExt, dif_pos (show i < n + 1 by omega)]
  refine ⟨δ, L, hδ, L.coe_nonneg, fun m ε hε hm => ?_⟩
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hm 0 (Nat.zero_le n))
  have hd : dist (fun i : Fin (n + 1) => m i) v₀ ≤ ε := by
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg hε0).mpr fun i => ?_
    simp only [Pi.sub_apply, hv₀, Real.norm_eq_abs]
    exact hm i (by omega)
  have h1 : (fun i : Fin (n + 1) => m i) ∈ t :=
    hball (Metric.mem_ball.mpr (hd.trans_lt hε))
  have h0 : v₀ ∈ t := hball (Metric.mem_ball_self hδ)
  have hl := hlip.dist_le_mul _ h1 _ h0
  rw [hval m, hval m₀, ← Real.dist_eq]
  exact hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

/-- Moments of `f` and `f_Λ` differ by at most `k!/η^k e^η ‖f - f_Λ‖_{m,η}`. -/
theorem abs_cepsJetMoment_sub_le {m : ℕ} {η : ℝ} (hη : 0 < η) {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) (hΛ : CepsSobolevClass m η cepsLambdaDensity) (k : ℕ) :
    |cepsJetMoment f k - cepsJetMoment cepsLambdaDensity k| ≤
      k.factorial / η ^ k * Real.exp η * cepsSobolev m η (fun x => f x - cepsLambdaDensity x) := by
  rw [← cepsJetMoment_sub (integrable_pow_mul_of_sobolev hf hη k)
    (integrable_pow_mul_of_sobolev hΛ hη k)]
  exact abs_cepsJetMoment_le hη k (hf.sub hΛ)

/-- **Cumulant jets are Lipschitz near `f_Λ`.** For `η > 0` and `f_Λ` in the Sobolev class of
order `m` and weight `η`, every cumulant moves by at most `C ‖f - f_Λ‖_{m,η}` when this distance
is at most `r₀`. -/
theorem cepsCumulant_lipschitz (n : ℕ) {m : ℕ} {η : ℝ} (hη : 0 < η)
    (hΛ : CepsSobolevClass m η cepsLambdaDensity) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ f : ℝ → ℝ, CepsSobolevClass m η f →
      cepsSobolev m η (fun x => f x - cepsLambdaDensity x) ≤ r₀ →
      |cepsCumulant f n - cepsCumulant cepsLambdaDensity n| ≤
        C * cepsSobolev m η (fun x => f x - cepsLambdaDensity x) := by
  obtain ⟨δ, L, hδ, hL, hlip⟩ := cepsCumRec_local_lipschitz n (cepsJetMoment cepsLambdaDensity)
  set A : ℝ := ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ) / η ^ k * Real.exp η with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => by positivity
  have hAk : ∀ k, k ≤ n → (k.factorial : ℝ) / η ^ k * Real.exp η ≤ A := fun k hk =>
    Finset.single_le_sum (f := fun k => (k.factorial : ℝ) / η ^ k * Real.exp η)
      (fun k _ => by positivity) (Finset.mem_range.mpr (by omega))
  refine ⟨δ / (2 * (A + 1)), L * A, by positivity, mul_nonneg hL hA0, fun f hf hS => ?_⟩
  set S := cepsSobolev m η (fun x => f x - cepsLambdaDensity x) with hSdef
  have hS0 : 0 ≤ S := cepsSobolev_nonneg _ _ _
  have hAS : A * S < δ := by
    calc A * S ≤ A * (δ / (2 * (A + 1))) := mul_le_mul_of_nonneg_left hS hA0
      _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have h := hlip (cepsJetMoment f) (A * S) hAS fun k hk =>
    (abs_cepsJetMoment_sub_le hη hf hΛ k).trans (mul_le_mul_of_nonneg_right (hAk k hk) hS0)
  calc |cepsCumulant f n - cepsCumulant cepsLambdaDensity n| ≤ L * (A * S) := h
    _ = L * A * S := by ring

end PGM
