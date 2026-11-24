import PLAStochastic.Index.KRE.LayerCountBridge
import PLAStochastic.Index.KRE.GoodEvent
import PLAStochastic.Index.ModelK.Transfer
import PLAStochastic.Index.KRE.HeightIntegrable

/-!
# H-K-RE for fixed parameters: the expected ALG-RE height under Model K

Let `f` be a Model K density (`DensityK f A B fmin fmax Lf`).  The change of keys is the
quantile `φ = quantK f A B`, with derivative `φ' u = 1 / f (φ u)` within `[0, 1]`,
`φ' ≥ δ = 1 / fmax > 0`, and `φ'` Lipschitz with constant `L = Lf / fmin³ + 1 > 0`
(`kre_quantK_deriv`, `kre_quantK_lip`, `kre_quantK_delta_pos`, `kre_quantK_le_deriv`).

On the canonical iid `Exp(1)` sequence, off the bad event `kreBad expCoord n eps t j` of
`PLAStochastic.Index.KRE.GoodEvent`, the reference keys `z s = expPartial s ω` satisfy `KREPath` for these data
(`krePath_of_not_kreBad`, `n ≥ 160000`).  Splitting the expectation on the bad event with the
deterministic bounds of `PLAStochastic.Index.KRE.LayerCountBridge` gives, for fixed parameters,

* the upper bound `E H ≤ kreUpper + (log₂ n + 1) P(bad)` (`integral_reHeight_expPartial_le`),
* the lower bound `kreLower (1 - P(bad)) ≤ E H` (`integral_reHeight_expPartial_ge_of_bad`,
  and `integral_reHeight_expPartial_ge` with the explicit bound on `P(bad)`),

where `P(bad) ≤ 18 / n² + 2 (2n + 1)² pairFail t + (2n + 1)² (71/72)^j`.  By the Model K
transfer `integral_reHeight_kKeys`, the same bounds hold for the sorted Model K sample
(`integral_reHeight_K_le`, `integral_reHeight_K_ge_of_bad`, `integral_reHeight_K_ge`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-! ## The analytic data of the quantile -/

/-- `quantK` has derivative `1 / f ∘ quantK` within `[0, 1]`. -/
theorem kre_quantK_deriv (hf : DensityK f A B fmin fmax Lf) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (quantK f A B) (1 / f (quantK f A B x)) (Set.Icc 0 1) x :=
  fun _ hx => hasDerivWithinAt_quantK hf hx

/-- The derivative `1 / f ∘ quantK` is `(Lf / fmin³ + 1)`-Lipschitz on `[0, 1]`. -/
theorem kre_quantK_lip (hf : DensityK f A B fmin fmax Lf) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |1 / f (quantK f A B x) - 1 / f (quantK f A B y)| ≤ (Lf / fmin ^ 3 + 1) * |x - y| :=
  fun _ hx _ hy => (abs_inv_f_quantK_sub_le hf hx hy).trans
    (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))

/-- The Lipschitz constant `Lf / fmin³ + 1` is positive. -/
theorem kre_quantK_lip_pos (hf : DensityK f A B fmin fmax Lf) : 0 < Lf / fmin ^ 3 + 1 := by
  have := div_nonneg hf.lf_nonneg (pow_nonneg hf.pos.le 3)
  linarith

theorem kre_quantK_delta_pos (hf : DensityK f A B fmin fmax Lf) : 0 < 1 / fmax :=
  one_div_pos.2 hf.fmax_pos

/-- The derivative `1 / f ∘ quantK` is at least `1 / fmax`. -/
theorem kre_quantK_le_deriv (hf : DensityK f A B fmin fmax Lf) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 / fmax ≤ 1 / f (quantK f A B x) :=
  fun x _ => (inv_f_quantK_mem_Icc hf x).1

/-! ## The good event of the canonical sequence -/

/-- Off the bad event, the partial sums of the canonical `Exp(1)` sequence satisfy `KREPath`
for the quantile of a Model K density. -/
theorem krePath_of_not_kreBad (hf : DensityK f A B fmin fmax Lf) {n : ℕ} (hn : 160000 ≤ n)
    {eps : ℝ} {t j : ℕ} {ω : ℕ → ℝ} (hω : ω ∉ kreBad expCoord n eps t j) :
    KREPath (quantK f A B) (fun u => 1 / f (quantK f A B u)) (Lf / fmin ^ 3 + 1) (1 / fmax)
      (fun s => expPartial s ω) n eps t j where
  deriv := kre_quantK_deriv hf
  lip := kre_quantK_lip hf
  delta_pos := kre_quantK_delta_pos hf
  le_deriv := kre_quantK_le_deriv hf
  strictMono := refWalk_strictMono hω
  mem_Icc := refWalk_div_mem_Icc hω
  span := refWalk_span hω
  tube := refWalk_tube hω
  half_le := half_le_refWalk hω hn
  bracket := fun _ hθ => refWalk_bracket hω hθ
  window := refWalk_not_windowFeasible hω

/-- The curved keys `s ↦ quantK f A B (Γ (s+1) / Γ (n+1))` are measurable. -/
theorem measurable_kreKeys (hf : DensityK f A B fmin fmax Lf) (n : ℕ) :
    Measurable fun (ω : ℕ → ℝ) (s : ℕ) => quantK f A B (expPartial s ω / expPartial n ω) :=
  measurable_pi_lambda _ fun s =>
    (measurable_quantK hf).comp ((measurable_expPartial s).div (measurable_expPartial n))

/-! ## The pathwise bounds -/

/-- The pathwise upper bound of `kreBridge_height_le`. -/
def kreUpper (n : ℕ) (eps L δ : ℝ) (t : ℕ) : ℝ :=
  Real.logb 2 (Real.log n / Real.log (eps ^ 2 / (4 * 514))) +
    Real.logb 2 (2 * (514 * (4 * ((t : ℝ) + 1) / (aRE / 4)) + ((t : ℝ) + 1))) +
    Real.logb 2 (Real.log n) +
    Real.logb 2 (max (3 * max 1 (16 / (kreC₂ eps L δ / 2) ^ 2)) (4 / (kreC₃ L δ / 2)) + 1) +
    8

/-- The pathwise lower bound of `kreBridge_logb_lt_height`. -/
def kreLower (n : ℕ) (eps : ℝ) : ℝ :=
  Real.logb 2 (Real.log n / (2 * Real.log (2 / (aRE / 4) * eps ^ 2)))

theorem kreUpper_nonneg {n : ℕ} (hn3 : 3 ≤ n) {eps : ℝ} (L δ : ℝ) (t : ℕ)
    (hq : 1 < eps ^ 2 / (4 * 514)) (hqn : eps ^ 2 / (4 * 514) ≤ n) :
    0 ≤ kreUpper n eps L δ t := by
  unfold kreUpper
  have hlog : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hlogq : 0 < Real.log (eps ^ 2 / (4 * 514)) := Real.log_pos hq
  have h1 : 0 ≤ Real.logb 2 (Real.log n / Real.log (eps ^ 2 / (4 * 514))) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hlogq, one_mul]
    exact Real.log_le_log (by linarith) hqn
  have h2 : 0 ≤ Real.logb 2 (2 * (514 * (4 * ((t : ℝ) + 1) / (aRE / 4)) + ((t : ℝ) + 1))) := by
    apply Real.logb_nonneg (by norm_num)
    have : 0 ≤ 514 * (4 * ((t : ℝ) + 1) / (aRE / 4)) := by have := aRE_pos; positivity
    have : (1 : ℝ) ≤ (t : ℝ) + 1 := by have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith
    linarith
  have h3 : 0 ≤ Real.logb 2 (Real.log n) := Real.logb_nonneg (by norm_num) hlog
  have h4 : 0 ≤ Real.logb 2
      (max (3 * max 1 (16 / (kreC₂ eps L δ / 2) ^ 2)) (4 / (kreC₃ L δ / 2)) + 1) := by
    apply Real.logb_nonneg (by norm_num)
    have := le_max_left (1 : ℝ) (16 / (kreC₂ eps L δ / 2) ^ 2)
    have := le_max_left (3 * max 1 (16 / (kreC₂ eps L δ / 2) ^ 2)) (4 / (kreC₃ L δ / 2))
    linarith
  linarith

/-! ## Expected height on the canonical sequence -/

/-- **Upper bound, fixed parameters.** -/
theorem integral_reHeight_expPartial_le (hf : DensityK f A B fmin fmax Lf) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : epsZero 1 18 ≤ eps / 2) (t j : ℕ) {Dn : ℝ}
    (hN1 : 16 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n)
    (hC1 : 640 * Real.log n ≤ eps * Dn)
    (hC2 : 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * Real.log n ≤ n)
    (hc₁D : 1 ≤ kreC₁ n eps / 2 * Dn)
    (hside : 64 * (kreC₂ eps (Lf / fmin ^ 3 + 1) (1 / fmax) / 2) ^ 2 * n ≤
      (kreC₁ n eps / 2) ^ 5 * Dn ^ 6)
    (hq : 1 < eps ^ 2 / (4 * 514)) (hqn : eps ^ 2 / (4 * 514) ≤ n) :
    ∫ ω, (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ)
        ∂expSeqMeasure ≤
      kreUpper n eps (Lf / fmin ^ 3 + 1) (1 / fmax) t +
        ((Nat.log 2 n : ℝ) + 1) *
          (18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
            ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j) := by
  have heps1 : 1 ≤ eps := by have := one_le_epsZero 1 18; linarith
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hHm : Measurable fun ω : ℕ → ℝ =>
      (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (measurable_reHeight_comp eps n (measurable_kreKeys hf n))
  have hmain := integral_le_of_good (P := expSeqMeasure)
    (H := fun ω => (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ))
    (measurableSet_kreBad measurable_expCoord n eps t j) hHm.aestronglyMeasurable
    (kreUpper_nonneg hn3 (Lf / fmin ^ 3 + 1) (1 / fmax) t hq hqn)
    (fun ω => Nat.cast_nonneg _) (Hmax := (Nat.log 2 n : ℝ) + 1)
    (fun ω => by exact_mod_cast reHeight_le_log heps1 hn1)
    (fun ω hω => kreBridge_height_le (krePath_of_not_kreBad hf hn hω) heps1 hn3
      (kre_quantK_lip_pos hf) hN1 hC1 hC2 hc₁D hside hq hqn)
  have hbad := measureReal_kreBad_le iidSeq_expCoord (hasLaw_expCoord 0) hn1 heps t j
  have hlog0 : 0 ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  calc _ ≤ _ := hmain
    _ ≤ _ := by gcongr

/-- **Lower bound, fixed parameters**, in terms of the probability of the bad event. -/
theorem integral_reHeight_expPartial_ge_of_bad (hf : DensityK f A B fmin fmax Lf) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : 1 ≤ eps) {t j : ℕ} (ht : 1 ≤ t) (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * (j : ℝ) ^ 2 * Dn ^ 3 *
      eps ^ 3 * Real.log n ≤ n)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn) (hsqrt : 4 * (t : ℝ) / (aRE / 4) ≤ Real.sqrt n) :
    kreLower n eps * (1 - expSeqMeasure.real (kreBad expCoord n eps t j)) ≤
      ∫ ω, (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ)
        ∂expSeqMeasure := by
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  set Lv := kreLower n eps
  set bad := kreBad expCoord n eps t j
  have hbadm : MeasurableSet bad := measurableSet_kreBad measurable_expCoord n eps t j
  have hHint : Integrable (fun ω : ℕ → ℝ =>
      (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ))
      expSeqMeasure :=
    integrable_reHeight heps hn1 (measurable_kreKeys hf n).aemeasurable
  have hpt : ∀ ω, badᶜ.indicator (fun _ => Lv) ω ≤
      (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ) := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_notMem (by simpa using hω)]; exact Nat.cast_nonneg _
    · rw [Set.indicator_of_mem (by simpa using hω)]
      exact (kreBridge_logb_lt_height (krePath_of_not_kreBad hf hn hω) heps hn3 ht hj hN2 hDn
        hsqrt).le
  have hint2 : Integrable (badᶜ.indicator (fun _ => Lv)) expSeqMeasure :=
    (integrable_const Lv).indicator hbadm.compl
  have hmono := integral_mono hint2 hHint hpt
  rw [integral_indicator hbadm.compl, setIntegral_const, probReal_compl_eq_one_sub hbadm,
    smul_eq_mul] at hmono
  linarith [mul_comm Lv (1 - expSeqMeasure.real bad)]

/-- **Lower bound, fixed parameters**, with the explicit bound on the bad event. -/
theorem integral_reHeight_expPartial_ge (hf : DensityK f A B fmin fmax Lf) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : epsZero 1 18 ≤ eps / 2) {t j : ℕ} (ht : 1 ≤ t)
    (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * (j : ℝ) ^ 2 * Dn ^ 3 *
      eps ^ 3 * Real.log n ≤ n)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn) (hsqrt : 4 * (t : ℝ) / (aRE / 4) ≤ Real.sqrt n)
    (hL0 : 0 ≤ kreLower n eps) :
    kreLower n eps *
        (1 - (18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
          ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j)) ≤
      ∫ ω, (reHeight eps (fun s => quantK f A B (expPartial s ω / expPartial n ω)) n : ℝ)
        ∂expSeqMeasure := by
  have heps1 : 1 ≤ eps := by have := one_le_epsZero 1 18; linarith
  have hn1 : 1 ≤ n := by omega
  have hbad := measureReal_kreBad_le iidSeq_expCoord (hasLaw_expCoord 0) hn1 heps t j
  calc _ ≤ kreLower n eps * (1 - expSeqMeasure.real (kreBad expCoord n eps t j)) := by
        gcongr
    _ ≤ _ := integral_reHeight_expPartial_ge_of_bad hf hn heps1 ht hj hN2 hDn hsqrt

/-! ## Model K -/

section ModelK

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **H-K-RE, upper bound, fixed parameters.** -/
theorem integral_reHeight_K_le (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : epsZero 1 18 ≤ eps / 2) (t j : ℕ) {Dn : ℝ}
    (hN1 : 16 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * Dn ^ 3 * eps ^ 3 * Real.log n ≤ n)
    (hC1 : 640 * Real.log n ≤ eps * Dn)
    (hC2 : 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * Real.log n ≤ n)
    (hc₁D : 1 ≤ kreC₁ n eps / 2 * Dn)
    (hside : 64 * (kreC₂ eps (Lf / fmin ^ 3 + 1) (1 / fmax) / 2) ^ 2 * n ≤
      (kreC₁ n eps / 2) ^ 5 * Dn ^ 6)
    (hq : 1 < eps ^ 2 / (4 * 514)) (hqn : eps ^ 2 / (4 * 514) ≤ n) :
    ∫ ω, (reHeight eps (kKeys X n ω) n : ℝ) ∂P ≤
      kreUpper n eps (Lf / fmin ^ 3 + 1) (1 / fmax) t +
        ((Nat.log 2 n : ℝ) + 1) *
          (18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
            ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j) := by
  rw [integral_reHeight_kKeys hf hX hind eps n]
  exact integral_reHeight_expPartial_le hf hn heps t j hN1 hC1 hC2 hc₁D hside hq hqn

/-- **H-K-RE, lower bound, fixed parameters**, in terms of the probability of the bad event
of the canonical sequence. -/
theorem integral_reHeight_K_ge_of_bad (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : 1 ≤ eps) {t j : ℕ} (ht : 1 ≤ t) (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * (j : ℝ) ^ 2 * Dn ^ 3 *
      eps ^ 3 * Real.log n ≤ n)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn) (hsqrt : 4 * (t : ℝ) / (aRE / 4) ≤ Real.sqrt n) :
    kreLower n eps * (1 - expSeqMeasure.real (kreBad expCoord n eps t j)) ≤
      ∫ ω, (reHeight eps (kKeys X n ω) n : ℝ) ∂P := by
  rw [integral_reHeight_kKeys hf hX hind eps n]
  exact integral_reHeight_expPartial_ge_of_bad hf hn heps ht hj hN2 hDn hsqrt

/-- **H-K-RE, lower bound, fixed parameters**, with the explicit bound on the bad event. -/
theorem integral_reHeight_K_ge (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) {n : ℕ}
    (hn : 160000 ≤ n) {eps : ℝ} (heps : epsZero 1 18 ≤ eps / 2) {t j : ℕ} (ht : 1 ≤ t)
    (hj : 1 ≤ j) {Dn : ℝ}
    (hN2 : 9 * 10 ^ 8 * kreLam (Lf / fmin ^ 3 + 1) (1 / fmax) * (j : ℝ) ^ 2 * Dn ^ 3 *
      eps ^ 3 * Real.log n ≤ n)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn) (hsqrt : 4 * (t : ℝ) / (aRE / 4) ≤ Real.sqrt n)
    (hL0 : 0 ≤ kreLower n eps) :
    kreLower n eps *
        (1 - (18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
          ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j)) ≤
      ∫ ω, (reHeight eps (kKeys X n ω) n : ℝ) ∂P := by
  rw [integral_reHeight_kKeys hf hX hind eps n]
  exact integral_reHeight_expPartial_ge hf hn heps ht hj hN2 hDn hsqrt hL0

end ModelK

end

end PGM
