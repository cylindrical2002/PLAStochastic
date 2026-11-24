import PLAStochastic.Index.CEPS.Actual.KilledDecay
import PLAStochastic.Index.GEP.SurvivalBound.GoodSlope
import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.LastGap
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Markov

/-!
# P-CEPS WP8: the exact integral of one minimal-slope certificate

For a certificate pair `(i, j) = (i, i + L)` with `L > w = 2ε` and `k = i + L + r`, in drift units
`μ = 1/a - 1` (`a` the certificate slope), band width `l = w(1+μ)` and `q = t(1+μ)`:

`E[e^{-t S_k}; cert(i, j)] = (L - w) ∫_{μ > -1} e^{-t((1+μ)k - l)} h_i(μ) h_r(μ) k_L^{(μ)}(0, l) dμ`

(`CepsGapDensity.integral_cert_eq`), where `h_n(μ) = cepsStripTerm ν t μ l n` and
`k_L^{(μ)}(0, l) = cepsBridgeDens ν f μ l L`. This is analytic-response (7) in drift units.

1. **Pathwise** (`ceps_cert_pathwise`): on positive gaps, scaling the residual walks by `1/a = 1+μ`
   turns the three blocks of `certOK` into the outer walk `V` (prefix, reversed), the middle walk with
   step `1 + μ - X`, and the outer walk of the reflected suffix, all in `[0, l]`; the last key is
   `S_k = (1+μ)k - l + U + V`.
2. **Permutation and Fubini** (`integral_cepsPermInt`): after putting the middle block first, the
   prefix–suffix integral at fixed drift is `e^{-t((1+μ)k - l)} h_i h_r`.
3. **Middle block** (`CepsGapDensity.integral_midAlive_mul`): translating the last middle gap pins the
   middle sum `s = (L - w)(1+μ)`; the last-gap reconstruction gives the killed endpoint density, and
   the affine change of variables `s ↦ μ` has Jacobian `L - w`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## Scaling the residual walks to drift units -/

theorem mem_Icc_zero_iff_div {a : ℝ} (ha : 0 < a) (x w : ℝ) :
    x ∈ Icc 0 w ↔ x / a ∈ Icc 0 (w / a) := by
  simp only [mem_Icc]
  rw [le_div_iff₀ ha, zero_mul, div_le_div_iff_of_pos_right ha]

theorem indicator_Icc_div {a : ℝ} (ha : 0 < a) (x w : ℝ) :
    (Icc 0 w).indicator (fun _ => (1 : ℝ)) x =
      (Icc 0 (w / a)).indicator (fun _ => (1 : ℝ)) (x / a) := by
  by_cases h : x ∈ Icc 0 w
  · rw [indicator_of_mem h, indicator_of_mem ((mem_Icc_zero_iff_div ha x w).1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((mem_Icc_zero_iff_div ha x w).2 h'))]

theorem kWalk_rev_div {a : ℝ} (ha : a ≠ 0) (G : ℕ → ℝ) (l : ℕ) :
    kWalk 0 (-1) (-a) G l / a = kWalk 0 (-(1 / a)) (-1) G l := by
  unfold kWalk; field_simp; ring

theorem kWalk_fwd_div {a : ℝ} (ha : a ≠ 0) (G : ℕ → ℝ) (l : ℕ) :
    kWalk 0 1 a G l / a = kWalk 0 (1 / a) 1 G l := by
  unfold kWalk; field_simp; ring

theorem kWalk_suf_div {a : ℝ} (ha : a ≠ 0) (w : ℝ) (G : ℕ → ℝ) (l : ℕ) :
    (w - kWalk w 1 a G l) / a = kWalk 0 (-(1 / a)) (-1) G l := by
  unfold kWalk; field_simp; ring

theorem krAlive_rev_scale {a : ℝ} (ha : 0 < a) (w : ℝ) (n : ℕ) (G : ℕ → ℝ) :
    krAlive (Icc 0 w) (-1) (-a) n 0 G = krAlive (Icc 0 (w / a)) (-(1 / a)) (-1) n 0 G := by
  unfold krAlive
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [indicator_Icc_div ha, kWalk_rev_div ha.ne']

theorem krAlive_fwd_scale {a : ℝ} (ha : 0 < a) (w : ℝ) (n : ℕ) (G : ℕ → ℝ) :
    krAlive (Icc 0 w) 1 a n 0 G = krAlive (Icc 0 (w / a)) (1 / a) 1 n 0 G := by
  unfold krAlive
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [indicator_Icc_div ha, kWalk_fwd_div ha.ne']

theorem krAlive_suf_scale {a : ℝ} (ha : 0 < a) (w : ℝ) (n : ℕ) (G : ℕ → ℝ) :
    krAlive (Icc 0 w) 1 a n w G = krAlive (Icc 0 (w / a)) (-(1 / a)) (-1) n 0 G := by
  unfold krAlive
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← indicator_Icc_reflect w, indicator_Icc_div ha, kWalk_suf_div ha.ne']

theorem krAlive_congr {J : Set ℝ} {β a y : ℝ} {n : ℕ} {G G' : ℕ → ℝ}
    (h : ∀ s < n, G s = G' s) : krAlive J β a n y G = krAlive J β a n y G' := by
  unfold krAlive
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [surv_kWalk_congr fun s hs => h s (by omega)]

/-! ## The permuted integrand -/

/-- The drift of a middle block of `L` gaps: `μ = S_L / (L - 2ε) - 1`. -/
def cepsMidDrift (eps : ℝ) (L : ℕ) (h : ℕ → ℝ) : ℝ := gapKeys h L / ((L : ℝ) - 2 * eps) - 1

/-- The middle walk (step `1 + μ - X`) stays in `[0, 2ε(1+μ)]`. -/
def cepsMidAlive (eps : ℝ) (L : ℕ) (h : ℕ → ℝ) : ℝ :=
  krAlive (Icc 0 (2 * eps * (1 + cepsMidDrift eps L h))) (1 + cepsMidDrift eps L h) 1 L 0 h

/-- The integrand of `cepsStripTerm`. -/
def cepsStripIntegrand (t : ℂ) (μ l : ℝ) (n : ℕ) (h : ℕ → ℝ) : ℂ :=
  (krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h : ℂ) *
    Complex.exp (-t * kWalk 0 (-(1 + μ)) (-1) h n)

theorem integral_cepsStripIntegrand (ν : ProbabilityMeasure ℝ) (t : ℂ) (μ l : ℝ) (n : ℕ) :
    ∫ h, cepsStripIntegrand t μ l n h ∂(iidLaw ν) = cepsStripTerm ν t μ l n := rfl

/-- The prefix–suffix integrand at drift `μ`: reversed prefix of `i` steps, reflected suffix of
`r` steps, and the deterministic part `e^{-t((1+μ)k - l)}` of the last key. -/
def cepsOuterInt (t : ℂ) (eps : ℝ) (i r k : ℕ) (μ : ℝ) (h : ℕ → ℝ) : ℂ :=
  cepsStripIntegrand t μ (2 * eps * (1 + μ)) i h *
    cepsStripIntegrand t μ (2 * eps * (1 + μ)) r (fun m => h (i + m)) *
    Complex.exp (-t * (((1 + μ) * k - 2 * eps * (1 + μ) : ℝ) : ℂ))

/-- The permuted certificate integrand: middle block on `0, …, L-1`, then prefix and suffix. -/
def cepsPermInt (t : ℂ) (eps : ℝ) (i L r : ℕ) (h : ℕ → ℝ) : ℂ :=
  (cepsMidAlive eps L h : ℂ) *
    cepsOuterInt t eps i r (i + L + r) (cepsMidDrift eps L h) (fun m => h (L + m))

/-! ## Measurability and bounds -/

theorem measurable_cepsMidDrift (eps : ℝ) (L : ℕ) : Measurable (cepsMidDrift eps L) :=
  ((rawAsm_measurable_gapKeys L).div_const _).sub_const _

theorem measurable_cepsMidAlive (eps : ℝ) (L : ℕ) : Measurable (cepsMidAlive eps L) := by
  have hμ := measurable_cepsMidDrift eps L
  exact measurable_krAlive_band (measurable_const.mul (measurable_const.add hμ)) measurable_const
    (measurable_const.add hμ) measurable_const measurable_id L

theorem measurable_cepsStripIntegrand_param (t : ℂ) (eps : ℝ) (n : ℕ) {α : Type*}
    [MeasurableSpace α] {μ : α → ℝ} {G : α → ℕ → ℝ} (hμ : Measurable μ) (hG : Measurable G) :
    Measurable (fun p => cepsStripIntegrand t (μ p) (2 * eps * (1 + μ p)) n (G p)) := by
  unfold cepsStripIntegrand
  have hβ : Measurable fun p => -(1 + μ p) := (measurable_const.add hμ).neg
  refine (Complex.measurable_ofReal.comp (measurable_krAlive_band
    (measurable_const.mul (measurable_const.add hμ)) measurable_const hβ measurable_const hG n)).mul ?_
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_kWalk_param measurable_const hβ measurable_const hG n)))

theorem measurable_cepsOuterInt (t : ℂ) (eps : ℝ) (i r k : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => cepsOuterInt t eps i r k p.1 p.2) := by
  unfold cepsOuterInt
  have hsh : Measurable fun p : ℝ × (ℕ → ℝ) => fun m => p.2 (i + m) :=
    measurable_pi_lambda _ fun m => (measurable_pi_apply (i + m)).comp measurable_snd
  refine ((measurable_cepsStripIntegrand_param t eps i measurable_fst measurable_snd).mul
    (measurable_cepsStripIntegrand_param t eps r measurable_fst hsh)).mul ?_
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (by fun_prop)))

theorem measurable_cepsPermInt (t : ℂ) (eps : ℝ) (i L r : ℕ) :
    Measurable (cepsPermInt t eps i L r) := by
  have hsh : Measurable fun h : ℕ → ℝ => fun m => h (L + m) :=
    measurable_pi_lambda _ fun m => measurable_pi_apply (L + m)
  unfold cepsPermInt
  refine Measurable.mul ?_ ?_
  · exact Complex.measurable_ofReal.comp (measurable_cepsMidAlive eps L)
  · have h2 := (measurable_cepsOuterInt t eps i r (i + L + r)).comp
      ((measurable_cepsMidDrift eps L).prodMk hsh)
    exact h2

theorem cepsMidAlive_nonneg (eps : ℝ) (L : ℕ) (h : ℕ → ℝ) : 0 ≤ cepsMidAlive eps L h :=
  krAlive_nonneg _ _ _

theorem cepsMidAlive_le_one (eps : ℝ) (L : ℕ) (h : ℕ → ℝ) : cepsMidAlive eps L h ≤ 1 :=
  krAlive_le_one _ _ _

theorem norm_cepsStripIntegrand_le {t : ℂ} (ht : 0 ≤ t.re) (μ l : ℝ) (n : ℕ) (h : ℕ → ℝ) :
    ‖cepsStripIntegrand t μ l n h‖ ≤ krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h := by
  unfold cepsStripIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _)]
  by_cases h0 : krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h = 0
  · rw [h0, zero_mul]
  · have hm := krAlive_ne_zero_mem h0 n le_rfl
    calc krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h * ‖Complex.exp (-t * kWalk 0 (-(1 + μ)) (-1) h n)‖
        ≤ krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h * 1 :=
          mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_le_one ht hm.1) (krAlive_nonneg _ _ _)
      _ = krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 h := mul_one _

theorem norm_cepsStripIntegrand_le_one {t : ℂ} (ht : 0 ≤ t.re) (μ l : ℝ) (n : ℕ)
    (h : ℕ → ℝ) : ‖cepsStripIntegrand t μ l n h‖ ≤ 1 :=
  (norm_cepsStripIntegrand_le ht μ l n h).trans (krAlive_le_one _ _ _)

theorem krAlive_zero_of_neg {l β a : ℝ} (hl : l < 0) (n : ℕ) (G : ℕ → ℝ) :
    krAlive (Icc 0 l) β a n 0 G = 0 :=
  krAlive_eq_zero_of_notMem (fun h : (0 : ℝ) ∈ Icc 0 l => by linarith [h.2]) n G

theorem norm_cepsOuterInt_le_one {t : ℂ} (ht : 0 ≤ t.re) {eps : ℝ} (heps : 0 < eps) {i r k : ℕ}
    (hk : 2 * eps ≤ k) (μ : ℝ) (h : ℕ → ℝ) : ‖cepsOuterInt t eps i r k μ h‖ ≤ 1 := by
  unfold cepsOuterInt
  rcases lt_or_ge (1 + μ) 0 with hμ | hμ
  · have hl : 2 * eps * (1 + μ) < 0 := mul_neg_of_pos_of_neg (by linarith) hμ
    rw [cepsStripIntegrand, krAlive_zero_of_neg hl]
    simp
  · rw [norm_mul, norm_mul]
    have hE : ‖Complex.exp (-t * (((1 + μ) * k - 2 * eps * (1 + μ) : ℝ) : ℂ))‖ ≤ 1 :=
      norm_cexp_neg_mul_le_one ht (by nlinarith)
    calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul (norm_cepsStripIntegrand_le_one ht _ _ _ _)
          (norm_cepsStripIntegrand_le_one ht _ _ _ _) (norm_nonneg _) zero_le_one) hE
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

theorem norm_cepsPermInt_le_one {t : ℂ} (ht : 0 ≤ t.re) {eps : ℝ} (heps : 0 < eps) {i L r : ℕ}
    (hL : 2 * eps < L) (h : ℕ → ℝ) : ‖cepsPermInt t eps i L r h‖ ≤ 1 := by
  unfold cepsPermInt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cepsMidAlive_nonneg _ _ _)]
  have hk : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  calc cepsMidAlive eps L h * ‖cepsOuterInt t eps i r (i + L + r) _ _‖ ≤ 1 * 1 :=
        mul_le_mul (cepsMidAlive_le_one _ _ _) (norm_cepsOuterInt_le_one ht heps hk _ _)
          (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ## Step 1: the pathwise identity -/

theorem indicator_one_ofReal {α : Type*} (A : Set α) (x : α) :
    A.indicator (fun _ => (1 : ℂ)) x = ((A.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
  by_cases h : x ∈ A
  · rw [indicator_of_mem h, indicator_of_mem h, Complex.ofReal_one]
  · rw [indicator_of_notMem h, indicator_of_notMem h, Complex.ofReal_zero]

/-- **The certificate in drift units.** On positive gaps, the certificate indicator times
`e^{-tS_k}` is the permuted integrand evaluated on the reordered gaps (middle, reversed prefix,
suffix). -/
theorem ceps_cert_pathwise {eps : ℝ} (heps : 0 < eps) {i L r : ℕ} (hL : 2 * eps < L) (t : ℂ)
    {g : ℕ → ℝ} (hg : ∀ l, 0 < g l) :
    ({g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g) * Complex.exp (-t * gapKeys g (i + L + r)) =
      cepsPermInt t eps i L r (fun l => g (surv_pi i (i + L) L l)) := by
  have hL0 : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hij : i < i + L := by omega
  have hjk : i + L ≤ i + L + r := by omega
  set h : ℕ → ℝ := fun l => g (surv_pi i (i + L) L l) with hh
  have hmid : ∀ s < L, h s = g (i + s) := fun s hs => by
    simp only [hh]; rw [surv_pi_of_lt hs]
  have hpre : ∀ s < i, h (L + s) = g (i - 1 - s) := fun s hs => by
    simp only [hh]; rw [surv_pi_prefix hij rfl hs]
  have hsuf : ∀ m, h (L + (i + m)) = g (i + L + m) := fun m => by
    simp only [hh]; rw [surv_pi_suffix rfl]
  have hpos : ∀ s t', s < t' → t' ≤ i + L + r → gapKeys g s < gapKeys g t' :=
    cert_gapKeys_lt fun l _ => hg l
  have hne : gapKeys g i ≠ gapKeys g (i + L) := (hpos i (i + L) hij hjk).ne
  have hs0 : 0 < gapKeys g (i + L) - gapKeys g i := sub_pos.2 (hpos i (i + L) hij hjk)
  have hc0 : 0 < (L : ℝ) - 2 * eps := by linarith
  have hhL : gapKeys h L = gapKeys g (i + L) - gapKeys g i := by
    have e : gapKeys h L = gapKeys (fun m => g (i + m)) L := by
      unfold gapKeys
      exact Finset.sum_congr rfl fun x hx => hmid x (Finset.mem_range.1 hx)
    rw [e, gapKeys_shift]
  have ha_eq : certSlope eps (gapKeys g) i (i + L) =
      ((L : ℝ) - 2 * eps) / (gapKeys g (i + L) - gapKeys g i) := by
    rw [certSlope]
    congr 1
    push_cast
    ring
  set a := certSlope eps (gapKeys g) i (i + L) with ha
  have ha0 : 0 < a := by rw [ha_eq]; positivity
  set μ := cepsMidDrift eps L h with hμ
  have hμa : 1 + μ = 1 / a := by
    rw [hμ, cepsMidDrift, hhL, ha_eq]
    field_simp
    ring
  have hla : 2 * eps * (1 + μ) = 2 * eps / a := by rw [hμa]; ring
  -- the indicator in drift units
  have hind : {g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
      (fun _ => (1 : ℝ)) g =
        krAlive (Icc 0 (2 * eps * (1 + μ))) (-(1 + μ)) (-1) i 0 (fun m => h (L + m)) *
          cepsMidAlive eps L h *
          krAlive (Icc 0 (2 * eps * (1 + μ))) (-(1 + μ)) (-1) r 0 (fun m => h (L + (i + m))) := by
    rw [cert_indicator_certOK_eq_prod hij.le hjk hne]
    have e1 : i + L - i = L := by omega
    have e2 : i + L + r - (i + L) = r := by omega
    rw [e1, e2]
    change krAlive (Icc 0 (2 * eps)) (-1) (-a) i 0 (fun m => g (i - 1 - m)) *
      krAlive (Icc 0 (2 * eps)) 1 a L 0 (fun m => g (i + m)) *
      krAlive (Icc 0 (2 * eps)) 1 a r (2 * eps) (fun m => g (i + L + m)) = _
    rw [krAlive_rev_scale ha0, krAlive_fwd_scale ha0, krAlive_suf_scale ha0, ← hla, ← hμa]
    unfold cepsMidAlive
    rw [← hμ]
    congr 1
    · congr 1
      · exact krAlive_congr fun s hs => (hpre s hs).symm
      · exact krAlive_congr fun s hs => (hmid s hs).symm
    · exact krAlive_congr fun m _ => (hsuf m).symm
  -- the last key in drift units
  have hU : kWalk 0 (-(1 + μ)) (-1) (fun m => h (L + m)) i =
      kWalk 0 (-1) (-a) (fun m => g (i - 1 - m)) i / a := by
    rw [kWalk_rev_div ha0.ne', hμa]
    exact surv_kWalk_congr fun s hs => hpre s hs
  have hV : kWalk 0 (-(1 + μ)) (-1) (fun m => h (L + (i + m))) r =
      (2 * eps - kWalk (2 * eps) 1 a (fun m => g (i + L + m)) r) / a := by
    rw [kWalk_suf_div ha0.ne', hμa]
    exact surv_kWalk_congr fun m _ => hsuf m
  have hkey : gapKeys g (i + L + r) =
      kWalk 0 (-(1 + μ)) (-1) (fun m => h (L + m)) i +
        kWalk 0 (-(1 + μ)) (-1) (fun m => h (L + (i + m))) r +
        ((1 + μ) * ((i + L + r : ℕ) : ℝ) - 2 * eps * (1 + μ)) := by
    have hk := cert_gapKeys_eq_ends_certSlope hij.le hjk hne ha0.ne'
    have e2 : i + L + r - (i + L) = r := by omega
    rw [e2, ← ha] at hk
    rw [hk, hU, hV, hμa]
    field_simp
    ring
  -- assemble
  unfold cepsPermInt cepsOuterInt cepsStripIntegrand
  rw [← hμ, indicator_one_ofReal, hind, hkey]
  simp only [neg_mul, Complex.ofReal_add, Complex.ofReal_mul, mul_add, neg_add, Complex.exp_add]
  push_cast
  ring

/-! ## Step 2: permutation and the prefix–suffix integral -/

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

theorem CepsGapDensity.integral_cert_eq_perm (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {i L r : ℕ} (hL : 2 * eps < L) (t : ℂ) :
    ∫ g, ({g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g) * Complex.exp (-t * gapKeys g (i + L + r)) ∂(iidLaw ν) =
      ∫ h, cepsPermInt t eps i L r h ∂(iidLaw ν) := by
  have hπ := surv_pi_injective (i := i) (j := i + L) (L := L) (by
    have : (0 : ℝ) < L := by linarith
    have : 0 < L := by exact_mod_cast this
    omega) rfl
  rw [integral_congr_ae (hf.ae_iidLaw_pos.mono fun g hg => ceps_cert_pathwise heps hL t hg)]
  have := integral_wordLaw_comp ν ν ∅ hπ (F := cepsPermInt t eps i L r)
    (measurable_cepsPermInt t eps i L r).aestronglyMeasurable
  simpa only [wordLaw_self] using this

/-- The prefix–suffix integral at fixed drift. -/
def cepsOuterMean (ν : ProbabilityMeasure ℝ) (t : ℂ) (eps : ℝ) (i r k : ℕ) (μ : ℝ) : ℂ :=
  ∫ h, cepsOuterInt t eps i r k μ h ∂(iidLaw ν)

theorem measurable_cepsOuterMean (ν : ProbabilityMeasure ℝ) (t : ℂ) (eps : ℝ) (i r k : ℕ) :
    Measurable (cepsOuterMean ν t eps i r k) :=
  ((measurable_cepsOuterInt t eps i r k).stronglyMeasurable.integral_prod_right'
    (ν := iidLaw ν)).measurable

theorem norm_cepsOuterMean_le_one (ν : ProbabilityMeasure ℝ) {t : ℂ} (ht : 0 ≤ t.re) {eps : ℝ}
    (heps : 0 < eps) {i r k : ℕ} (hk : 2 * eps ≤ k) (μ : ℝ) :
    ‖cepsOuterMean ν t eps i r k μ‖ ≤ 1 := by
  unfold cepsOuterMean
  have h := norm_integral_le_of_norm_le_const (μ := iidLaw ν)
    (f := fun h => cepsOuterInt t eps i r k μ h)
    (Eventually.of_forall fun h => norm_cepsOuterInt_le_one ht heps hk μ h)
  simpa using h

theorem integral_cepsPermInt (ν : ProbabilityMeasure ℝ) {eps : ℝ}
    (heps : 0 < eps) {i L r : ℕ} (hL : 2 * eps < L) {t : ℂ} (ht : 0 ≤ t.re) :
    ∫ h, cepsPermInt t eps i L r h ∂(iidLaw ν) =
      ∫ h, (cepsMidAlive eps L h : ℂ) *
        cepsOuterMean ν t eps i r (i + L + r) (cepsMidDrift eps L h) ∂(iidLaw ν) := by
  have hcat := surv_integral_cat ν ν ∅ L (measurable_cepsPermInt t eps i L r)
    (norm_cepsPermInt_le_one ht heps hL)
  simp only [wordLaw_self] at hcat
  rw [hcat]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hk : ∀ h' : ℕ → ℝ, cepsPermInt t eps i L r (surv_cat L g h') =
      (cepsMidAlive eps L g : ℂ) * cepsOuterInt t eps i r (i + L + r) (cepsMidDrift eps L g) h' := by
    intro h'
    have hagree : ∀ s < L, surv_cat L g h' s = g s := fun s hs => surv_cat_apply_lt hs g h'
    have hdrift : cepsMidDrift eps L (surv_cat L g h') = cepsMidDrift eps L g := by
      unfold cepsMidDrift gapKeys
      rw [Finset.sum_congr rfl fun s hs => hagree s (Finset.mem_range.1 hs)]
    have halive : cepsMidAlive eps L (surv_cat L g h') = cepsMidAlive eps L g := by
      unfold cepsMidAlive
      rw [hdrift]
      exact krAlive_congr hagree
    have hshift : (fun m => surv_cat L g h' (L + m)) = h' :=
      funext fun m => surv_cat_apply_add L m g h'
    unfold cepsPermInt
    rw [halive, hdrift, hshift]
  simp only [hk]
  rw [integral_const_mul]
  rfl

theorem dependsOnPrefix_cepsStripIntegrand (t : ℂ) (μ l : ℝ) (n : ℕ) :
    WienerHopf.DependsOnPrefix n (cepsStripIntegrand t μ l n) := by
  intro ω ω' h
  unfold cepsStripIntegrand
  rw [krAlive_congr h, surv_kWalk_congr h]

theorem cepsOuterMean_eq (ν : ProbabilityMeasure ℝ) (t : ℂ) (eps : ℝ) (i r k : ℕ) (μ : ℝ) :
    cepsOuterMean ν t eps i r k μ =
      cepsStripTerm ν t μ (2 * eps * (1 + μ)) i * cepsStripTerm ν t μ (2 * eps * (1 + μ)) r *
        Complex.exp (-t * (((1 + μ) * k - 2 * eps * (1 + μ) : ℝ) : ℂ)) := by
  unfold cepsOuterMean cepsOuterInt
  rw [integral_mul_const]
  congr 1
  have hm : ∀ n, Measurable (cepsStripIntegrand t μ (2 * eps * (1 + μ)) n) := fun n =>
    measurable_cepsStripIntegrand_param t eps n (μ := fun _ : ℕ → ℝ => μ) measurable_const
      measurable_id
  exact WienerHopf.integral_mul_shift (ρ := (ν : Measure ℝ)) (hm i)
    (dependsOnPrefix_cepsStripIntegrand t μ _ i) (hm r)

/-! ## Step 3: the middle block -/

theorem CepsGapDensity.cepsBridgeDens_eq_zero_of_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {μ : ℝ} (hμ : μ ≤ -1) (n : ℕ) :
    cepsBridgeDens ν f μ (2 * eps * (1 + μ)) (n + 1) = 0 := by
  unfold cepsBridgeDens
  rcases lt_or_eq_of_le hμ with hlt | heq
  · apply krDens_eq_zero_of_right_notMem
    intro hm
    have := hm.1
    nlinarith
  · rw [krDens_succ]
    refine (integral_congr_ae (Eventually.of_forall fun g => ?_)).trans (integral_zero _ _)
    unfold krKer
    by_cases hy : kWalk 0 (1 + μ) 1 g n ∈ Icc 0 (2 * eps * (1 + μ))
    · have hz : 2 * eps * (1 + μ) = 0 := by rw [heq]; ring
      have hy0 : kWalk 0 (1 + μ) 1 g n = 0 :=
        le_antisymm (hy.2.trans hz.le) hy.1
      rw [hy0, heq]
      norm_num [hf.eq_zero 0 le_rfl]
    · rw [indicator_of_notMem hy]
      ring

/-- The middle-block integrand `1{middle walk alive} Ψ(μ)`. -/
def cepsMidF (eps : ℝ) (L : ℕ) (Ψ : ℝ → ℂ) (h : ℕ → ℝ) : ℂ :=
  (cepsMidAlive eps L h : ℂ) * Ψ (cepsMidDrift eps L h)

/-- `k_L^{(μ)}(0, l) Ψ(μ)` at `l = 2ε(1+μ)`. -/
def cepsBridgeMul (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (L : ℕ) (Ψ : ℝ → ℂ)
    (μ : ℝ) : ℂ :=
  (cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L : ℂ) * Ψ μ

theorem measurable_cepsMidF (eps : ℝ) (L : ℕ) {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) :
    Measurable (cepsMidF eps L Ψ) :=
  (Complex.measurable_ofReal.comp (measurable_cepsMidAlive eps L)).mul
    (hΨ.comp (measurable_cepsMidDrift eps L))

theorem norm_cepsMidF_le (eps : ℝ) (L : ℕ) {Ψ : ℝ → ℂ} {M : ℝ} (hM : ∀ μ, ‖Ψ μ‖ ≤ M)
    (h : ℕ → ℝ) : ‖cepsMidF eps L Ψ h‖ ≤ M := by
  unfold cepsMidF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cepsMidAlive_nonneg _ _ _)]
  calc _ ≤ 1 * M := mul_le_mul (cepsMidAlive_le_one _ _ _) (hM _) (norm_nonneg _) zero_le_one
    _ = M := one_mul M

/-- **The pinned last middle gap.** Translating the last middle gap to make the middle sum `x`
gives the killed endpoint density at drift `μ = x/(L - 2ε) - 1`. -/
theorem integral_midShift (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (n : ℕ)
    (hc0 : ((n + 1 : ℕ) : ℝ) - 2 * eps ≠ 0) (Ψ : ℝ → ℂ) (x : ℝ) :
    ∫ g, (f (x - gapKeys g n) : ℂ) *
        cepsMidF eps (n + 1) Ψ (Function.update g n (x - gapKeys g n)) ∂(iidLaw ν) =
      cepsBridgeMul ν f eps (n + 1) Ψ (x / (((n + 1 : ℕ) : ℝ) - 2 * eps) - 1) := by
  set c : ℝ := ((n + 1 : ℕ) : ℝ) - 2 * eps with hc
  set μx := x / c - 1 with hμx
  have hkeys : ∀ g : ℕ → ℝ, gapKeys (Function.update g n (x - gapKeys g n)) (n + 1) = x :=
    fun g => by rw [gapKeys_update_succ]; ring
  have hdrift : ∀ g : ℕ → ℝ,
      cepsMidDrift eps (n + 1) (Function.update g n (x - gapKeys g n)) = μx := fun g => by
    unfold cepsMidDrift
    rw [hkeys, ← hc]
  have hpin : ∀ g : ℕ → ℝ,
      kernelPinLastGap (1 + μx) 1 0 (2 * eps * (1 + μx)) n g = x - gapKeys g n := fun g => by
    unfold kernelPinLastGap kWalk
    rw [hμx]
    have hc' : c = (n : ℝ) + 1 - 2 * eps := by rw [hc]; push_cast; ring
    field_simp
    rw [hc']
    ring
  have e : ∀ g : ℕ → ℝ, (f (x - gapKeys g n) : ℂ) *
      cepsMidF eps (n + 1) Ψ (Function.update g n (x - gapKeys g n)) =
      ((f (kernelPinLastGap (1 + μx) 1 0 (2 * eps * (1 + μx)) n g) *
        krAlive (Icc 0 (2 * eps * (1 + μx))) (1 + μx) 1 (n + 1) 0
          (kernelPinLastPath (1 + μx) 1 0 (2 * eps * (1 + μx)) n g) : ℝ) : ℂ) * Ψ μx := by
    intro g
    simp only [cepsMidF, cepsMidAlive, hdrift]
    rw [kernelPinLastPath, hpin g]
    push_cast
    ring
  simp_rw [e]
  rw [integral_mul_const, integral_complex_ofReal,
    kernel_pin_last_integral_eq_density (Icc 0 _) ν f one_ne_zero]
  simp [cepsBridgeMul, cepsBridgeDens]

theorem CepsGapDensity.integrable_midShift (hf : CepsGapDensity ν f D) (eps : ℝ) (n : ℕ)
    {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) {M : ℝ} (hM : ∀ μ, ‖Ψ μ‖ ≤ M) :
    Integrable (fun p : (ℕ → ℝ) × ℝ => (f (p.2 - gapKeys p.1 n) : ℂ) *
      cepsMidF eps (n + 1) Ψ (Function.update p.1 n (p.2 - gapKeys p.1 n)))
      ((iidLaw ν).prod volume) := by
  obtain ⟨hfi, -⟩ := surv_integrable_density hf.measurable hf.nonneg hf.eq
  have hR : Measurable fun g : ℕ → ℝ => gapKeys g n := rawAsm_measurable_gapKeys n
  have hU : Measurable fun p : (ℕ → ℝ) × ℝ => Function.update p.1 n (p.2 - gapKeys p.1 n) :=
    (measurable_update_pair n).comp ((measurable_snd.sub (hR.comp measurable_fst)).prodMk
      measurable_fst)
  have hfm : Measurable fun p : (ℕ → ℝ) × ℝ => f (p.2 - gapKeys p.1 n) :=
    hf.measurable.comp (measurable_snd.sub (hR.comp measurable_fst))
  have hdom : Integrable (fun p : (ℕ → ℝ) × ℝ => M * f (p.2 - gapKeys p.1 n))
      ((iidLaw ν).prod volume) := by
    refine Integrable.const_mul ?_ M
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Eventually.of_forall fun g => hfi.comp_sub_right (gapKeys g n)
    · have e : ∀ g : ℕ → ℝ, ∫ t, ‖f (t - gapKeys g n)‖ = ∫ t, f t := by
        intro g
        simp only [Real.norm_eq_abs, abs_of_nonneg (hf.nonneg _)]
        exact integral_sub_right_eq_self (fun t => f t) (gapKeys g n)
      simp only [e]
      exact integrable_const _
  refine hdom.mono' ((Complex.measurable_ofReal.comp hfm).mul
    ((measurable_cepsMidF eps (n + 1) hΨ).comp hU)).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf.nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_cepsMidF_le eps (n + 1) hM _) (hf.nonneg _)

theorem exists_succ_of_two_mul_lt {eps : ℝ} (heps : 0 < eps) {L : ℕ} (hL : 2 * eps < L) :
    ∃ n, L = n + 1 := ⟨L - 1, by
  have : (0 : ℝ) < L := by linarith
  have : 0 < L := by exact_mod_cast this
  omega⟩

/-- `μ ↦ k_L^{(μ)}(0, l) Ψ(μ)` is integrable. -/
theorem CepsGapDensity.integrable_cepsBridgeMul (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {L : ℕ} (hL : 2 * eps < L) {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) {M : ℝ}
    (hM : ∀ μ, ‖Ψ μ‖ ≤ M) : Integrable (cepsBridgeMul ν f eps L Ψ) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_two_mul_lt heps hL
  set c : ℝ := ((n + 1 : ℕ) : ℝ) - 2 * eps with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have h1 := (hf.integrable_midShift eps n hΨ hM).integral_prod_right
  simp only [integral_midShift ν f eps n hc0.ne' Ψ] at h1
  have h2 := (h1.comp_mul_left' hc0.ne').comp_add_right 1
  refine h2.congr (Eventually.of_forall fun μ => ?_)
  simp only
  congr 1
  rw [← hc, mul_div_cancel_left₀ _ hc0.ne']
  ring

theorem CepsGapDensity.integral_midAlive_mul (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 < eps) {L : ℕ} (hL : 2 * eps < L) {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) {M : ℝ}
    (hM : ∀ μ, ‖Ψ μ‖ ≤ M) :
    ∫ h, (cepsMidAlive eps L h : ℂ) * Ψ (cepsMidDrift eps L h) ∂(iidLaw ν) =
      (((L : ℝ) - 2 * eps : ℝ) : ℂ) * ∫ μ in Ioi (-1 : ℝ),
        (cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L : ℂ) * Ψ μ := by
  obtain ⟨n, rfl⟩ := exists_succ_of_two_mul_lt heps hL
  set c : ℝ := ((n + 1 : ℕ) : ℝ) - 2 * eps with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hshift := surv_integral_wordLaw_shift ν ν ∅ (m := n) (Finset.notMem_empty n) hf.measurable
    hf.nonneg hf.eq (R := fun g => gapKeys g n) (rawAsm_measurable_gapKeys n)
    (measurable_cepsMidF eps (n + 1) hΨ) (norm_cepsMidF_le eps (n + 1) hM)
  simp only [wordLaw_self] at hshift
  change ∫ h, cepsMidF eps (n + 1) Ψ h ∂(iidLaw ν) = _
  rw [hshift]
  simp_rw [integral_midShift ν f eps n hc0.ne' Ψ]
  have hcov : ∫ x, cepsBridgeMul ν f eps (n + 1) Ψ (x / c - 1) =
      (c : ℂ) * ∫ μ, cepsBridgeMul ν f eps (n + 1) Ψ μ := by
    have h1 := Measure.integral_comp_div (fun y => cepsBridgeMul ν f eps (n + 1) Ψ (y - 1)) c
    rw [h1, integral_sub_right_eq_self (fun y => cepsBridgeMul ν f eps (n + 1) Ψ y) 1,
      abs_of_pos hc0, Complex.real_smul]
  rw [hcov, setIntegral_eq_integral_of_forall_compl_eq_zero fun μ hμ => ?_]
  · rfl
  have hμ' : μ ≤ -1 := not_lt.1 hμ
  simp only [hf.cepsBridgeDens_eq_zero_of_le heps hμ' n, Complex.ofReal_zero, zero_mul]

/-! ## The certificate integral -/

/-- **The exact integral of one certificate** (analytic-response (7) in drift units). -/
theorem CepsGapDensity.integral_cert_eq (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    {i L r : ℕ} (hL : 2 * eps < L) {t : ℂ} (ht : 0 ≤ t.re) :
    ∫ g, ({g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g) * Complex.exp (-t * gapKeys g (i + L + r)) ∂(iidLaw ν) =
      (((L : ℝ) - 2 * eps : ℝ) : ℂ) * ∫ μ in Ioi (-1 : ℝ),
        Complex.exp (-t * (((1 + μ) * ((i + L + r : ℕ) : ℝ) - 2 * eps * (1 + μ) : ℝ) : ℂ)) *
          cepsStripTerm ν t μ (2 * eps * (1 + μ)) i * cepsStripTerm ν t μ (2 * eps * (1 + μ)) r *
          (cepsBridgeDens ν f μ (2 * eps * (1 + μ)) L : ℂ) := by
  have hk : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  rw [hf.integral_cert_eq_perm heps hL t, integral_cepsPermInt ν heps hL ht,
    hf.integral_midAlive_mul heps hL (measurable_cepsOuterMean ν t eps i r (i + L + r))
      (norm_cepsOuterMean_le_one ν ht heps hk)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun μ _ => ?_
  rw [cepsOuterMean_eq]
  ring

end

end PGM
