import PLAStochastic.Index.GEP.Kernel.Row.ClassUniform
import PLAStochastic.Index.GEP.Kernel.BV.LongKernel

/-!
# WP4 kernel rows: connection to the BV decomposition of the killed operator

Source: `influence-lipschitz.md` §3, (long): for a long row `q_n(b, ·)`, run about a third of the
time to obtain the `L²` bound, then apply the dissipation–BV proposition to the remaining steps.

This file connects the pointwise kernel `krDens` with the `L²` operator `kBVKilledL2` of the
`GEPKernelBV*` modules (developed separately, compiled):

* `kStep_iterate_ofReal`: the complex iterate `(kStep)^[n]` of a real function is the coercion of
  `krRow`;
* `krRow_toLp`: `(kBVKilledL2 J)^n (toLp (1_J φ)) = toLp (krRow n φ)` in `L²`;
* `krDens_shift_eq_krRow`: `q_{m+1+k}(b, ·) = P̃^k q_{m+1}(b, ·)` with the reversed step
  `P̃ = krStep (-β) (-a)` (pointwise, from `krDens_add` and `krDens_symm`);
* `krDens_long_decomposition`: for `k ≥ 8`, `toLp (q_{m+1+k}(b, ·)) = G + R` with `G` having a
  BV representative supported in `[0, w]` of variation
  `≤ 8π√w (1 + 1/(1 - √(1 - c))) √(e^{-κ ⌊k/4⌋ / w²} ‖q_{m+1}(b,·)‖₂² / (c ⌊k/4⌋))` and
  `‖R‖₂ ≤ √(1 - c)^{⌊k/2⌋} √(…)`, where `c = killCnu D vlo vhi`, `κ = krKappa D vlo vhi`;
* `krDens_long_decomposition_bdry`: the same from a boundary point with the medium-time `L²`
  bound `‖q_{m+1}(b,·)‖₂² ≤ C₂ (1 + A)² / ((m+1) √(m+1))` inserted (`m + 1 ≤ w²`).

The pointwise (Lipschitz / sup) form, the summation over `n`, and the endpoint traces of the
(long) display are in `GEPKernelRowLong`; the exponentially weighted versions in
`GEPKernelRowWeighted`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## The complex iterate of a real function -/

theorem kStep_iterate_ofReal (ρ : Measure ℝ) (n : ℕ) (φ : ℝ → ℝ) :
    (kStep J ρ β a)^[n] (fun x => ((J.indicator φ x : ℝ) : ℂ)) =
      fun y => (krRow J ρ β a n φ y : ℂ) := by
  induction n with
  | zero => funext y; simp [krRow_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, krRow_succ]
    funext y
    exact kStep_ofReal ρ _ y

/-! ## Square integrability of bounded functions supported in `J` -/

theorem kr_memLp_two_ofReal {u : ℝ → ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ J → u y = 0) {M : ℝ} (hM : ∀ y, |u y| ≤ M) :
    MemLp (fun y => (u y : ℂ)) 2 := by
  have hm : AEStronglyMeasurable (fun y => (u y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hu : Measurable fun y => (u y : ℂ)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine (kr_integrable_sq_of_bdd hJ hJfin hu hsupp hM).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem kr_integrable_ofReal {u : ℝ → ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ J → u y = 0) {M : ℝ} (hM : ∀ y, |u y| ≤ M) :
    Integrable (fun y => (u y : ℂ)) :=
  (kr_integrable_of_bdd_support hJ hJfin hu hsupp hM).ofReal

theorem kBVNormSq_ofReal (u : ℝ → ℝ) : kBVNormSq (fun y => (u y : ℂ)) = ∫ y, u y ^ 2 := by
  unfold kBVNormSq
  congr 1
  funext y
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The `L²` bridge -/

/-- **Bridge**: `(kBVKilledL2 J)^n (toLp (1_J φ)) = toLp (krRow n φ)` for bounded measurable `φ`. -/
theorem krRow_toLp (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤) (β a : ℝ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (n : ℕ)
    (h0 : MemLp (fun x => ((J.indicator φ x : ℝ) : ℂ)) 2)
    (hn : MemLp (fun y => (krRow J (ν : Measure ℝ) β a n φ y : ℂ)) 2) :
    ((kBVKilledL2 J hJ (ν : Measure ℝ) β a) ^ n) (h0.toLp _) = hn.toLp _ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hind : Measurable (J.indicator φ) := hφ.indicator hJ
  have hindM : ∀ y, |J.indicator φ y| ≤ M := fun y => by
    by_cases hy : y ∈ J
    · rw [indicator_of_mem hy]; exact hM y
    · rw [indicator_of_notMem hy, abs_zero]; exact hM0
  have hu : Measurable (fun x => ((J.indicator φ x : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hind
  have h1 : Integrable (fun x => ((J.indicator φ x : ℝ) : ℂ)) :=
    kr_integrable_ofReal hJ hJfin hind (fun _ hy => indicator_of_notMem hy _) hindM
  rw [kBVKilledL2_pow_toLp hJ (ν : Measure ℝ) β a hu h1 h0
    (fun _ hy => by simp [indicator_of_notMem hy]) n]
  exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (kStep_iterate_ofReal _ n φ))

/-! ## The shifted kernel as a reversed row -/

/-- `q_{m+1+k}(b, ·) = P̃^k q_{m+1}(b, ·)`, `P̃ = krStep (-β) (-a)`, pointwise. -/
theorem krDens_shift_eq_krRow (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m k : ℕ) (b : ℝ) :
    (fun z => krDens J ν f β a (m + 1 + k) b z) =
      krRow J (ν : Measure ℝ) (-β) (-a) k (fun y => krDens J ν f β a (m + 1) b y) := by
  funext z
  cases k with
  | zero =>
    rw [Nat.add_zero, krRow_zero]
    by_cases hz : z ∈ J
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, krDens_eq_zero_of_right_notMem ν hz]
  | succ k =>
    rw [krDens_add ν hJ hJfin hf hf0 hfD hν ha m k b z,
      krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν (neg_ne_zero.2 ha) k
        (measurable_krDens_right ν hJ hf β a (m + 1) b) (M := D / |a|)
        (fun y => abs_krDens_le ν hf0 hfD (m + 1) b y) z]
    congr 1
    funext y
    rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha k y z, mul_comm]

/-! ## The long decomposition of the actual kernel -/

/-- **(long), per row**: for `k ≥ 8`, `toLp (q_{m+1+k}(b, ·)) = G + R` with a BV representative of
`G` supported in `[0, w]` and an `L²`-small `R`, both controlled by `‖q_{m+1}(b, ·)‖₂²`. -/
theorem krDens_long_decomposition {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (hk : 8 ≤ k) (b : ℝ) :
    ∃ G R : KernelL2, ∃ hq : MemLp (fun z => (krDens (Icc 0 w) ν f β a' (m + 1 + k) b z : ℂ)) 2,
      hq.toLp _ = G + R ∧
      kBVHasRep (Icc 0 w)
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
          Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
            (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2) /
              (killCnu D vlo vhi * (k / 4 : ℕ)))) G ∧
      ‖R‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ (k / 2) *
        Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
          (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2) /
            (killCnu D vlo vhi * (k / 4 : ℕ))) := by
  have hJ := H.hJ
  have hJfin := H.hJfin
  -- the input row `u = q_{m+1}(b, ·)`
  set u : ℝ → ℝ := fun y => krDens (Icc 0 w) ν f β a' (m + 1) b y with hu_def
  have hu : Measurable u := measurable_krDens_right ν hJ H.hf β a' (m + 1) b
  have husupp : ∀ y, y ∉ Icc 0 w → u y = 0 := fun _ hy => krDens_eq_zero_of_right_notMem ν hy _ _
  have huM : ∀ y, |u y| ≤ D / |a'| := fun y => abs_krDens_le ν H.hf0 H.hfD (m + 1) b y
  have h2 : MemLp (fun y => (u y : ℂ)) 2 := kr_memLp_two_ofReal hJ hJfin hu husupp huM
  have huc : Measurable (fun y => (u y : ℂ)) := Complex.measurable_ofReal.comp hu
  have hsuppc : ∀ x, x ∉ Icc (0 : ℝ) (0 + w) → (u x : ℂ) = 0 := fun x hx => by
    rw [zero_add] at hx
    rw [husupp x hx, Complex.ofReal_zero]
  have ha' : 1 / 2 ≤ |-a'| := by rw [abs_neg]; exact H.ha₁'
  obtain ⟨G, R, hGR, hG, hR⟩ := kBV_regLaw_n_decomposition H.hD H.hθ H.hvlo H.hν (-β) (α := 0)
    ha' H.hw huc h2 hsuppc k hk
  rw [zero_add] at hGR hG
  -- identify the operator iterate with the shifted kernel
  have hq : MemLp (fun z => (krDens (Icc 0 w) ν f β a' (m + 1 + k) b z : ℂ)) 2 :=
    kr_memLp_two_ofReal hJ hJfin (measurable_krDens_right ν hJ H.hf β a' _ b)
      (fun _ hz => krDens_eq_zero_of_right_notMem ν hz _ _) (abs_krDens_le ν H.hf0 H.hfD _ b)
  have hind : (fun y => (u y : ℂ)) = fun x => (((Icc 0 w).indicator u x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) w
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, husupp x hx]
  have h0 : MemLp (fun x => (((Icc 0 w).indicator u x : ℝ) : ℂ)) 2 :=
    MemLp.ae_eq (Filter.EventuallyEq.of_eq hind) h2
  have hshift : ∀ z, krDens (Icc 0 w) ν f β a' (m + 1 + k) b z =
      krRow (Icc 0 w) (ν : Measure ℝ) (-β) (-a') k u z := fun z =>
    congrFun (krDens_shift_eq_krRow ν hJ hJfin H.hf H.hf0 H.hfD H.hνf H.ha' m k b) z
  have hshift' : (fun z => (krDens (Icc 0 w) ν f β a' (m + 1 + k) b z : ℂ)) =
      fun z => (krRow (Icc 0 w) (ν : Measure ℝ) (-β) (-a') k u z : ℂ) := by
    funext z
    rw [hshift z]
  have hn : MemLp (fun z => (krRow (Icc 0 w) (ν : Measure ℝ) (-β) (-a') k u z : ℂ)) 2 :=
    MemLp.ae_eq (Filter.EventuallyEq.of_eq hshift') hq
  have hbridge := krRow_toLp ν hJ hJfin (-β) (-a') hu huM k h0 hn
  have h0eq : h2.toLp (fun y => (u y : ℂ)) = h0.toLp _ :=
    MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hind)
  refine ⟨G, R, hq, ?_, ?_, ?_⟩
  · rw [← hGR, h0eq, hbridge]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hshift')
  · rw [kBVNormSq_ofReal] at hG
    exact hG
  · rw [kBVNormSq_ofReal] at hR
    exact hR

/-- **(long), per boundary row**: the decomposition with the medium-time `L²` bound inserted.
For `m + 1 ≤ w²`, `k ≥ 8`, and `Λ := 8π√w (1 + 1/(1 - √(1 - c)))`,
`V(G) ≤ Λ √(C₂ (1 + A)² / ((m+1)√(m+1) · c ⌊k/4⌋))` and `‖R‖ ≤ √(1-c)^{⌊k/2⌋} √(…)`. -/
theorem krDens_long_decomposition_bdry {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (m k : ℕ)
    (hk : 8 ≤ k) (hmw : ((m + 1 : ℕ) : ℝ) ≤ w ^ 2) :
    ∃ G R : KernelL2, ∃ hq : MemLp (fun z => (krDens (Icc 0 w) ν f β a' (m + 1 + k) b z : ℂ)) 2,
      hq.toLp _ = G + R ∧
      kBVHasRep (Icc 0 w)
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
          Real.sqrt (krC₂ D K L * (1 + A) ^ 2 / (((m + 1 : ℕ) : ℝ) * Real.sqrt (m + 1 : ℕ)) /
            (killCnu D vlo vhi * (k / 4 : ℕ)))) G ∧
      ‖R‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ (k / 2) *
        Real.sqrt (krC₂ D K L * (1 + A) ^ 2 / (((m + 1 : ℕ) : ℝ) * Real.sqrt (m + 1 : ℕ)) /
          (killCnu D vlo vhi * (k / 4 : ℕ))) := by
  obtain ⟨G, R, hq, hGR, hG, hR⟩ := krDens_long_decomposition ν H m k hk b
  have hc := killCnu_pos H.hD H.hvlo H.hvhi
  have hk4 : (0 : ℝ) < (k / 4 : ℕ) := by exact_mod_cast (by omega : 0 < k / 4)
  have hL2 := integral_sq_krDens_bdry_medium ν H hb (n := m + 1) (by omega) hmw
  have hexp : Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := krKappa_pos H.hD H.hvlo H.hvhi
    have : 0 ≤ krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2 := by positivity
    linarith
  have hint0 : 0 ≤ ∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hmono : Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
      (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2) / (killCnu D vlo vhi * (k / 4 : ℕ)) ≤
      krC₂ D K L * (1 + A) ^ 2 / (((m + 1 : ℕ) : ℝ) * Real.sqrt (m + 1 : ℕ)) /
        (killCnu D vlo vhi * (k / 4 : ℕ)) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc _ ≤ 1 * ∫ y, krDens (Icc 0 w) ν f β a' (m + 1) b y ^ 2 :=
          mul_le_mul_of_nonneg_right hexp hint0
      _ = _ := one_mul _
      _ ≤ _ := hL2
  have hsq := Real.sqrt_le_sqrt hmono
  have hΛ : 0 ≤ 8 * Real.pi * Real.sqrt w +
      8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi)) := by
    have hρ1 := kBVHighStepL2_regLaw_factor_lt_one H.hD H.hvlo (H.hν.var_ge.trans H.hν.var_le)
    have : 0 < 1 - Real.sqrt (1 - killCnu D vlo vhi) := by linarith
    positivity
  refine ⟨G, R, hq, hGR, kBVHasRep_mono hG (mul_le_mul_of_nonneg_left hsq hΛ), hR.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

end

end PGM
