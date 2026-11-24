import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments

/-!
# WP2: the joint stopping bound (`density-tail.md` §4)

For a law `ρ` of the moment class with an exponential moment, and any nonincreasing local
bounds `F n` of `S_n` (`n ≥ 1`), the joint stopping measure `ν_t(A) = P(T = t, S_t ∈ A)`
satisfies, for `t > 2 eps` (so `t ≥ 17` once `eps ≥ 8`; `ν_t = 0` otherwise by
`stopMeas_eq_zero`), with `r = ⌊t/2⌋`, `E = eps²`,

* early stop (`density-tail.md` (4.2); `prop:transfer`): through `cyclicCount_pos_walk`,
  `measure_block_inter_le` on each half, and `iid_maximal_bernstein` at `x = eps/6`
  (`min(x²/s, x) ≥ E/(36 t)` since `t > 2 eps`):
  `ν_t ≤ (8/t) e^{-(c/36) E/t} F(r) dx`, `c = bernsteinRate θ₁ B₁`;
* long time (`density-tail.md` (4.4), the new step): through `cyclicCount_pos_block`,
  `measure_block_inter_le` with `exists_prefix_set_lt_gapSegLen`, `measure_block_shift` and
  `gapSegLen_tail` with `m = ⌊t/8⌋ ≥ t/16`:
  `ν_t ≤ (32/t)(72/71) e^{-(λ/16) t/E} F(r) dx`, `λ = tailRate · vmin`;
* spatial localisation (`density-tail.md` (4.5)): through `stopMeas_le_cyclic` with `E = univ`,
  `measure_gapKeys_le_spatial` and `iid_endpoint_bernstein`
  (`min(d²/n, d) ≥ Q_t(x)/4` for `d = |x - t|/2`, `n ≤ t`):
  `ν_t ≤ (8/t) e^{-(c/16) Q_t(x)} F(r) dx`;

and the three combine (`le_withDensity_min`, `min(e^{-u}, e^{-v}, e^{-w}) ≤ e^{-(u+v+w)/3}`)
into `stopMeas_le_kernel`:
`ν_t ≤ (C₁/t) F(r) exp(-γ₁ (E/t + t/E + Q_t(x))) dx`, with `C₁, γ₁` depending only on
`(vmin, θ₁, B₁)` and the threshold on `(b, β, vmin, θ₁, B₁)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Two density bounds give their minimum. -/
theorem le_withDensity_min {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (h1 : μ ≤ volume.withDensity f) (h2 : μ ≤ volume.withDensity g) :
    μ ≤ volume.withDensity fun x => min (f x) (g x) := by
  rw [Measure.le_iff] at h1 h2 ⊢
  intro A hA
  have hB : MeasurableSet {x | f x ≤ g x} := measurableSet_le hf hg
  rw [← measure_inter_add_sdiff A hB, withDensity_apply _ hA,
    ← lintegral_inter_add_sdiff _ A hB]
  refine add_le_add ?_ ?_
  · calc μ (A ∩ {x | f x ≤ g x}) ≤ volume.withDensity f (A ∩ {x | f x ≤ g x}) :=
          h1 _ (hA.inter hB)
      _ = ∫⁻ x in A ∩ {x | f x ≤ g x}, f x := withDensity_apply _ (hA.inter hB)
      _ = _ := setLIntegral_congr_fun (hA.inter hB) fun x hx => (min_eq_left hx.2).symm
  · calc μ (A \ {x | f x ≤ g x}) ≤ volume.withDensity g (A \ {x | f x ≤ g x}) :=
          h2 _ (hA.diff hB)
      _ = ∫⁻ x in A \ {x | f x ≤ g x}, g x := withDensity_apply _ (hA.diff hB)
      _ = _ := setLIntegral_congr_fun (hA.diff hB) fun x hx =>
          (min_eq_right (not_le.1 hx.2).le).symm

/-- A local bound is monotone in its constant. -/
private theorem locBd_mono_joint {D D' : ℝ} {μ : Measure ℝ} (h : LocBd D μ) (hDD : D ≤ D') :
    LocBd D' μ := fun A hA =>
  (h A hA).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDD) _)

/-- A uniform bound on sets is a constant density bound. -/
private theorem le_withDensity_const_joint {μ : Measure ℝ} {c : ℝ}
    (h : ∀ A, MeasurableSet A → μ A ≤ ENNReal.ofReal c * volume A) :
    μ ≤ volume.withDensity fun _ => ENNReal.ofReal c := by
  rw [withDensity_const, Measure.le_iff]
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul]
  exact h A hA

/-- `2 / t` as the extended real `ofReal (2 / t)`. -/
private theorem two_div_natCast_joint {t : ℕ} (ht : 0 < t) :
    (2 : ℝ≥0∞) / (t : ℝ≥0∞) = ENNReal.ofReal (2 / t) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast ht), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_natCast]

/-- A real bound on a probability gives the extended-real bound. -/
private theorem measure_le_ofReal_joint {μ : Measure (ℕ → ℝ)} [IsFiniteMeasure μ]
    {s : Set (ℕ → ℝ)} {x : ℝ} (h : μ.real s ≤ x) : μ s ≤ ENNReal.ofReal x := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- The maximal Bernstein bound at `x = eps/6` for a walk of length `s ≤ t`, `t > 2 eps`. -/
private theorem walk_prob_le_joint {θ₁ B₁ eps : ℝ} (hθ₁ : 0 < θ₁) (heps : 0 ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1)
    (hexp : ExpMom θ₁ B₁ ρ) {t s : ℕ} (ht : 2 * eps < t) (hs : 1 ≤ s) (hst : s ≤ t)
    (heps0 : 0 < eps) :
    iidLaw ρ {g | ∃ j ≤ s, eps / 6 < |gapKeys g j - j|} ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ / 36) * (eps ^ 2 / t))) := by
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc0 : 0 < bernsteinRate θ₁ B₁ := bernsteinRate_pos hθ₁ hB₁
  refine measure_le_ofReal_joint ((iid_maximal_bernstein hθ₁ hpos hmean hexp s hs
    (by positivity : 0 < eps / 6)).trans ?_)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have htpos : (0 : ℝ) < t := by linarith
  have hmin : eps ^ 2 / (36 * t) ≤ min ((eps / 6) ^ 2 / s) (eps / 6) := by
    refine le_min ?_ ?_
    · rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [mul_le_mul_of_nonneg_left hst' (sq_nonneg eps)]
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have e : -(bernsteinRate θ₁ B₁ / 36) * (eps ^ 2 / t) =
      -(bernsteinRate θ₁ B₁ * (eps ^ 2 / (36 * t))) := by
    field_simp
  rw [e, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left hmin hc0.le

/-- **Early-stop bound** (`density-tail.md` (4.2)). -/
theorem stopMeas_le_early {b β vmin θ₁ B₁ eps : ℝ} (hθ₁ : 0 < θ₁) (heps : 8 ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) (hexp : ExpMom θ₁ B₁ ρ)
    {F : ℕ → ℝ} (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    stopMeas eps ρ t ≤ volume.withDensity fun _ =>
      ENNReal.ofReal (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 36) * (eps ^ 2 / t)) *
        F (t / 2)) := by
  classical
  have heps0 : 0 ≤ eps := by linarith
  have hepspos : 0 < eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  set r := t / 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrt : r ≤ t - r := by omega
  set ee := Real.exp (-(bernsteinRate θ₁ B₁ / 36) * (eps ^ 2 / t)) with hee
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  -- the two halves
  obtain ⟨E₁, hE₁, hE₁iff⟩ := exists_prefix_set_walk (eps / 6) r
  obtain ⟨E₂, hE₂, hE₂iff⟩ := exists_prefix_set_walk (eps / 6) (t - r)
  set S₁ : Set (ℕ → ℝ) := {g | (fun i : Fin r => g i) ∈ E₁} with hS₁def
  set S₂ : Set (ℕ → ℝ) := {g | (fun i : Fin (t - r) => g (r + i)) ∈ E₂} with hS₂def
  have hS₁ : MeasurableSet S₁ :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE₁
  have hS₂ : MeasurableSet S₂ :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE₂
  have hP₁ : iidLaw ρ S₁ ≤ ENNReal.ofReal (2 * ee) := by
    have e : S₁ = {g | ∃ j ≤ r, eps / 6 < |gapKeys g j - j|} := by
      ext g
      exact (hE₁iff g).symm
    rw [e]
    exact walk_prob_le_joint hθ₁ heps0 hρ.pos hρ.mean hexp ht hr1 (by omega) hepspos
  have hP₂ : iidLaw ρ S₂ ≤ ENNReal.ofReal (2 * ee) := by
    rw [hS₂def, measure_block_shift ρ r (t - r) hE₂]
    have e : {g : ℕ → ℝ | (fun i : Fin (t - r) => g i) ∈ E₂} =
        {g | ∃ j ≤ t - r, eps / 6 < |gapKeys g j - j|} := by
      ext g
      exact (hE₂iff g).symm
    rw [e]
    exact walk_prob_le_joint hθ₁ heps0 hρ.pos hρ.mean hexp ht (by omega) (by omega) hepspos
  refine le_withDensity_const_joint fun A hA => ?_
  have hcyc := stopMeas_le_cyclic hρ.pos heps0 htpos (hS₁.union hS₂) (fun g _ h => by
    rcases cyclicCount_pos_walk (r := r) (by omega) h with h1 | h2
    · exact Or.inl ((hE₁iff g).1 h1)
    · exact Or.inr ((hE₂iff (fun i => g (r + i))).1 h2)) hA
  have h₁ := measure_block_inter_le ρ (u := 0) (m := r) (t := t) (by omega) hE₁
    (hF (t - r) (by omega)) hA
  simp only [zero_add] at h₁
  have h₂ := measure_block_inter_le ρ (u := r) (m := t - r) (t := t) (by omega) hE₂
    (c := F r) (by rw [show t - (t - r) = r by omega]; exact hF r hr1) hA
  have hFtr : ENNReal.ofReal (F (t - r)) ≤ ENNReal.ofReal (F r) :=
    ENNReal.ofReal_le_ofReal (hFa r (t - r) hr1 hrt)
  calc stopMeas eps ρ t A ≤ 2 / (t : ℝ≥0∞) * iidLaw ρ ((S₁ ∪ S₂) ∩ {g | gapKeys g t ∈ A}) :=
        hcyc
    _ ≤ 2 / (t : ℝ≥0∞) * (iidLaw ρ (S₁ ∩ {g | gapKeys g t ∈ A}) +
          iidLaw ρ (S₂ ∩ {g | gapKeys g t ∈ A})) := by
        rw [Set.union_inter_distrib_right]
        gcongr
        exact measure_union_le _ _
    _ ≤ 2 / (t : ℝ≥0∞) * (ENNReal.ofReal (2 * ee) * (ENNReal.ofReal (F r) * volume A) +
          ENNReal.ofReal (2 * ee) * (ENNReal.ofReal (F r) * volume A)) := by
        gcongr
        · exact h₁.trans (mul_le_mul' hP₁ (mul_le_mul_left hFtr _))
        · exact h₂.trans (mul_le_mul_left hP₂ _)
    _ = ENNReal.ofReal (2 / t) * ENNReal.ofReal (2 * ee) * ENNReal.ofReal (F r) * 2 *
          volume A := by
        rw [two_div_natCast_joint htpos]
        ring
    _ = ENNReal.ofReal (8 / t * ee * F r) * volume A := by
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **Long-time bound** (`density-tail.md` (4.3)–(4.4)). -/
theorem stopMeas_le_long {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps8 : 8 ≤ eps)
    (heps : epsZero b β ≤ eps) {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ)
    {F : ℕ → ℝ} (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    stopMeas eps ρ t ≤ volume.withDensity fun _ =>
      ENNReal.ofReal (32 / t * (72 / 71) *
        Real.exp (-(tailRate * vmin / 16) * (t / eps ^ 2)) * F (t / 2)) := by
  classical
  have heps0 : 0 ≤ eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  set m := t / 8 with hm
  set r := t / 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrm : r ≤ t - m := by omega
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  set PP := 72 / 71 * Real.exp (-(tailRate * vmin / 16) * (t / eps ^ 2)) with hPP
  have hPP0 : 0 ≤ PP := by positivity
  obtain ⟨E', hE', hE'iff⟩ := exists_prefix_set_lt_gapSegLen eps m
  set J := (Finset.range 16).filter (fun j => (j + 1) * m ≤ t) with hJ
  set S : ℕ → Set (ℕ → ℝ) := fun j => {g | (fun i : Fin m => g (j * m + i)) ∈ E'} with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE'
  have hU : MeasurableSet (⋃ j ∈ J, S j) := Finset.measurableSet_biUnion J fun j _ => hSm j
  have hsub : ∀ g : ℕ → ℝ, (∀ i, 0 < g i) → 1 ≤ cyclicCount eps (fun i : Fin t => g i) →
      g ∈ ⋃ j ∈ J, S j := by
    intro g hg h
    obtain ⟨j, hj16, hjt, hjT⟩ := cyclicCount_pos_block heps0 (by omega) hg h
    exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj16, hjt⟩,
      (hE'iff _).1 hjT⟩
  -- the probability of a feasible block
  have hPS : ∀ j, iidLaw ρ (S j) ≤ ENNReal.ofReal PP := by
    intro j
    rw [hSdef, measure_block_shift ρ (j * m) m hE']
    have e : {g : ℕ → ℝ | (fun i : Fin m => g i) ∈ E'} = {g | (m : ℕ∞) < gapSegLen eps g} := by
      ext g
      exact (hE'iff g).symm
    rw [e]
    refine (gapSegLen_tail hvmin0 heps hρ m).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hPP]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hE : 0 < eps ^ 2 := by positivity
    have hlam : 0 < tailRate * vmin := mul_pos tailRate_pos hvmin0
    have h16 : (t : ℝ) ≤ 16 * m := by exact_mod_cast (show t ≤ 16 * m by omega)
    have hkey : (tailRate * vmin / 16) * (t / eps ^ 2) ≤ (tailRate * vmin) * m / eps ^ 2 := by
      calc (tailRate * vmin / 16) * (t / eps ^ 2) = (tailRate * vmin) * (t / 16) / eps ^ 2 := by
            ring
        _ ≤ (tailRate * vmin) * m / eps ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hlam.le) hE.le
    rw [neg_mul, neg_mul, neg_div]
    exact neg_le_neg hkey
  -- the block factorisation
  have hblock : ∀ j ∈ J, ∀ A, MeasurableSet A →
      iidLaw ρ (S j ∩ {g | gapKeys g t ∈ A}) ≤
        ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A) := by
    intro j hj A hA
    have hjt : (j + 1) * m ≤ t := (Finset.mem_filter.1 hj).2
    have hjm : j * m + m ≤ t := by rw [add_one_mul] at hjt; exact hjt
    refine (measure_block_inter_le ρ (u := j * m) (m := m) (t := t) hjm hE'
      (hF (t - m) (by omega)) hA).trans ?_
    exact mul_le_mul' (hPS j) (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (hFa r (t - m) hr1 hrm)) _)
  have hJcard : (J.card : ℝ≥0∞) ≤ 16 := by
    have : J.card ≤ 16 := (Finset.card_filter_le _ _).trans (Finset.card_range 16).le
    exact_mod_cast this
  refine le_withDensity_const_joint fun A hA => ?_
  have hcyc := stopMeas_le_cyclic hρ.pos heps0 htpos hU hsub hA
  calc stopMeas eps ρ t A
      ≤ 2 / (t : ℝ≥0∞) * iidLaw ρ ((⋃ j ∈ J, S j) ∩ {g | gapKeys g t ∈ A}) := hcyc
    _ ≤ 2 / (t : ℝ≥0∞) * ∑ j ∈ J, iidLaw ρ (S j ∩ {g | gapKeys g t ∈ A}) := by
        gcongr
        rw [Set.iUnion₂_inter]
        exact measure_biUnion_finset_le J _
    _ ≤ 2 / (t : ℝ≥0∞) * ∑ j ∈ J, ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A) := by
        gcongr with j hj
        exact hblock j hj A hA
    _ ≤ 2 / (t : ℝ≥0∞) * (16 * (ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
    _ = ENNReal.ofReal (2 / t) * ENNReal.ofReal PP * ENNReal.ofReal (F r) * 16 *
          volume A := by
        rw [two_div_natCast_joint htpos]
        ring
    _ = ENNReal.ofReal (32 / t * (72 / 71) *
          Real.exp (-(tailRate * vmin / 16) * (t / eps ^ 2)) * F r) * volume A := by
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hPP]
        ring

/-- **Spatial bound** (`density-tail.md` (4.5)). -/
theorem stopMeas_le_spatial {b β vmin θ₁ B₁ eps : ℝ} (hθ₁ : 0 < θ₁) (heps : 8 ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) (hexp : ExpMom θ₁ B₁ ρ)
    {F : ℕ → ℝ} (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    stopMeas eps ρ t ≤ volume.withDensity fun x =>
      ENNReal.ofReal (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x) *
        F (t / 2)) := by
  have heps0 : 0 ≤ eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  have htpos' : (0 : ℝ) < t := by exact_mod_cast htpos
  set r := t / 2 with hr
  set s := t - t / 2 with hs
  have hr1 : 1 ≤ r := by omega
  have hrs : r ≤ s := by omega
  have hs1 : 1 ≤ s := by omega
  have hrst : r + s = t := by omega
  set c := bernsteinRate θ₁ B₁ with hc
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc0 : 0 < c := bernsteinRate_pos hθ₁ hB₁
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  have hFs : F s ≤ F r := hFa r s hr1 hrs
  -- the endpoint bound of either half
  have hb : ∀ n : ℕ, 1 ≤ n → n ≤ t → ∀ x : ℝ,
      (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g n - n|} ≤
        2 * Real.exp (-(c / 16) * qdev t x) := by
    intro n hn1 hnt x
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnt' : (n : ℝ) ≤ t := by exact_mod_cast hnt
    refine (iid_endpoint_bernstein hθ₁ hρ.pos hρ.mean hexp n hn1 (by positivity)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hq1 : qdev t x ≤ (x - t) ^ 2 / t := min_le_left _ _
    have hq2 : qdev t x ≤ |x - t| := min_le_right _ _
    have hm : qdev t x / 4 ≤ min ((|x - t| / 2) ^ 2 / n) (|x - t| / 2) := by
      refine le_min ?_ ?_
      · have e : (|x - t| / 2) ^ 2 / n = (x - t) ^ 2 / (4 * n) := by
          rw [div_pow, sq_abs]
          ring
        rw [e]
        calc qdev t x / 4 ≤ (x - t) ^ 2 / t / 4 := by linarith
          _ = (x - t) ^ 2 / (4 * t) := by ring
          _ ≤ (x - t) ^ 2 / (4 * n) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      · have := abs_nonneg (x - (t : ℝ))
        linarith
    have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ c / 4)
    linarith
  rw [Measure.le_iff]
  intro A hA
  have h1 := stopMeas_le_cyclic hρ.pos heps0 htpos MeasurableSet.univ
    (fun g _ _ => Set.mem_univ g) hA
  rw [Set.univ_inter] at h1
  have h2 := measure_gapKeys_le_spatial ρ (r := r) (s := s) (hF r hr1) (hF s hs1) hA
  rw [hrst] at h2
  have hpt : ∀ x : ℝ, ENNReal.ofReal
      (F s * (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g r - r|} +
        F r * (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g s - s|}) ≤
      ENNReal.ofReal (4 * F r * Real.exp (-(c / 16) * qdev t x)) := by
    intro x
    refine ENNReal.ofReal_le_ofReal ?_
    have p1 := hb r hr1 (by omega) x
    have p2 := hb s hs1 (by omega) x
    have hP1 : 0 ≤ (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g r - r|} := measureReal_nonneg
    have q1 := mul_le_mul_of_nonneg_right hFs hP1
    have q2 := mul_le_mul_of_nonneg_left p1 hFr0
    have q3 := mul_le_mul_of_nonneg_left p2 hFr0
    linarith
  rw [withDensity_apply _ hA]
  calc stopMeas eps ρ t A ≤ 2 / (t : ℝ≥0∞) * iidLaw ρ {g | gapKeys g t ∈ A} := h1
    _ ≤ 2 / (t : ℝ≥0∞) * ∫⁻ x in A, ENNReal.ofReal (4 * F r * Real.exp (-(c / 16) * qdev t x)) := by
        gcongr
        exact h2.trans (lintegral_mono hpt)
    _ = ∫⁻ x in A, ENNReal.ofReal (2 / t) *
          ENNReal.ofReal (4 * F r * Real.exp (-(c / 16) * qdev t x)) := by
        rw [two_div_natCast_joint htpos, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x in A, ENNReal.ofReal (8 / t * Real.exp (-(c / 16) * qdev t x) * F r) := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The joint stopping bound** (`density-tail.md` (4.6)). -/
theorem stopMeas_le_kernel {b β vmin θ₁ B₁ : ℝ} (hvmin0 : 0 < vmin) (hθ₁ : 0 < θ₁)
    (hB₁ : 0 < B₁) :
    ∃ C₁ γ₁ e₃ : ℝ, 0 < C₁ ∧ 0 < γ₁ ∧ ∀ eps, e₃ ≤ eps → ∀ ρ : ProbabilityMeasure ℝ,
      MomClass b β vmin ρ → ExpMom θ₁ B₁ ρ → ∀ F : ℕ → ℝ,
      (∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n)) →
      (∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) →
      ∀ t : ℕ, 2 * eps < t →
        stopMeas eps ρ t ≤ volume.withDensity fun a =>
          ENNReal.ofReal (C₁ / t * F (t / 2) *
            Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a))) := by
  have hc0 : 0 < bernsteinRate θ₁ B₁ := bernsteinRate_pos hθ₁ hB₁
  have hlam : 0 < tailRate * vmin := mul_pos tailRate_pos hvmin0
  refine ⟨32 * (72 / 71), min (bernsteinRate θ₁ B₁ / 36) (tailRate * vmin / 16) / 3,
    max 8 (epsZero b β), by norm_num, by positivity, ?_⟩
  intro eps heps ρ hρ hexp F hF hFa t ht
  have heps8 : 8 ≤ eps := le_trans (le_max_left _ _) heps
  have heps0 : epsZero b β ≤ eps := le_trans (le_max_right _ _) heps
  have htpos : (0 : ℝ) < t := by linarith
  have hr1 : 1 ≤ t / 2 := by
    have : (2 : ℝ) < t := by linarith
    have : 2 < t := by exact_mod_cast this
    omega
  have hFr0 : 0 ≤ F (t / 2) := (hF _ hr1).const_nonneg
  have hq : Measurable fun x : ℝ => qdev t x :=
    Continuous.measurable (by unfold qdev; fun_prop)
  have hm3 : Measurable fun x : ℝ => ENNReal.ofReal
      (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x) * F (t / 2)) := by
    fun_prop
  have h1 := stopMeas_le_early hθ₁ heps8 hρ hexp hF hFa ht
  have h2 := stopMeas_le_long hvmin0 heps8 heps0 hρ hF hFa ht
  have h3 := stopMeas_le_spatial hθ₁ heps8 hρ hexp hF hFa ht
  have h12 := le_withDensity_min measurable_const measurable_const h1 h2
  have h123 := le_withDensity_min (measurable_const.min measurable_const) hm3 h12 h3
  refine h123.trans (withDensity_mono (Filter.Eventually.of_forall fun a => ?_))
  beta_reduce
  rw [← ENNReal.ofReal_min, ← ENNReal.ofReal_min]
  refine ENNReal.ofReal_le_ofReal ?_
  set c := bernsteinRate θ₁ B₁ with hc
  set lam := tailRate * vmin with hlamdef
  set X := eps ^ 2 / t with hX
  set Y := (t : ℝ) / eps ^ 2 with hY
  set Z := qdev t a with hZ
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Z := le_min (div_nonneg (sq_nonneg _) htpos.le) (abs_nonneg _)
  set γ₁ := min (c / 36) (lam / 16) / 3 with hγ₁
  have hg1 : γ₁ ≤ c / 36 / 3 := by
    have := min_le_left (c / 36) (lam / 16)
    rw [hγ₁]
    linarith
  have hg2 : γ₁ ≤ lam / 16 / 3 := by
    have := min_le_right (c / 36) (lam / 16)
    rw [hγ₁]
    linarith
  set S := γ₁ * (X + Y + Z) with hS
  have hsum : S ≤ (c / 36 * X + lam / 16 * Y + c / 16 * Z) / 3 := by
    have a1 := mul_le_mul_of_nonneg_right hg1 hX0
    have a2 := mul_le_mul_of_nonneg_right hg2 hY0
    have a3 := mul_le_mul_of_nonneg_right hg1 hZ0
    have a4 : c / 36 * Z ≤ c / 16 * Z :=
      mul_le_mul_of_nonneg_right (by linarith) hZ0
    rw [hS]
    nlinarith
  have key : ∀ k u : ℝ, k ≤ 32 * (72 / 71) → S ≤ u →
      k / t * Real.exp (-u) * F (t / 2) ≤ 32 * (72 / 71) / t * F (t / 2) * Real.exp (-S) := by
    intro k u hk hu
    have he : Real.exp (-u) ≤ Real.exp (-S) := Real.exp_le_exp.2 (by linarith)
    calc k / t * Real.exp (-u) * F (t / 2) = (k * Real.exp (-u)) * (F (t / 2) / t) := by ring
      _ ≤ (32 * (72 / 71) * Real.exp (-S)) * (F (t / 2) / t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk he (Real.exp_pos _).le (by norm_num))
            (by positivity)
      _ = 32 * (72 / 71) / t * F (t / 2) * Real.exp (-S) := by ring
  rw [neg_mul, neg_mul, neg_mul, neg_mul]
  by_cases hu : S ≤ c / 36 * X
  · exact ((min_le_left _ _).trans (min_le_left _ _)).trans (key 8 _ (by norm_num) hu)
  by_cases hv : S ≤ lam / 16 * Y
  · refine ((min_le_left _ _).trans (min_le_right _ _)).trans (le_of_eq_of_le ?_
      (key (32 * (72 / 71)) _ le_rfl hv))
    ring
  have hw : S ≤ c / 16 * Z := by linarith
  exact (min_le_right _ _).trans (key 8 _ (by norm_num) hw)

end

end PGM
