import PLAStochastic.Index.CEPS.Output.IidTransfer
import PLAStochastic.Index.CEPS.Output.Grouping

/-!
# Track O: stopping tails with finitely many inserted coordinates

`output-closure.md` (O9) and `smoothing.md` (S7). Under `outMeasure f β`, the coordinates
in `H = {l | β l ≠ 0}` carry the finite measures `|mellinOp^[β l] f| dx` and the others carry
the input law `ν`. Write `M_H = ∏_{l ∈ H} ‖mellinOp^[β l] f‖₁` and
`W_H = ∏_{l ∈ H} ∫ |mellinOp^[β l] f(x)| e^{θ|x - 1|} dx`.

* `outMeasure_eq_mul_pi`: an event that ignores the coordinates in `H` has
  `outMeasure`-measure `M_H` times its `ν^{⊗n}`-probability (`lintegral_pi_eq_mul_of_indep`).
* `outMeasure_stop_le_long`: `{T = n}` lies in a window event of one of `r + 1` fixed
  disjoint blocks of length `⌊(n-1)/(r+1)⌋` that avoids `H` (`exists_block_disjoint`), so
  `μ{T = n} ≤ M_H (72/71) e^{-λ ⌊(n-1)/(r+1)⌋/ε²}`.
* `outMeasure_stop_le_short`: replacing the inserted coordinates by `1` moves every key by at
  most `D_H = ∑_{l ∈ H} |x_l - 1|` (`abs_vkeys_sub_replaceOne_le`), so
  `μ{T = n} ≤ e^{-θε/2} W_H + M_H (2 e^{-c min((ε/4)²/n, ε/4)} + e^{-θε/4} W_0^{|H|})`,
  with the maximal Bernstein bound for the uninserted walk.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace PGM

variable {n : ℕ}

/-- The inserted coordinates. -/
def outSupp (β : Fin n → ℕ) : Finset (Fin n) := {l | β l ≠ 0}

/-- The mass of one inserted factor. -/
def outMass (f : ℝ → ℝ) (a : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal |mellinOp^[a] f x|

/-- The exponentially weighted mass of one inserted factor. -/
def outWeight (f : ℝ → ℝ) (θ : ℝ) (a : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|mellinOp^[a] f x| * Real.exp (θ * |x - 1|))

theorem outMeasure_factor_univ (f : ℝ → ℝ) (β : Fin n → ℕ) (l : Fin n) :
    (volume.withDensity fun x => ENNReal.ofReal |mellinOp^[β l] f x|) univ = outMass f (β l) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, outMass]

theorem outMass_le_outWeight (f : ℝ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (a : ℕ) :
    outMass f a ≤ outWeight f θ a := by
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  have : 1 ≤ Real.exp (θ * |x - 1|) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg (mellinOp^[a] f x)]

variable {f : ℝ → ℝ} {ν : ProbabilityMeasure ℝ}

theorem outMeasure_factor_of_zero (hpos : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    {β : Fin n → ℕ} {l : Fin n} (hl : l ∉ outSupp β) :
    (volume.withDensity fun x => ENNReal.ofReal |mellinOp^[β l] f x|) = (ν : Measure ℝ) := by
  have h0 : β l = 0 := by simpa [outSupp] using hl
  rw [h0, hν]
  simp only [Function.iterate_zero, id, abs_of_nonneg (hpos _)]

/-- **Replacing the inserted factors by the input law.** -/
theorem lintegral_outMeasure_eq_mul (hpos : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    (β : Fin n → ℕ) {F : (Fin n → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (hind : ∀ x y : Fin n → ℝ, (∀ l ∉ outSupp β, x l = y l) → F x = F y) :
    ∫⁻ x, F x ∂(outMeasure f β) =
      (∏ l ∈ outSupp β, outMass f (β l)) * ∫⁻ x, F x ∂(Measure.pi fun _ => (ν : Measure ℝ)) := by
  rw [outMeasure, lintegral_pi_eq_mul_of_indep _ (ν : Measure ℝ) (outSupp β)
    (fun l hl => outMeasure_factor_of_zero hpos hν hl) hF hind]
  simp_rw [outMeasure_factor_univ]

theorem outMeasure_eq_mul_pi (hpos : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    (β : Fin n → ℕ) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hind : ∀ x y : Fin n → ℝ, (∀ l ∉ outSupp β, x l = y l) → (x ∈ E ↔ y ∈ E)) :
    outMeasure f β E =
      (∏ l ∈ outSupp β, outMass f (β l)) * Measure.pi (fun _ => (ν : Measure ℝ)) E := by
  have h := lintegral_outMeasure_eq_mul hpos hν β (F := E.indicator 1)
    (measurable_one.indicator hE) (fun x y hxy => by
      by_cases hx : x ∈ E
      · rw [indicator_of_mem hx, indicator_of_mem ((hind x y hxy).mp hx)]; rfl
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun hy => hx ((hind x y hxy).mpr hy))])
  rwa [lintegral_indicator_one hE, lintegral_indicator_one hE] at h

/-! ## The long tail -/

/-- Among `r + 1` disjoint blocks of length `w`, one avoids a set of at most `r` points. -/
theorem exists_block_disjoint {r w : ℕ} (H : Finset (Fin n)) (hH : #H ≤ r) :
    ∃ b ≤ r, ∀ l ∈ H, ¬ (b * w ≤ (l : ℕ) ∧ (l : ℕ) < b * w + w) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, -, -⟩ := hcon 0 (Nat.zero_le r)
  let φ : ℕ → Fin n := fun b => if h : b ≤ r then (hcon b h).choose else l₀
  have hφH : ∀ b ∈ Finset.range (r + 1), φ b ∈ H := by
    intro b hb
    have h : b ≤ r := by rw [Finset.mem_range] at hb; omega
    simp only [φ, dif_pos h]
    exact (hcon b h).choose_spec.1
  have hφ : ∀ b ∈ Finset.range (r + 1), b * w ≤ (φ b : ℕ) ∧ (φ b : ℕ) < b * w + w := by
    intro b hb
    have h : b ≤ r := by rw [Finset.mem_range] at hb; omega
    simp only [φ, dif_pos h]
    exact (hcon b h).choose_spec.2
  have key : ∀ b b' (l : ℕ), b < b' → b' * w ≤ l → l < b * w + w → False := by
    intro b b' l h h1 h2
    have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega
  have hinj : Set.InjOn φ ((Finset.range (r + 1) : Finset ℕ) : Set ℕ) := by
    intro b hb b' hb' heq
    have h1 := hφ b hb
    have h2 := hφ b' hb'
    rw [heq] at h1
    rcases lt_trichotomy b b' with h | h | h
    · exact (key b b' _ h h2.1 h1.2).elim
    · exact h
    · exact (key b' b _ h h1.1 h2.2).elim
  have := Finset.card_le_card_of_injOn φ (fun b hb => hφH b hb) hinj
  rw [Finset.card_range] at this
  omega

variable {eps : ℝ}

/-- **Long stopping tail with inserted coordinates** (`smoothing.md` (S7)). -/
theorem outMeasure_stop_le_long (hpos : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    {b β' vmin : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β' ≤ eps)
    (hmom : MomClass b β' vmin ν) {r : ℕ} (hn : 1 ≤ n) (β : Fin n → ℕ)
    (hH : #(outSupp β) ≤ r) :
    outMeasure f β {z | stopsAt eps z} ≤ (∏ l ∈ outSupp β, outMass f (β l)) *
      ENNReal.ofReal (72 / 71 *
        Real.exp (-(tailRate * vmin) * ((n - 1) / (r + 1) : ℕ) / eps ^ 2)) := by
  set w := (n - 1) / (r + 1) with hw
  obtain ⟨b0, hb0, hdisj⟩ := exists_block_disjoint (w := w) (outSupp β) hH
  have hle : b0 * w + w + 1 ≤ n := by
    have h1 : w * (r + 1) ≤ n - 1 := Nat.div_mul_le_self (n - 1) (r + 1)
    have h2 : (b0 + 1) * w ≤ (r + 1) * w := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at h2
    rw [mul_comm] at h1
    omega
  calc outMeasure f β {z | stopsAt eps z}
      ≤ outMeasure f β (windowEvent eps n (b0 * w) w) :=
        measure_mono fun z hz => stopsAt_mem_windowEvent hz hle
    _ = (∏ l ∈ outSupp β, outMass f (β l)) *
          Measure.pi (fun _ => (ν : Measure ℝ)) (windowEvent eps n (b0 * w) w) :=
        outMeasure_eq_mul_pi hpos hν β (measurableSet_windowEvent n _ w) fun x y hxy =>
          windowEvent_congr fun l hl1 hl2 => hxy l fun hlH => hdisj l hlH ⟨hl1, hl2⟩
    _ ≤ _ := by
        gcongr
        exact pi_windowEvent_le hvmin0 heps hmom (by omega)

/-! ## The short tail -/

/-- Replace the inserted coordinates by `1`. -/
def replaceOne (H : Finset (Fin n)) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun l => if l ∈ H then 1 else z l

/-- The total deviation `∑_{l ∈ H} |z_l - 1|` of the inserted coordinates. -/
def devH (H : Finset (Fin n)) (z : Fin n → ℝ) : ℝ := ∑ l ∈ H, |z l - 1|

theorem measurable_replaceOne (H : Finset (Fin n)) : Measurable (replaceOne H) := by
  refine measurable_pi_lambda _ fun l => ?_
  simp only [replaceOne]
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply l

theorem measurable_devH (H : Finset (Fin n)) : Measurable (devH H) :=
  Finset.measurable_sum _ fun l _ =>
    continuous_abs.measurable.comp ((measurable_pi_apply l).sub_const 1)

theorem abs_vkeys_sub_replaceOne_le (H : Finset (Fin n)) (z : Fin n → ℝ) (j : ℕ) :
    |vkeys z j - vkeys (replaceOne H z) j| ≤ devH H z := by
  classical
  set g : ℕ → ℝ := fun q => |vext z q - vext (replaceOne H z) q| with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => abs_nonneg _
  have hgn : ∀ q, n ≤ q → g q = 0 := by
    intro q hq
    simp [hg, vext, show ¬ q < n by omega]
  have h1 : |vkeys z j - vkeys (replaceOne H z) j| ≤ ∑ q ∈ range j, g q := by
    rw [vkeys, vkeys, gapKeys, gapKeys, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ q ∈ range j, g q ≤ ∑ q ∈ range n, g q := by
    rw [← Finset.sum_filter_of_ne (p := fun q => q < n) (fun q _ hq => by
      by_contra h; exact hq (hgn q (not_lt.mp h)))]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ => hg0 q
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact hq.2
  have h3 : ∑ q ∈ range n, g q = devH H z := by
    rw [← Fin.sum_univ_eq_sum_range, devH, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ H)]
    have e1 : ∑ l ∈ univ.filter (· ∈ H), g l = ∑ l ∈ H, |z l - 1| := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.sum_congr rfl fun l hl => ?_
      simp [hg, vext, replaceOne, hl]
    have e2 : ∑ l ∈ univ.filter (· ∉ H), g l = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [hg, vext, replaceOne, hl]
    rw [e1, e2, add_zero]
  linarith

theorem stopsAt_subset_short (H : Finset (Fin n)) :
    {z : Fin n → ℝ | stopsAt eps z} ⊆
      {z | eps / 2 < devH H z} ∪ replaceOne H ⁻¹' walkEvent (eps / 2) n := by
  intro z hz
  obtain ⟨j, hj, hjz⟩ := stopsAt_mem_walkEvent hz
  by_cases hd : eps / 2 < devH H z
  · exact Or.inl hd
  · refine Or.inr ⟨j, hj, ?_⟩
    have h := abs_vkeys_sub_replaceOne_le H z j
    have := abs_sub_abs_le_abs_sub (vkeys z j - j) (vkeys (replaceOne H z) j - j)
    have e : vkeys z j - j - (vkeys (replaceOne H z) j - j) =
        vkeys z j - vkeys (replaceOne H z) j := by ring
    rw [e] at this
    push Not at hd
    linarith

theorem walk_replaceOne_subset (H : Finset (Fin n)) (x : ℝ) :
    replaceOne H ⁻¹' walkEvent x n ⊆ walkEvent (x / 2) n ∪ {z | x / 2 < devH H z} := by
  rintro z ⟨j, hj, hjz⟩
  by_cases hd : x / 2 < devH H z
  · exact Or.inr hd
  · refine Or.inl ⟨j, hj, ?_⟩
    have h := abs_vkeys_sub_replaceOne_le H z j
    have := abs_sub_abs_le_abs_sub (vkeys (replaceOne H z) j - j) (vkeys z j - j)
    have e : vkeys (replaceOne H z) j - j - (vkeys z j - j) =
        -(vkeys z j - vkeys (replaceOne H z) j) := by ring
    rw [e, abs_neg] at this
    push Not at hd
    linarith

/-- The exponential moment of the deviation of the inserted coordinates. -/
theorem lintegral_exp_devH (μ : Fin n → Measure ℝ) [∀ l, SigmaFinite (μ l)] (θ : ℝ)
    (H : Finset (Fin n)) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (θ * devH H z)) ∂(Measure.pi μ) =
      (∏ l ∈ H, ∫⁻ x, ENNReal.ofReal (Real.exp (θ * |x - 1|)) ∂(μ l)) *
        ∏ l ∈ univ.filter (· ∉ H), μ l univ := by
  classical
  set g : Fin n → ℝ → ℝ≥0∞ := fun l x =>
    if l ∈ H then ENNReal.ofReal (Real.exp (θ * |x - 1|)) else 1 with hg
  have hgm : ∀ l, Measurable (g l) := by
    intro l
    simp only [hg]
    split_ifs
    · exact (Real.continuous_exp.measurable.comp (measurable_const.mul
        (continuous_abs.measurable.comp (measurable_id.sub_const 1)))).ennreal_ofReal
    · exact measurable_const
  have hpt : ∀ z : Fin n → ℝ, ENNReal.ofReal (Real.exp (θ * devH H z)) = ∏ l, g l (z l) := by
    intro z
    rw [devH, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun l _ => (Real.exp_pos _).le]
    simp only [hg]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hpt]
  rw [lintegral_fin_pi_prod μ g hgm]
  have hint : ∀ l, ∫⁻ y, g l y ∂(μ l) =
      if l ∈ H then ∫⁻ x, ENNReal.ofReal (Real.exp (θ * |x - 1|)) ∂(μ l) else μ l univ := by
    intro l
    simp only [hg]
    split_ifs <;> simp
  simp_rw [hint]
  rw [Finset.prod_ite (s := univ) (p := (· ∈ H)), Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Markov's inequality for the deviation of the inserted coordinates. -/
theorem measure_devH_le (μ : Measure (Fin n → ℝ)) (H : Finset (Fin n)) {θ : ℝ} (hθ : 0 ≤ θ)
    (t : ℝ) :
    μ {z | t < devH H z} ≤
      ENNReal.ofReal (Real.exp (-(θ * t))) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (θ * devH H z)) ∂μ := by
  set F : (Fin n → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * devH H z)) with hFdef
  have hF : Measurable F :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_devH H))).ennreal_ofReal
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * t)) with hc
  have hsub : {z | t < devH H z} ⊆ {z | c ≤ F z} := fun z hz =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hz) hθ))
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) hF.aemeasurable c
  calc μ {z | t < devH H z} ≤ μ {z | c ≤ F z} := measure_mono hsub
    _ = c⁻¹ * (c * μ {z | c ≤ F z}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ c⁻¹ * ∫⁻ z, F z ∂μ := by gcongr
    _ = _ := by rw [hc, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]

theorem outWeight_eq_lintegral {f : ℝ → ℝ} (hfm : Measurable f) (θ : ℝ) (a : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * |x - 1|))
        ∂(volume.withDensity fun x => ENNReal.ofReal |mellinOp^[a] f x|) = outWeight f θ a := by
  have h1 : Measurable fun x => ENNReal.ofReal |mellinOp^[a] f x| :=
    (continuous_abs.measurable.comp (measurable_mellinOp_iterate hfm a)).ennreal_ofReal
  have h2 : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * |x - 1|)) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      (continuous_abs.measurable.comp (measurable_id.sub_const 1)))).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ h1 h2, outWeight]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Short stopping tail with inserted coordinates** (`output-closure.md` (O9)). -/
theorem outMeasure_stop_le_short (hpos : ∀ x, 0 ≤ f x) (hfm : Measurable f)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    {θ : ℝ} (hθ : 0 ≤ θ) {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hνpos : (ν : Measure ℝ) (Iic 0) = 0)
    (hmean : lawMean ν = 1) (hexp : ExpMom θ₁ B₁ ν) (hn : 1 ≤ n) (heps : 0 < eps)
    (β : Fin n → ℕ) :
    outMeasure f β {z | stopsAt eps z} ≤
      ENNReal.ofReal (Real.exp (-(θ * (eps / 2)))) * ∏ l ∈ outSupp β, outWeight f θ (β l) +
      (∏ l ∈ outSupp β, outMass f (β l)) *
        (ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ *
            min ((eps / 4) ^ 2 / n) (eps / 4)))) +
          ENNReal.ofReal (Real.exp (-(θ * (eps / 4)))) *
            (∫⁻ x, ENNReal.ofReal (Real.exp (θ * |x - 1|)) ∂(ν : Measure ℝ)) ^ #(outSupp β)) := by
  classical
  set H := outSupp β with hH
  have hfac : ∀ l ∈ univ.filter (· ∉ H),
      (volume.withDensity fun x => ENNReal.ofReal |mellinOp^[β l] f x|) univ = 1 := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [outMeasure_factor_of_zero hpos hν hl, measure_univ]
  -- the inserted deviation under `outMeasure`
  have hE1 : outMeasure f β {z | eps / 2 < devH H z} ≤
      ENNReal.ofReal (Real.exp (-(θ * (eps / 2)))) * ∏ l ∈ H, outWeight f θ (β l) := by
    refine (measure_devH_le _ H hθ _).trans (le_of_eq ?_)
    rw [outMeasure, lintegral_exp_devH, Finset.prod_eq_one hfac, mul_one]
    simp_rw [outWeight_eq_lintegral hfm]
  -- the uninserted walk
  have hind : ∀ x y : Fin n → ℝ, (∀ l ∉ outSupp β, x l = y l) →
      (x ∈ replaceOne H ⁻¹' walkEvent (eps / 2) n ↔ y ∈ replaceOne H ⁻¹' walkEvent (eps / 2) n) := by
    intro x y hxy
    have : replaceOne H x = replaceOne H y := by
      funext l
      simp only [replaceOne]
      split_ifs with hl
      · rfl
      · exact hxy l hl
    simp only [Set.mem_preimage, this]
  have hE2 : outMeasure f β (replaceOne H ⁻¹' walkEvent (eps / 2) n) =
      (∏ l ∈ H, outMass f (β l)) *
        Measure.pi (fun _ => (ν : Measure ℝ)) (replaceOne H ⁻¹' walkEvent (eps / 2) n) :=
    outMeasure_eq_mul_pi hpos hν β (measurable_replaceOne H (measurableSet_walkEvent _ n)) hind
  have hW : Measure.pi (fun _ => (ν : Measure ℝ)) (replaceOne H ⁻¹' walkEvent (eps / 2) n) ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ * min ((eps / 4) ^ 2 / n) (eps / 4)))) +
        ENNReal.ofReal (Real.exp (-(θ * (eps / 4)))) *
          (∫⁻ x, ENNReal.ofReal (Real.exp (θ * |x - 1|)) ∂(ν : Measure ℝ)) ^ #H := by
    refine (measure_mono (walk_replaceOne_subset H (eps / 2))).trans
      ((measure_union_le _ _).trans (add_le_add ?_ ?_))
    · have := pi_walkEvent_le hθ₁ hνpos hmean hexp hn (x := eps / 4) (by positivity)
      rwa [show eps / 2 / 2 = eps / 4 by ring]
    · rw [show eps / 2 / 2 = eps / 4 by ring]
      refine (measure_devH_le _ H hθ _).trans (le_of_eq ?_)
      rw [lintegral_exp_devH, Finset.prod_const]
      simp
  calc outMeasure f β {z | stopsAt eps z}
      ≤ outMeasure f β ({z | eps / 2 < devH H z} ∪ replaceOne H ⁻¹' walkEvent (eps / 2) n) :=
        measure_mono (stopsAt_subset_short H)
    _ ≤ outMeasure f β {z | eps / 2 < devH H z} +
          outMeasure f β (replaceOne H ⁻¹' walkEvent (eps / 2) n) := measure_union_le _ _
    _ ≤ _ := by
        rw [hE2]
        gcongr

end PGM
