import PLAStochastic.ForMathlib.Probability.LatticeConcentration.Elementary
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Kesten's sharpening of the lattice Kolmogorov–Rogozin inequality

H. Kesten, *A sharper form of the Doeblin–Lévy–Kolmogorov–Rogozin inequality for
concentration functions*, Math. Scand. 25 (1969), Theorem 2 and §2, specialised to
integer-valued summands and windows of one point.

Main result: `kesten_lattice`, the lattice iid case of Kesten (1.6) with `L = λ = 1/2`,
`lconc (convFin n μ) 1 · √(n (1 - lconc μ 1)) ≤ KKes C · lconc μ 1` with
`KKes C = 32 (1 + C)`, assuming `RogozinLattice C`.

Proof, following Kesten §2 (lattice transcription):
* laws on `ℤ` form a commutative monoid `Kesten.Law` under convolution, so finite
  convolutions are `Finset.prod`s;
* `Kesten.Bound K a` is Kesten's `R(m, a) ≤ K a m^{-1/2}` for all `m ≥ 4`;
* `Kesten.bound_step` is (2.8): each law is split as `(α + β)/2` with `α` living on a
  median window of `cᵢ + 1` integers (replacing the events `Eᵢ`), the `⌊m/2⌋` laws with the
  shortest windows are expanded (`Kesten.expand_le`, (2.15)), and the window terms are
  bounded by `RogozinLattice` applied to the other half ((2.19)–(2.21));
* `Kesten.bound_of_level` iterates (2.8) down from `Kesten.bound_base` ((2.12)), giving
  `R(m, a) ≤ 24 C a m^{-1/2}` for `a ≤ 1/2`.
-/

namespace PGM

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Kesten

/-! ### Probability laws on `ℤ` as a commutative monoid under convolution -/

/-- A probability law on `ℤ`; these form a commutative monoid under convolution. -/
structure Law where
  /-- The underlying measure. -/
  toMeasure : Measure ℤ
  isProb : IsProbabilityMeasure toMeasure

attribute [instance] Law.isProb

@[ext] lemma Law.ext {p q : Law} (h : p.toMeasure = q.toMeasure) : p = q := by
  cases p; cases q; cases h; rfl

instance : CommMonoid Law where
  mul p q := ⟨p.toMeasure ∗ q.toMeasure, inferInstance⟩
  one := ⟨Measure.dirac 0, inferInstance⟩
  mul_assoc p q r := Law.ext (Measure.conv_assoc _ _ _)
  one_mul p := Law.ext (Measure.dirac_zero_conv _)
  mul_one p := Law.ext (Measure.conv_dirac_zero _)
  mul_comm p q := Law.ext (Measure.conv_comm _ _)

@[simp] lemma Law.mul_toMeasure (p q : Law) :
    (p * q).toMeasure = p.toMeasure ∗ q.toMeasure := rfl

lemma convFin_eq_prod : ∀ (m : ℕ) (f : Fin m → Law),
    convFin m (fun i => (f i).toMeasure) = (∏ i, f i).toMeasure
  | 0, f => by rw [Fin.prod_univ_zero]; rfl
  | m + 1, f => by
    rw [Fin.prod_univ_castSucc, Law.mul_toMeasure, ← convFin_eq_prod m]
    rfl

/-! ### The concentration function `lconc` -/

lemma lconc_mono (μ : Measure ℤ) [IsFiniteMeasure μ] {c c' : ℕ} (h : c ≤ c') :
    lconc μ c ≤ lconc μ c' :=
  lconc_le fun x => (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ico_subset_Ico le_rfl (by omega)))).trans
    (window_le_lconc μ c' x)

lemma lconc_one_le {μ : Measure ℤ} {t : ℝ} (h : ∀ x : ℤ, (μ {x}).toReal ≤ t) :
    lconc μ 1 ≤ t :=
  lconc_le fun x => by rw [Nat.cast_one, Ico_one]; exact h x

/-! ### Convolution on `ℤ` -/

lemma conv_apply (μ ν : Measure ℤ) [SFinite ν] (s : Set ℤ) :
    (μ ∗ ν) s = ∫⁻ y, ν ((fun z => y + z) ⁻¹' s) ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add (MeasurableSet.of_discrete),
    Measure.prod_apply (measurable_add (MeasurableSet.of_discrete))]
  rfl

/-- Kesten (2.3): convolving with a probability law does not increase concentration. -/
lemma lconc_conv_le_right (μ ν : Measure ℤ) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (c : ℕ) : lconc (μ ∗ ν) c ≤ lconc ν c := by
  refine lconc_le fun x => ENNReal.toReal_le_of_le_ofReal (lconc_nonneg _ _) ?_
  rw [conv_apply]
  calc ∫⁻ y, ν ((fun z => y + z) ⁻¹' Set.Ico x (x + c)) ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (lconc ν c) ∂μ := by
        refine lintegral_mono fun y => ?_
        have : (fun z => y + z) ⁻¹' Set.Ico x (x + c) = Set.Ico (x - y) (x - y + c) := by
          ext z; simp only [Set.mem_preimage, Set.mem_Ico]; omega
        rw [this]
        exact window_le_ofReal_lconc ν c _
    _ = ENNReal.ofReal (lconc ν c) := by simp

lemma lconc_conv_le_left (μ ν : Measure ℤ) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (c : ℕ) : lconc (μ ∗ ν) c ≤ lconc μ c := by
  rw [Measure.conv_comm]
  exact lconc_conv_le_right ν μ c

lemma lconc_pos (μ : Measure ℤ) [IsProbabilityMeasure μ] : 0 < lconc μ 1 := by
  by_contra h
  replace h := not_lt.1 h
  have hz : ∀ x : ℤ, μ {x} = 0 := fun x =>
    (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm ((atom_le_lconc μ x).trans h)
      ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top μ _)
  have : μ (⋃ x : ℤ, {x}) = 0 := measure_iUnion_null hz
  rw [Set.iUnion_of_singleton, measure_univ] at this
  exact one_ne_zero this

/-! ### The lattice Kolmogorov–Rogozin inequality over a finite index set -/

lemma rogozin_finset {C : ℝ} (hC : RogozinLattice C) {ι : Type*} (s : Finset ι)
    (f : ι → Law) (c w : ℕ) (hc : 1 ≤ c) (hw : 1 ≤ w) :
    lconc (∏ i ∈ s, f i).toMeasure w * Real.sqrt (∑ i ∈ s, (1 - lconc (f i).toMeasure c)) ≤
      C * ((w : ℝ) / c + 1) := by
  have h := hC s.card (fun k => (f (s.equivFin.symm k)).toMeasure) (fun _ => inferInstance)
    c w hc hw
  rw [convFin_eq_prod s.card (fun k => f (s.equivFin.symm k))] at h
  have e1 : ∏ k : Fin s.card, f (s.equivFin.symm k) = ∏ i ∈ s, f i := by
    rw [Equiv.prod_comp s.equivFin.symm (fun x : s => f x), Finset.prod_coe_sort]
  have e2 : ∑ k : Fin s.card, (1 - lconc (f (s.equivFin.symm k)).toMeasure c) =
      ∑ i ∈ s, (1 - lconc (f i).toMeasure c) := by
    rw [Equiv.sum_comp s.equivFin.symm (fun x : s => 1 - lconc (f x).toMeasure c),
      Finset.sum_coe_sort s (fun i => 1 - lconc (f i).toMeasure c)]
  rwa [e1, e2] at h

lemma sqrt_le_two_mul_sqrt {x y : ℝ} (h : x ≤ 4 * y) : Real.sqrt x ≤ 2 * Real.sqrt y := by
  calc Real.sqrt x ≤ Real.sqrt (4 * y) := Real.sqrt_le_sqrt h
    _ = 2 * Real.sqrt y := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-! ### Median windows and the half-and-half splitting of a law -/

/-- The lattice form of Kesten's intervals `Iᵢ = [bᵢ, bᵢ + cᵢ]`: a window of `c + 1`
consecutive integers carrying mass `≥ 1/2`, while every window of `c` integers carries mass
`≤ 1/2`. -/
lemma exists_window (μ : Measure ℤ) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} < 2⁻¹) :
    ∃ c : ℕ, 1 ≤ c ∧ (∃ b : ℤ, 2⁻¹ ≤ μ (Set.Ico b (b + ((c + 1 : ℕ) : ℤ)))) ∧
      lconc μ c ≤ 2⁻¹ := by
  classical
  have hex : ∃ c : ℕ, ∃ b : ℤ, 2⁻¹ ≤ μ (Set.Ico b (b + ((c + 1 : ℕ) : ℤ))) := by
    have hmono : Monotone (fun N : ℕ => Set.Ico (-(N : ℤ)) N) := fun a b h =>
      Set.Ico_subset_Ico (by omega) (by omega)
    have hU : (⋃ N : ℕ, Set.Ico (-(N : ℤ)) N) = Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_univ, iff_true]
      exact ⟨z.natAbs + 1, by omega, by omega⟩
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU, measure_univ] at ht
    obtain ⟨N, hN⟩ :=
      (ht.eventually (lt_mem_nhds (show (2⁻¹ : ℝ≥0∞) < 1 by norm_num))).exists
    refine ⟨2 * N, -N, hN.le.trans (measure_mono (Set.Ico_subset_Ico le_rfl ?_))⟩
    push_cast
    omega
  have hc₀ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := hc₀
    rw [h0, zero_add, Nat.cast_one, Ico_one] at hb
    exact absurd hb (not_le.2 (hμ b))
  refine ⟨Nat.find hex, Nat.one_le_iff_ne_zero.2 hpos, hc₀, lconc_le fun x => ?_⟩
  obtain ⟨c', hc'⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (show c' < Nat.find hex by omega)
  have hx : μ (Set.Ico x (x + ((c' + 1 : ℕ) : ℤ))) < 2⁻¹ := not_le.1 fun h => hmin ⟨x, h⟩
  rw [hc']
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) (hx.le.trans ?_)
  rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- Kesten's events `Eᵢ` of probability `1/2`: split a law into two halves, the first of
which lives on a prescribed set of mass at least `1/2`. -/
lemma exists_split (ν : Law) (W : Set ℤ) (hW : 2⁻¹ ≤ ν.toMeasure W) :
    ∃ α β : Law, ν.toMeasure = (2⁻¹ : ℝ≥0∞) • α.toMeasure + (2⁻¹ : ℝ≥0∞) • β.toMeasure ∧
      ∀ k ∉ W, α.toMeasure {k} = 0 := by
  set t := ν.toMeasure W with ht_def
  have ht0 : t ≠ 0 := (lt_of_lt_of_le (by norm_num) hW).ne'
  have ht1 : t ≠ ⊤ := measure_ne_top _ _
  have htinv : t⁻¹ ≤ 2 := by rw [ENNReal.inv_le_iff_inv_le]; exact hW
  have h2 : (2⁻¹ : ℝ≥0∞) * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  set αm : Measure ℤ := t⁻¹ • ν.toMeasure.restrict W with hαm
  set βm : Measure ℤ := (2 : ℝ≥0∞) • ν.toMeasure.restrict Wᶜ +
    (2 - t⁻¹) • ν.toMeasure.restrict W with hβm
  have hsum : ν.toMeasure = (2⁻¹ : ℝ≥0∞) • αm + (2⁻¹ : ℝ≥0∞) • βm := by
    have h3 : (2⁻¹ : ℝ≥0∞) * t⁻¹ + 2⁻¹ * (2 - t⁻¹) = 1 := by
      rw [← mul_add, add_tsub_cancel_of_le htinv, h2]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := ν.toMeasure)
      (MeasurableSet.of_discrete : MeasurableSet W)]
    rw [hαm, hβm, smul_add, smul_smul, smul_smul, smul_smul, h2, one_smul, add_left_comm,
      ← add_smul, h3, one_smul, add_comm]
  have hα : IsProbabilityMeasure αm := ⟨by
    rw [hαm, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ← ht_def,
      ENNReal.inv_mul_cancel ht0 ht1]⟩
  have hβ : IsProbabilityMeasure βm := ⟨by
    have e := congrArg (fun μ : Measure ℤ => μ Set.univ) hsum
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ] at e
    have e2 : (2⁻¹ : ℝ≥0∞) + 2⁻¹ * βm Set.univ = 2⁻¹ + 2⁻¹ * 1 :=
      calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ * βm Set.univ = 2⁻¹ * 1 + 2⁻¹ * βm Set.univ := by rw [mul_one]
        _ = 1 := e.symm
        _ = 2⁻¹ + 2⁻¹ * 1 := by rw [mul_one, ENNReal.inv_two_add_inv_two]
    have e3 := (ENNReal.add_right_inj (by norm_num)).1 e2
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 e3⟩
  refine ⟨⟨αm, hα⟩, ⟨βm, hβ⟩, hsum, fun k hk => ?_⟩
  change αm {k} = 0
  rw [hαm, Measure.smul_apply, Measure.restrict_apply (MeasurableSet.of_discrete),
    Set.singleton_inter_eq_empty.2 hk, measure_empty, smul_zero]

lemma atom_le_of_split {ν α β : Measure ℤ}
    (h : ν = (2⁻¹ : ℝ≥0∞) • α + (2⁻¹ : ℝ≥0∞) • β) (k : ℤ) :
    α {k} ≤ 2 * ν {k} ∧ β {k} ≤ 2 * ν {k} := by
  have hk : ν {k} = 2⁻¹ * α {k} + 2⁻¹ * β {k} := by
    rw [h]; simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [hk, mul_add, ← mul_assoc, ← mul_assoc, h2, one_mul, one_mul]
  exact ⟨le_self_add, le_add_self⟩

/-! ### Kesten (2.17)–(2.19): a law supported on a window, convolved -/

lemma conv_atom_le (α σ : Measure ℤ) [SFinite α] [SFinite σ] (b : ℤ) (c : ℕ)
    {A D : ℝ≥0∞} (hαW : ∀ k ∉ Set.Ico b (b + c), α {k} = 0) (hα : ∀ k, α {k} ≤ A)
    (hσ : ∀ x, σ (Set.Ico x (x + c)) ≤ D) (j : ℤ) : (α ∗ σ) {j} ≤ A * D := by
  rw [Measure.conv_comm, conv_apply_singleton]
  set V : Set ℤ := Set.Ico (j - b - c + 1) (j - b - c + 1 + c) with hV
  calc ∫⁻ y, α {j - y} ∂σ ≤ ∫⁻ y, V.indicator (fun _ => A) y ∂σ := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ V
        · rw [Set.indicator_of_mem hy]; exact hα _
        · rw [Set.indicator_of_notMem hy, hαW]
          simp only [hV, Set.mem_Ico, not_and_or, not_le, not_lt] at hy ⊢
          omega
    _ = A * σ V := lintegral_indicator_const MeasurableSet.of_discrete A
    _ ≤ A * D := by gcongr; exact hσ _

/-! ### Kesten (2.15): expanding the halved factors one at a time -/

lemma conv_split_singleton {ν α β : Measure ℤ} (σ : Measure ℤ) [SFinite σ]
    (h : ν = (2⁻¹ : ℝ≥0∞) • α + (2⁻¹ : ℝ≥0∞) • β) (j : ℤ) :
    (ν ∗ σ) {j} = 2⁻¹ * (α ∗ σ) {j} + 2⁻¹ * (β ∗ σ) {j} := by
  rw [conv_apply_singleton, conv_apply_singleton, conv_apply_singleton, h,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul]

/-- Iterating the splitting over a set `S` of factors: each factor `ν i` either contributes
its window half `α i` (a term bounded by `E`), or passes on its other half `β i`. -/
lemma expand_le {ι : Type*} [DecidableEq ι] (ν α β : ι → Law) (A : Finset ι) (ρ : Law)
    (E : ℝ≥0∞)
    (hsplit : ∀ i ∈ A, (ν i).toMeasure =
      (2⁻¹ : ℝ≥0∞) • (α i).toMeasure + (2⁻¹ : ℝ≥0∞) • (β i).toMeasure)
    (hα : ∀ i ∈ A, ∀ (τ : Law) (j : ℤ), (α i * τ * ρ).toMeasure {j} ≤ E) :
    ∀ S ⊆ A, ∀ (τ : Law) (j : ℤ), ((∏ i ∈ S, ν i) * τ * ρ).toMeasure {j} ≤
      E + (2⁻¹ : ℝ≥0∞) ^ S.card * ((∏ i ∈ S, β i) * τ * ρ).toMeasure {j} := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ τ j; simp
  | insert i S hi ih =>
    intro hS τ j
    have hiA : i ∈ A := hS (Finset.mem_insert_self _ _)
    have hSA : S ⊆ A := (Finset.subset_insert _ _).trans hS
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    set P := ∏ x ∈ S, ν x
    set Q := ∏ x ∈ S, β x
    have e1 : ν i * P * τ * ρ = ν i * (P * τ * ρ) := by simp only [mul_assoc]
    have key : (ν i * (P * τ * ρ)).toMeasure {j} = 2⁻¹ * (α i * (P * τ * ρ)).toMeasure {j} +
        2⁻¹ * (β i * (P * τ * ρ)).toMeasure {j} :=
      conv_split_singleton _ (hsplit i hiA) j
    have hA' : (α i * (P * τ * ρ)).toMeasure {j} ≤ E := by
      have := hα i hiA (P * τ) j
      rwa [show α i * (P * τ) * ρ = α i * (P * τ * ρ) by simp only [mul_assoc]] at this
    have hB' := ih hSA (β i * τ) j
    rw [show P * (β i * τ) * ρ = β i * (P * τ * ρ) by
      simp only [mul_assoc, mul_left_comm]] at hB'
    rw [e1, key, show β i * Q * τ * ρ = Q * (β i * τ) * ρ by
      simp only [mul_assoc, mul_left_comm]]
    calc 2⁻¹ * (α i * (P * τ * ρ)).toMeasure {j} + 2⁻¹ * (β i * (P * τ * ρ)).toMeasure {j}
        ≤ 2⁻¹ * E + 2⁻¹ * (E + 2⁻¹ ^ S.card * (Q * (β i * τ) * ρ).toMeasure {j}) := by
          gcongr
      _ = E + 2⁻¹ ^ (S.card + 1) * (Q * (β i * τ) * ρ).toMeasure {j} := by
          rw [mul_add, ← add_assoc, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul,
            ← mul_assoc, ← pow_succ']

/-- Kesten (2.14): the `⌊m/2⌋` factors with the shortest median windows. -/
lemma exists_lower_half {m : ℕ} (c : Fin m → ℕ) :
    ∃ A : Finset (Fin m), A.card = m / 2 ∧ ∀ i ∈ A, ∀ j ∉ A, c i ≤ c j := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = Tuple.sort c := ⟨_, rfl⟩
  have hmono : Monotone (c ∘ σ) := hσ ▸ Tuple.monotone_sort c
  refine ⟨Finset.univ.filter (fun i => ((σ.symm i : Fin m) : ℕ) < m / 2), ?_, ?_⟩
  · have : Finset.univ.filter (fun i => ((σ.symm i : Fin m) : ℕ) < m / 2) =
        (Finset.univ.filter (fun k : Fin m => (k : ℕ) < m / 2)).map σ.toEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding]
      constructor
      · intro h; exact ⟨σ.symm i, h, by simp⟩
      · rintro ⟨k, hk, rfl⟩; simpa using hk
    rw [this, Finset.card_map, Fin.card_filter_val_lt]
    omega
  · intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
    have := hmono (show σ.symm i ≤ σ.symm j from Fin.le_def.2 (by omega))
    simpa using this

/-! ### Kesten's recursion for `R(m, a)` -/

/-- `Bound K a`: every sum of `m ≥ 4` independent integer variables whose atoms are all at
most `a` has largest atom at most `K a / √m`, i.e. Kesten's `R(m, a) ≤ K a m^{-1/2}`. -/
def Bound (K a : ℝ) : Prop :=
  ∀ (m : ℕ), 4 ≤ m → ∀ f : Fin m → Law, (∀ i, lconc (f i).toMeasure 1 ≤ a) →
    lconc (∏ i, f i).toMeasure 1 * Real.sqrt m ≤ K * a

/-- Kesten (2.12): Theorem 1 with `λ = L` gives the bound once `1/4 ≤ a ≤ 1/2`. -/
lemma bound_base {C : ℝ} (hC : RogozinLattice C) (h0 : 0 ≤ C) {a : ℝ} (ha1 : 1 / 4 ≤ a)
    (ha2 : a ≤ 1 / 2) : Bound (24 * C) a := by
  intro m hm f hf
  have h := rogozin_finset hC Finset.univ f 1 1 le_rfl le_rfl
  simp only [Nat.cast_one, div_one] at h
  have hS : (m : ℝ) ≤ 4 * ∑ i, (1 - lconc (f i).toMeasure 1) := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin m)), (1 / 2 : ℝ) ≤ 1 - lconc (f i).toMeasure 1 :=
      fun i _ => by linarith [hf i]
    have := Finset.card_nsmul_le_sum _ _ _ hle
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hsq := sqrt_le_two_mul_sqrt hS
  have hL := lconc_nonneg (∏ i, f i).toMeasure 1
  calc lconc (∏ i, f i).toMeasure 1 * Real.sqrt m
      ≤ lconc (∏ i, f i).toMeasure 1 *
          (2 * Real.sqrt (∑ i, (1 - lconc (f i).toMeasure 1))) :=
        mul_le_mul_of_nonneg_left hsq hL
    _ = 2 * (lconc (∏ i, f i).toMeasure 1 *
          Real.sqrt (∑ i, (1 - lconc (f i).toMeasure 1))) := by ring
    _ ≤ 2 * (C * (1 + 1)) := by linarith
    _ ≤ 24 * C * a := by nlinarith

/-- Kesten (2.8), `R(m, a) ≤ 12 C a m^{-1/2} + 2^{-⌊m/2⌋} R(m, 2a)`, in the form used by the
induction on the doubling level. -/
lemma bound_step {C : ℝ} (hC : RogozinLattice C) (h0 : 0 ≤ C) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (h2 : Bound (24 * C) (2 * a)) : Bound (24 * C) a := by
  classical
  intro m hm f hf
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  -- every atom is at most `a < 1/2`
  have hatom : ∀ i x, (f i).toMeasure {x} ≤ ENNReal.ofReal a := fun i x =>
    (atom_le_ofReal_lconc _ x).trans (ENNReal.ofReal_le_ofReal (hf i))
  have hhalf : ∀ i x, (f i).toMeasure {x} < 2⁻¹ := fun i x => by
    refine (hatom i x).trans_lt ?_
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 ha
  -- median windows `Iᵢ` and the splitting `νᵢ = (αᵢ + βᵢ)/2`
  choose c hc1 hb hlc using fun i => exists_window (f i).toMeasure (hhalf i)
  choose b hb using hb
  choose α β hsplit hsupp using fun i => exists_split (f i) _ (hb i)
  obtain ⟨A, hAcard, hAord⟩ := exists_lower_half c
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Law, ρ = ∏ i ∈ Aᶜ, f i := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 6 * C / Real.sqrt m := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ div_nonneg (by linarith) hsqrt_pos.le
  have hDm : D * Real.sqrt m = 6 * C := by rw [hD, div_mul_cancel₀ _ hsqrt_pos.ne']
  -- Kesten (2.20): the second half is spread out at the scale of each short window
  have hρD : ∀ i ∈ A, lconc ρ.toMeasure (c i + 1) ≤ D := by
    intro i hi
    have h := rogozin_finset hC Aᶜ f (c i) (c i + 1) (hc1 i) (by omega)
    rw [← hρ] at h
    have hci : (1 : ℝ) ≤ c i := by exact_mod_cast hc1 i
    have hR : C * (((c i + 1 : ℕ) : ℝ) / c i + 1) ≤ 3 * C := by
      have : ((c i + 1 : ℕ) : ℝ) / c i ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; push_cast; linarith
      nlinarith
    have hS : (m : ℝ) ≤ 4 * ∑ j ∈ Aᶜ, (1 - lconc (f j).toMeasure (c i)) := by
      have hle : ∀ j ∈ Aᶜ, (1 / 2 : ℝ) ≤ 1 - lconc (f j).toMeasure (c i) := fun j hj => by
        have := (lconc_mono (f j).toMeasure (hAord i hi j (Finset.mem_compl.1 hj))).trans
          (hlc j)
        linarith
      have h' := Finset.card_nsmul_le_sum _ _ _ hle
      rw [Finset.card_compl, Fintype.card_fin, hAcard, nsmul_eq_mul] at h'
      have hmm : (m : ℝ) ≤ 2 * ((m - m / 2 : ℕ) : ℝ) := by
        have : m ≤ 2 * (m - m / 2) := by omega
        exact_mod_cast this
      linarith
    have hsq := sqrt_le_two_mul_sqrt hS
    have hL := lconc_nonneg ρ.toMeasure (c i + 1)
    rw [hD, le_div_iff₀ hsqrt_pos]
    calc lconc ρ.toMeasure (c i + 1) * Real.sqrt m
        ≤ lconc ρ.toMeasure (c i + 1) *
            (2 * Real.sqrt (∑ j ∈ Aᶜ, (1 - lconc (f j).toMeasure (c i)))) :=
          mul_le_mul_of_nonneg_left hsq hL
      _ = 2 * (lconc ρ.toMeasure (c i + 1) *
            Real.sqrt (∑ j ∈ Aᶜ, (1 - lconc (f j).toMeasure (c i)))) := by ring
      _ ≤ 6 * C := by linarith
  -- Kesten (2.19)–(2.21): the terms in which a window half occurs
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = 2 * ENNReal.ofReal a * ENNReal.ofReal D := ⟨_, rfl⟩
  have hα : ∀ i ∈ A, ∀ (τ : Law) (j : ℤ), (α i * τ * ρ).toMeasure {j} ≤ E := by
    intro i hi τ j
    rw [mul_assoc, Law.mul_toMeasure, hE]
    refine conv_atom_le _ _ (b i) (c i + 1) (hsupp i) (fun k => ?_) (fun x => ?_) j
    · exact (atom_le_of_split (hsplit i) k).1.trans (by gcongr; exact hatom i k)
    · rw [Law.mul_toMeasure]
      exact (window_le_ofReal_lconc _ _ x).trans (ENNReal.ofReal_le_ofReal
        ((lconc_conv_le_right _ _ _).trans (hρD i hi)))
  have hexp := expand_le f α β A ρ E (fun i _ => hsplit i) hα A subset_rfl 1
  -- Kesten (2.22): the remaining term is a sum of variables with atoms at most `2a`
  obtain ⟨f', hf'⟩ : ∃ f' : Fin m → Law, f' = fun i => if i ∈ A then β i else f i :=
    ⟨_, rfl⟩
  have hprod : (∏ i ∈ A, f i) * 1 * ρ = ∏ i, f i := by
    rw [mul_one, hρ, Finset.prod_mul_prod_compl]
  have hprod' : (∏ i ∈ A, β i) * 1 * ρ = ∏ i, f' i := by
    rw [mul_one, ← Finset.prod_mul_prod_compl A f', hρ]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [hf', hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [hf', Finset.mem_compl.1 hi]
  simp only [hprod, hprod'] at hexp
  have hf'2 : ∀ i, lconc (f' i).toMeasure 1 ≤ 2 * a := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hf', hi, if_true]
      refine lconc_one_le fun k => ?_
      calc ((β i).toMeasure {k}).toReal ≤ (2 * (f i).toMeasure {k}).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _))
              (atom_le_of_split (hsplit i) k).2
        _ = 2 * ((f i).toMeasure {k}).toReal := by simp [ENNReal.toReal_mul]
        _ ≤ 2 * a := by linarith [atom_le_lconc (f i).toMeasure k, hf i]
    · simp only [hf', hi, if_false]; linarith [hf i, lconc_nonneg (f i).toMeasure 1]
  have hL' := h2 m hm f' hf'2
  have hcard : (2⁻¹ : ℝ) ^ A.card ≤ 1 / 4 := by
    calc (2⁻¹ : ℝ) ^ A.card ≤ (2⁻¹ : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hL'0 := lconc_nonneg (∏ i, f' i).toMeasure 1
  have hmain : lconc (∏ i, f i).toMeasure 1 ≤
      2 * a * D + 1 / 4 * lconc (∏ i, f' i).toMeasure 1 := by
    refine lconc_one_le fun j => ?_
    have hne : E + (2⁻¹ : ℝ≥0∞) ^ A.card * (∏ i, f' i).toMeasure {j} ≠ ⊤ := by
      rw [hE]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)) (measure_ne_top _ _)⟩
    have h1 := ENNReal.toReal_mono hne (hexp j)
    rw [ENNReal.toReal_add (by rw [hE]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
        (measure_ne_top _ _)), hE] at h1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hD0,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h1
    have hx := atom_le_lconc (∏ i, f' i).toMeasure j
    have hx0 : 0 ≤ ((∏ i, f' i).toMeasure {j}).toReal := ENNReal.toReal_nonneg
    have hp0 : (0 : ℝ) ≤ 2⁻¹ ^ A.card := by positivity
    calc ((∏ i, f i).toMeasure {j}).toReal
        ≤ 2 * a * D + 2⁻¹ ^ A.card * ((∏ i, f' i).toMeasure {j}).toReal := h1
      _ ≤ 2 * a * D + 1 / 4 * lconc (∏ i, f' i).toMeasure 1 := by
          gcongr
  calc lconc (∏ i, f i).toMeasure 1 * Real.sqrt m
      ≤ (2 * a * D + 1 / 4 * lconc (∏ i, f' i).toMeasure 1) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hmain hsqrt_pos.le
    _ = 2 * a * (D * Real.sqrt m) + 1 / 4 * (lconc (∏ i, f' i).toMeasure 1 * Real.sqrt m) := by
        ring
    _ ≤ 2 * a * (6 * C) + 1 / 4 * (24 * C * (2 * a)) := by
        rw [hDm]; gcongr
    _ = 24 * C * a := by ring

/-- Kesten (2.10)–(2.12): iterating the recursion until the atom bound reaches `[1/4, 1/2]`. -/
lemma bound_of_level {C : ℝ} (hC : RogozinLattice C) (h0 : 0 ≤ C) :
    ∀ r : ℕ, ∀ a : ℝ, 1 / 4 ≤ 2 ^ r * a → a ≤ 1 / 2 → Bound (24 * C) a
  | 0, a, h1, h2 => bound_base hC h0 (by simpa using h1) h2
  | r + 1, a, h1, h2 => by
    by_cases ha : 1 / 4 ≤ a
    · exact bound_base hC h0 ha h2
    · have ha0 : 0 ≤ a := by
        by_contra hlt
        have : (2 : ℝ) ^ (r + 1) * a < 0 := mul_neg_of_pos_of_neg (by positivity) (not_le.1 hlt)
        linarith
      rw [pow_succ, mul_assoc] at h1
      exact bound_step hC h0 ha0 (by linarith)
        (bound_of_level hC h0 r (2 * a) h1 (by linarith))

end Kesten

open Kesten

/-- The constant of `kesten_lattice`. -/
def KKes (C : ℝ) : ℝ := 32 * (1 + C)

/-- Kesten's inequality (1.6) for integer-valued iid summands and one-point windows
(`L = λ = 1/2`), given the lattice Kolmogorov–Rogozin inequality with constant `C`.
The hypothesis `lconc μ 1 < 1` is not needed by the proof. -/
theorem kesten_lattice {C : ℝ} (hC : RogozinLattice C) (h0 : 0 ≤ C) {μ : Measure ℤ}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (_hp : lconc μ 1 < 1) :
    lconc (convFin n (fun _ => μ)) 1 * Real.sqrt (n * (1 - lconc μ 1)) ≤
      KKes C * lconc μ 1 := by
  obtain ⟨f, hf⟩ : ∃ f : Fin n → Law, ∀ i, (f i).toMeasure = μ :=
    ⟨fun _ => ⟨μ, inferInstance⟩, fun _ => rfl⟩
  have hconv : convFin n (fun _ => μ) = (∏ i, f i).toMeasure := by
    rw [← convFin_eq_prod n f]
    simp only [hf]
  rw [hconv, KKes]
  have hp0 : 0 < lconc μ 1 := lconc_pos μ
  have hL0 := lconc_nonneg (∏ i, f i).toMeasure 1
  have hsq0 := Real.sqrt_nonneg (n * (1 - lconc μ 1))
  by_cases hbig : 1 / 16 < lconc μ 1
  · -- a large atom: Theorem 1 directly
    have h := rogozin_finset hC Finset.univ f 1 1 le_rfl le_rfl
    simp only [hf, Nat.cast_one, div_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    calc _ ≤ C * (1 + 1) := h
      _ ≤ 32 * (1 + C) * lconc μ 1 := by nlinarith
  · replace hbig := not_lt.1 hbig
    by_cases hn4 : 4 ≤ n
    · -- Kesten (2.7)
      obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 / (4 * lconc μ 1) < 2 ^ r :=
        pow_unbounded_of_one_lt _ (by norm_num)
      rw [div_lt_iff₀ (by positivity)] at hr
      have hB := bound_of_level hC h0 r (lconc μ 1) (by nlinarith) (by linarith) n hn4 f
        (fun i => by rw [hf])
      have hs : Real.sqrt (n * (1 - lconc μ 1)) ≤ Real.sqrt n :=
        Real.sqrt_le_sqrt (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      calc _ ≤ lconc (∏ i, f i).toMeasure 1 * Real.sqrt n := mul_le_mul_of_nonneg_left hs hL0
        _ ≤ 24 * C * lconc μ 1 := hB
        _ ≤ 32 * (1 + C) * lconc μ 1 := by nlinarith
    · -- few summands: Kesten (2.3)
      replace hn4 := not_le.1 hn4
      have hle : lconc (∏ i, f i).toMeasure 1 ≤ lconc μ 1 := by
        rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ ⟨0, hn⟩), Law.mul_toMeasure,
          ← hf ⟨0, hn⟩]
        exact lconc_conv_le_left _ _ 1
      have hs : Real.sqrt (n * (1 - lconc μ 1)) ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        refine Real.sqrt_le_sqrt ?_
        have : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc _ ≤ lconc μ 1 * 2 := mul_le_mul hle hs hsq0 hp0.le
        _ ≤ 32 * (1 + C) * lconc μ 1 := by nlinarith

end

end PGM
