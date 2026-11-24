import PLAStochastic.Index.KEP.CountRoute.LayerCount
import PLAStochastic.Index.KEP.Additive.OfReferenceCountTail

/-!
# Actual layer counts at the reference scale from the window quantile condition

Source: `pgm-analysis/research/2026-09-28-kep-additive/conditional-assembly.md`, §4–5
(condition (Q-finite) and the count bound (12)), and `count-route.md`, §3.1.

The window quantile condition `KepWindowQuantile Q eps0 a p Bc γ` is the finite-sample
condition (Q-finite) at the actual reference scale `m_L = kepReferenceSpan eps L`: for
`eps ≥ eps0`, every layer `L ≥ 1`, every number `m ≥ ⌈Bc eps^γ m_L⌉₊` of remaining sorted
uniforms and every anchor value `u ∈ [0, 1)`, the anchored pairs `anchPairsW Q u w`,
`w ∼ orderLaw m`, have second layer-`L` pivot of base rank `> ⌊a m_L⌋₊` with probability at
least `p`.  It is **assumed** here; its proof (window bridge and nonhomogeneous Poisson
kernel) is the remaining probabilistic input of the general-density additive theorem.

* **Transfer** (`integral_epLayer_snd_kKeys_eq_orderLaw`): the expected layer size of the
  sorted Model K sample equals that of `quantK f A B ∘ v`, `v ∼ orderLaw N`.
* **Reference ratio** (`kepReferenceSpan_succ_le`, `kepReferenceSpan_count_budget`):
  `m_{L+1} ≤ K eps² m_L` and `1 ≤ m_L` for large `eps`.
* **Count input** (`integral_epLayer_snd_kKeys_le_of_windowQuantile`): under the window
  quantile condition, `E[layer-L size] ≤ A' n / m_L + D' eps^(γ+2)` for all `n`, `L` and
  large `eps`, which is the hypothesis `hcount` of `H_EP_additive_of_reference_count_tail`.
* **Assembly** (`H_EP_additive_kKeys_of_windowQuantile_tail`): with the early-termination
  tail bound `htail` as the second remaining input, the additive `O(1)` height formula holds
  for general Model K densities.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-! ## Transfer of the layer size to the sorted-uniform representation -/

theorem measurable_kKeys {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (kKeys X n) :=
  measurable_extendKeys.comp (Renyi.measurable_sortVec.comp
    (measurable_pi_lambda _ fun i => hX i))

omit [IsProbabilityMeasure P] in
/-- **Sorted sample law, layer size.** -/
theorem integral_epLayer_snd_kKeys_eq_orderLaw (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (N L : ℕ) :
    ∫ ω, ((epLayer eps (kKeys X N ω) N L).2 : ℝ) ∂P =
      ∫ v, ((epLayer eps (extendKeys (quantK f A B ∘ v)) N L).2 : ℝ) ∂(Renyi.orderLaw N) := by
  have hid := identDistrib_sortVec_quantK_orderLaw hf (fun i : Fin N => hX i)
    (hind.precomp Fin.val_injective)
  have hu : Measurable fun v : Fin N → ℝ => ((epLayer eps (extendKeys v) N L).2 : ℝ) :=
    measurable_from_nat.comp
      ((measurable_snd.comp (measurable_epLayer eps N L)).comp measurable_extendKeys)
  exact (hid.comp hu).integral_eq

/-! ## The reference scale: ratio and lower bound -/

/-- `m_{j+1} ≤ K eps² m_j` at the actual reference scale, for large `eps`. -/
theorem kepReferenceSpan_succ_le :
    ∃ eps0 K : ℝ, 0 ≤ K ∧ ∀ eps, eps0 ≤ eps → ∀ j,
      kepReferenceSpan eps (j + 1) ≤ K * eps ^ 2 * kepReferenceSpan eps j := by
  have hg := gapLaw_expCoord
  refine ⟨epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))),
    cBr (bIn 1 1) (vIn 1 1), by linarith [one_le_cBr (vmin := vIn 1 1) (bAbs_le_bIn 1 1)], ?_⟩
  intro eps heps j
  have hL := layerOK_all (layerOK_input hg) (bAbs_le_bIn 1 1) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le 1 1) KcAbs_le_KcIn heps
  have hpos : 0 < kepReferenceSpan eps j := (hL j).1.cnt_pos
  have hstep : kepReferenceSpan eps (j + 1) =
      kepReferenceSpan eps j * segMean expSeqMeasure eps (epLayerSeq eps expCoord j) :=
    (hL j).2.2.1
  rw [hstep]
  calc kepReferenceSpan eps j * segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
      ≤ kepReferenceSpan eps j * (cBr (bIn 1 1) (vIn 1 1) * eps ^ 2) :=
        mul_le_mul_of_nonneg_left (segMean_bracket hg heps j).2 hpos.le
    _ = _ := by ring

/-- Reference-scale facts used by the count route: `m_0 = 1`, `1 ≤ m_j`, `m_{j+1} ≤ K eps² m_j`. -/
theorem kepReferenceSpan_count_budget :
    ∃ eps0 K : ℝ, 2 ≤ eps0 ∧ 0 ≤ K ∧ ∀ eps, eps0 ≤ eps →
      kepReferenceSpan eps 0 = 1 ∧ (∀ j, 1 ≤ kepReferenceSpan eps j) ∧
      ∀ j, kepReferenceSpan eps (j + 1) ≤ K * eps ^ 2 * kepReferenceSpan eps j := by
  obtain ⟨e0, B, he0, -, hb⟩ := kepReferenceSpan_budget
  obtain ⟨e1, K, hK, hr⟩ := kepReferenceSpan_succ_le
  refine ⟨max e0 e1, K, le_trans he0 (le_max_left _ _), hK, fun eps heps => ?_⟩
  obtain ⟨h0, -, h2, -, -⟩ := hb eps (le_trans (le_max_left _ _) heps)
  refine ⟨h0, ?_, hr eps (le_trans (le_max_right _ _) heps)⟩
  intro j
  induction j with
  | zero => rw [h0]
  | succ j ih => have := h2 j; linarith

/-! ## The window quantile condition -/

/-- **Window quantile condition (Q-finite) at the reference scale.**  For `eps ≥ eps0`, every
    layer `L ≥ 1`, every number `m ≥ ⌈Bc eps^γ m_L⌉₊` of remaining sorted uniforms and every
    anchor value `u ∈ [0, 1)`, the anchored pairs with key map `Q` have second layer-`L`
    pivot of base rank `> ⌊a m_L⌋₊` with probability at least `p`, `m_L = kepReferenceSpan eps L`. -/
def KepWindowQuantile (Q : ℝ → ℝ) (eps0 a p Bc γ : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ m : ℕ, ⌈Bc * eps ^ γ * kepReferenceSpan eps L⌉₊ ≤ m →
    ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤ Renyi.orderLaw m
        {w | ⌊a * kepReferenceSpan eps L⌋₊ + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1}

/-! ## The count input -/

/-- **Actual layer counts from the window quantile condition.**  For a Model K sample with
    density `f` and the window quantile condition for its quantile map, there are `eps1`,
    `A' ≥ 1` and `D' ≥ 0` with `E[layer-L size] ≤ A' n / m_L + D' eps^(γ+2)` for every
    `eps ≥ eps1`, every sample size `n` and every layer `L`. -/
theorem integral_epLayer_snd_kKeys_le_of_windowQuantile (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 a p Bc γ : ℝ} (ha : 0 < a) (hp : 0 < p) (hBc : 0 ≤ Bc) (hγ : 0 ≤ γ)
    (hQ : KepWindowQuantile (quantK f A B) eps0 a p Bc γ) :
    ∃ eps1 A' D' : ℝ, 1 ≤ A' ∧ 0 ≤ D' ∧ ∀ eps, eps1 ≤ eps → ∀ n : ℕ, ∀ L,
      ∫ ω, ((epLayer eps (kKeys X n ω) n L).2 : ℝ) ∂P ≤
        A' * (n : ℝ) / kepReferenceSpan eps L + D' * eps ^ (γ + 2) := by
  obtain ⟨e0, K, he0, hK, hbud⟩ := kepReferenceSpan_count_budget
  refine ⟨max eps0 e0, max 1 (1 / (a * p)),
    4 / p + (Bc * K + 1) / (a * p) + 5 + Bc + Bc * K, le_max_left _ _, by positivity, ?_⟩
  intro eps heps n L
  have heps0 : eps0 ≤ eps := le_trans (le_max_left _ _) heps
  have he : e0 ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := by linarith
  have hepspos : 0 < eps := by linarith
  obtain ⟨hm0, hm1, hratio⟩ := hbud eps he
  have hmpos : ∀ j, 0 < kepReferenceSpan eps j := fun j => by linarith [hm1 j]
  set E : ℝ := eps ^ (γ + 2) with hEdef
  have hpowγ : 0 ≤ eps ^ γ := Real.rpow_nonneg hepspos.le γ
  have hsplit : E = eps ^ γ * eps ^ 2 := by
    rw [hEdef, Real.rpow_add hepspos, Real.rpow_two]
  have hE1 : 1 ≤ E := Real.one_le_rpow heps1 (by linarith)
  have hE0 : 0 ≤ E := by linarith
  have hγle : eps ^ γ ≤ E := Real.rpow_le_rpow_of_exponent_le heps1 (by linarith)
  have hepsle : eps ≤ E := by
    have := Real.rpow_le_rpow_of_exponent_le heps1 (show (1 : ℝ) ≤ γ + 2 by linarith)
    rwa [Real.rpow_one] at this
  have hD'E : 0 ≤ (4 / p + (Bc * K + 1) / (a * p) + 5 + Bc + Bc * K) * E := by positivity
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · -- layer `0` has `n` keys
    have h0 : ∀ ω, ((epLayer eps (kKeys X n ω) n 0).2 : ℝ) = n := fun ω => rfl
    simp only [h0, integral_const, probReal_univ, one_smul]
    rw [hm0, div_one]
    have hA1 : (1 : ℝ) ≤ max 1 (1 / (a * p)) := le_max_left _ _
    have hn : (n : ℝ) ≤ max 1 (1 / (a * p)) * n :=
      le_mul_of_one_le_left (Nat.cast_nonneg n) hA1
    linarith
  · rw [integral_epLayer_snd_kKeys_eq_orderLaw hf hX hind eps n L]
    set D : ℕ → ℕ := fun j => ⌈Bc * eps ^ γ * kepReferenceSpan eps j⌉₊ with hDdef
    set g : ℕ → ℕ := fun j => ⌊a * kepReferenceSpan eps j⌋₊ + 1 with hgdef
    have hg : ∀ j, 1 ≤ g j := fun j => Nat.le_add_left 1 _
    have hgreal : ∀ j, a * kepReferenceSpan eps j ≤ (g j : ℝ) := fun j => by
      simp only [hgdef]
      push_cast
      exact (Nat.lt_floor_add_one _).le
    have hgpos : ∀ j, 0 < (g j : ℝ) := fun j =>
      lt_of_lt_of_le (mul_pos ha (hmpos j)) (hgreal j)
    have hDreal : ∀ j, (D j : ℝ) ≤ Bc * eps ^ γ * kepReferenceSpan eps j + 1 := fun j => by
      simp only [hDdef]
      exact (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hBc hpowγ) (hmpos j).le)).le
    set Wb : ℝ := (Bc * K * E + 1) / a with hWbdef
    have hW : ∀ j, 1 ≤ j → (D (j + 1) : ℝ) / g j ≤ Wb := by
      intro j _
      rw [div_le_iff₀ (hgpos j)]
      have hr := hratio j
      have hm := hm1 j
      have h1 : Bc * eps ^ γ * kepReferenceSpan eps (j + 1) ≤
          Bc * eps ^ γ * (K * eps ^ 2 * kepReferenceSpan eps j) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      calc (D (j + 1) : ℝ) ≤ Bc * eps ^ γ * kepReferenceSpan eps (j + 1) + 1 := hDreal (j + 1)
        _ ≤ Bc * eps ^ γ * (K * eps ^ 2 * kepReferenceSpan eps j) + kepReferenceSpan eps j := by
            linarith
        _ = (Bc * K * E + 1) * kepReferenceSpan eps j := by rw [hsplit]; ring
        _ = Wb * (a * kepReferenceSpan eps j) := by
            rw [hWbdef]
            field_simp
        _ ≤ Wb * g j := mul_le_mul_of_nonneg_left (hgreal j) (by positivity)
    have hS : ∀ L, 1 ≤ L → ∀ r m, r + 1 + m = n → D L ≤ m → ∀ u : ℝ, 0 ≤ u → u < 1 →
        ENNReal.ofReal p ≤ Renyi.orderLaw m
          {w | g L ≤ layerPivot eps (anchPairsW (quantK f A B) u w) L 1} :=
      fun L hL _ m _ hm u hu0 hu1 => hQ eps heps0 L hL m hm u hu0 hu1
    have hmain := integral_epLayer_snd_le_of_window_quantile (measurable_quantK hf)
      (by linarith : 1 / 2 ≤ eps) hg hp hW hS hL
    refine hmain.trans ?_
    -- head term
    have t1 : ((n : ℝ) / g L + 2) / p ≤
        max 1 (1 / (a * p)) * n / kepReferenceSpan eps L + 2 / p * E := by
      have h1 : (n : ℝ) / g L ≤ n / (a * kepReferenceSpan eps L) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg n) (mul_pos ha (hmpos L)) (hgreal L)
      have h2 : (n : ℝ) / (a * kepReferenceSpan eps L) / p =
          1 / (a * p) * n / kepReferenceSpan eps L := by
        field_simp
      have h3 : 1 / (a * p) * n / kepReferenceSpan eps L ≤
          max 1 (1 / (a * p)) * n / kepReferenceSpan eps L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg n)) (hmpos L).le
      have h4 : 2 / p ≤ 2 / p * E := le_mul_of_one_le_right (by positivity) hE1
      have h5 : (n : ℝ) / g L / p ≤ n / (a * kepReferenceSpan eps L) / p :=
        div_le_div_of_nonneg_right h1 hp.le
      rw [add_div]
      linarith
    -- bridge remainder
    have t2 : (Wb + 2) / p ≤ ((Bc * K + 1) / (a * p) + 2 / p) * E := by
      have h1 : Wb / p = (Bc * K * E + 1) / (a * p) := by rw [hWbdef, div_div]
      have h2 : Bc * K * E + 1 ≤ (Bc * K + 1) * E := by nlinarith
      have h3 : (Bc * K * E + 1) / (a * p) ≤ (Bc * K + 1) * E / (a * p) :=
        div_le_div_of_nonneg_right h2 (by positivity)
      have h4 : 2 / p ≤ 2 / p * E := le_mul_of_one_le_right (by positivity) hE1
      have h5 : (Bc * K + 1) * E / (a * p) = (Bc * K + 1) / (a * p) * E := by ring
      rw [add_div]
      linarith
    -- `q = ⌊2 eps⌋₊ + 1 ≤ 3 E`
    have t3 : (⌊2 * eps⌋₊ + 1 : ℝ) ≤ 3 * E := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * eps)
      linarith
    -- `D 0 ≤ (Bc + 1) E`
    have t4 : (D 0 : ℝ) ≤ (Bc + 1) * E := by
      have h := hDreal 0
      rw [hm0, mul_one] at h
      have : Bc * eps ^ γ ≤ Bc * E := mul_le_mul_of_nonneg_left hγle hBc
      linarith
    -- `D 1 ≤ (Bc K + 1) E`
    have t5 : (D 1 : ℝ) ≤ (Bc * K + 1) * E := by
      have h := hDreal 1
      have h1 : Bc * eps ^ γ * kepReferenceSpan eps 1 ≤
          Bc * eps ^ γ * (K * eps ^ 2 * kepReferenceSpan eps 0) :=
        mul_le_mul_of_nonneg_left (hratio 0) (by positivity)
      rw [hm0, mul_one] at h1
      have h2 : Bc * eps ^ γ * (K * eps ^ 2) = Bc * K * E := by rw [hsplit]; ring
      linarith
    have hsum := add_le_add t1 (add_le_add (add_le_add (add_le_add t2 t3) t4) t5)
    refine hsum.trans (le_of_eq ?_)
    ring

/-! ## Assembly with the early-termination tail -/

/-- **Additive height for general Model K from (Q-finite) and the tail bound.**  Under the
    window quantile condition for the quantile map of `f` and the early-termination tail
    bound at the reference scale, the expected ALG-PGM height of the sorted Model K sample
    is `log n / log C_eps + O(1)`. -/
theorem H_EP_additive_kKeys_of_windowQuantile_tail (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 a p Bc γ : ℝ} (ha : 0 < a) (hp : 0 < p) (hBc : 0 ≤ Bc) (hγ : 0 ≤ γ)
    (hQ : KepWindowQuantile (quantK f A B) eps0 a p Bc γ)
    {R K r : ℝ} (hR : 1 ≤ R) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (htail : ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n → ∀ L,
      (R * eps ^ r) * kepReferenceSpan eps L < n →
        P.real {ω | epHeight eps (kKeys X n ω) n ≤ L} ≤ K * kepReferenceSpan eps L / n) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C := by
  obtain ⟨e1, A', D', hA', hD', hcount⟩ :=
    integral_epLayer_snd_kKeys_le_of_windowQuantile hf hX hind ha hp hBc hγ hQ
  refine H_EP_additive_of_reference_count_tail (keys := kKeys X) (measurable_kKeys hXm)
    (eps0 := max eps0 e1) hA' hD' hR hK (by linarith : (0 : ℝ) ≤ γ + 2) hr ?_ ?_
  · intro eps heps n _ L
    exact hcount eps (le_trans (le_max_right _ _) heps) n L
  · intro eps heps
    exact htail eps (le_trans (le_max_left _ _) heps)

end

end PGM
