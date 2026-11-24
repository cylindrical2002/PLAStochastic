import PLAStochastic.Index.Model.IIDPairs
import PLAStochastic.Index.Model.ExpConcentration
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The uniform maximal Bernstein estimate and the early PLA stop

Source: `theory/proofs/proofK_local_count_core.tex`, `klc:lem:maximal-bernstein`.

For an iid pair sequence `Z` (`IIDPairs`) with positive integer counts `N = (Z 0).2`, the Gamma
kernel `P(g ∈ A, N = n) = P(N = n) · Gamma(n, 1)(A)` for the gaps `g = (Z 0).1`, `E N = m₀`
and `E e^{θ N/m₀} ≤ B`:

* `lcbb_centred_moments`: `X = g/m₀ - 1` has `E X = 0` and `E e^{η₀|X|} ≤ e^{η₀} B`,
  `η₀ = min(1/4, θ/2)` (via the Gamma transforms `lcbb_gamma_mgf`, `lcbb_gamma_mean` and the
  kernel transfer `lcbb_setLIntegral_fst`);
* `lcbb_mgf_quad`: `1 ≤ E e^{λX} ≤ 1 + C₀ λ²` for `|λ| ≤ η₀/2`, `C₀ = 8 e^{η₀} B/η₀²`;
* `lcbb_maximal_exp`: the first-passage maximal inequality
  `P(∃ j ≤ s, x ≤ V_j) e^{λx} ≤ (E e^{λ φ(Z 0)})^s` (no union bound over `j`);
* `maximal_bernstein`: `P(max_{j ≤ s} |∑_{i<j} (gᵢ/m₀ - 1)| > x) ≤ 2 exp(-c min(x²/s, x))`
  with `c = bernsteinRate θ B = min(1/(4C₀), η₀/4)`;
* `pairSegLen_le_prob`: `P(pairSegLen eps ≤ s) ≤ 2 exp(-c min(eps²/s, eps))`;
* `floor_two_eps_lt_pairSegLen`: deterministically `⌊2 eps⌋ < pairSegLen eps`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace PGM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

/-- Normalized centred gap walk `W_j = ∑_{i<j} (g_i/m₀ - 1)`. -/
def gapWalk (m₀ : ℝ) (Z : ℕ → Ω → ℝ × ℕ) (j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, ((Z i ω).1 / m₀ - 1)

/-- Exponent parameter `η₀ = min(1/4, θ/2)`. -/
def bernsteinEta (θ : ℝ) : ℝ := min (1 / 4) (θ / 2)
/-- Quadratic cgf constant `C₀ = 8 e^{η₀} B / η₀²`. -/
def bernsteinC0 (θ B : ℝ) : ℝ := 8 * Real.exp (bernsteinEta θ) * B / bernsteinEta θ ^ 2
/-- Rate `c = min(1/(4 C₀), η₀/4)`. -/
def bernsteinRate (θ B : ℝ) : ℝ := min (1 / (4 * bernsteinC0 θ B)) (bernsteinEta θ / 4)

theorem lcbb_eta_pos {θ : ℝ} (hθ : 0 < θ) : 0 < bernsteinEta θ :=
  lt_min (by norm_num) (by linarith)

theorem lcbb_eta_le_quarter (θ : ℝ) : bernsteinEta θ ≤ 1 / 4 := min_le_left _ _

theorem lcbb_two_eta_le (θ : ℝ) : 2 * bernsteinEta θ ≤ θ := by
  have := min_le_right (1 / 4 : ℝ) (θ / 2)
  unfold bernsteinEta
  linarith

theorem lcbb_C0_pos {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B) : 0 < bernsteinC0 θ B := by
  have := lcbb_eta_pos hθ
  unfold bernsteinC0
  positivity

theorem bernsteinRate_pos {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B) : 0 < bernsteinRate θ B := by
  have h1 := lcbb_C0_pos hθ hB
  have h2 := lcbb_eta_pos hθ
  exact lt_min (by positivity) (by positivity)

/-- Early stop, deterministic part: `T > ⌊2 eps⌋`. -/
theorem floor_two_eps_lt_pairSegLen {eps : ℝ} (heps : 0 ≤ eps) (z : ℕ → ℝ × ℕ) :
    ((⌊2 * eps⌋₊ : ℕ) : ℕ∞) < pairSegLen eps z := by
  have h := constantLine_le_segLen (ConstantLineLengthCertificate.of_nonneg heps) (pairKeys z)
  have hq : ((ConstantLineLengthCertificate.of_nonneg heps).q : ℕ∞) =
      ((⌊2 * eps⌋₊ : ℕ) : ℕ∞) + 1 := by
    simp [ConstantLineLengthCertificate.of_nonneg]
  rw [hq] at h
  exact (ENat.add_one_le_iff (ENat.natCast_ne_top _)).1 h

/-! ## Elementary inequalities -/

theorem lcbb_exp_le_quad (y : ℝ) : Real.exp y ≤ 1 + y + y ^ 2 * Real.exp |y| := by
  have he : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
  rcases le_or_gt |y| 1 with hy | hy
  · have h := Real.abs_exp_sub_one_sub_id_le hy
    have h' := (abs_le.1 h).2
    have : y ^ 2 ≤ y ^ 2 * Real.exp |y| := le_mul_of_one_le_right (sq_nonneg y) he
    linarith
  · rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy ⊢
      have : 1 ≤ y ^ 2 := by nlinarith
      have hpos := Real.exp_pos y
      nlinarith
    · rw [abs_of_neg h0] at hy ⊢
      have h1 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h2 : 1 + (-y) ≤ Real.exp (-y) := by
        have := Real.add_one_le_exp (-y); linarith
      have h3 : y ^ 2 * (1 + -y) ≤ y ^ 2 * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg y)
      nlinarith

theorem lcbb_sq_le_two_exp {w : ℝ} (hw : 0 ≤ w) : w ^ 2 ≤ 2 * Real.exp w := by
  have := Real.quadratic_le_exp_of_nonneg hw
  nlinarith

/-- `X² e^{|λ X|} ≤ (8/η²) e^{η |X|}` for `|λ| ≤ η/2`. -/
theorem lcbb_sq_mul_exp_le {η l X : ℝ} (hη : 0 < η) (hl : |l| ≤ η / 2) :
    X ^ 2 * Real.exp |l * X| ≤ 8 / η ^ 2 * Real.exp (η * |X|) := by
  set w := η * |X| / 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 : Real.exp |l * X| ≤ Real.exp w := by
    apply Real.exp_le_exp.2
    rw [abs_mul, hw]
    have := mul_le_mul_of_nonneg_right hl (abs_nonneg X)
    linarith
  have h2 : X ^ 2 = 4 / η ^ 2 * w ^ 2 := by
    rw [hw, div_pow, mul_pow, ← sq_abs X]
    field_simp
    ring
  have h3 := lcbb_sq_le_two_exp hw0
  have h4 : Real.exp (η * |X|) = Real.exp w * Real.exp w := by
    rw [← Real.exp_add]; congr 1; rw [hw]; ring
  rw [h4, h2]
  have hpos : 0 < Real.exp w := Real.exp_pos w
  have hη2 : 0 < η ^ 2 := by positivity
  calc 4 / η ^ 2 * w ^ 2 * Real.exp |l * X| ≤ 4 / η ^ 2 * (2 * Real.exp w) * Real.exp w := by
        gcongr
    _ = 8 / η ^ 2 * (Real.exp w * Real.exp w) := by ring
/-! ## The quadratic mgf bound -/

/-- If `E X = 0` and `E e^{η |X|} ≤ K`, then for `|λ| ≤ η/2`,
`1 ≤ E e^{λ X} ≤ 1 + λ² (8/η²) K`. -/
theorem lcbb_mgf_quad [IsProbabilityMeasure P] {X : Ω → ℝ} (hXm : Measurable X)
    (hXi : Integrable X P) (hX0 : ∫ ω, X ω ∂P = 0) {η K : ℝ} (hη : 0 < η)
    (hK : Integrable (fun ω => Real.exp (η * |X ω|)) P)
    (hKle : ∫ ω, Real.exp (η * |X ω|) ∂P ≤ K) {l : ℝ} (hl : |l| ≤ η / 2) :
    Integrable (fun ω => Real.exp (l * X ω)) P ∧ 1 ≤ ∫ ω, Real.exp (l * X ω) ∂P ∧
      ∫ ω, Real.exp (l * X ω) ∂P ≤ 1 + l ^ 2 * (8 / η ^ 2 * K) := by
  have hint : Integrable (fun ω => Real.exp (l * X ω)) P := by
    refine hK.mono' (hXm.const_mul l).exp.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have h1 : l * X ω ≤ |l| * |X ω| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : |l| * |X ω| ≤ η * |X ω| :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg l]) (abs_nonneg _)
    linarith
  have hlin : Integrable (fun ω => 1 + l * X ω) P := (integrable_const 1).add (hXi.const_mul l)
  have hlin_int : ∫ ω, (1 + l * X ω) ∂P = 1 := by
    rw [integral_add (integrable_const 1) (hXi.const_mul l), integral_const_mul, hX0]
    simp
  refine ⟨hint, ?_, ?_⟩
  · rw [← hlin_int]
    exact integral_mono hlin hint fun ω => by
      have := Real.add_one_le_exp (l * X ω); linarith
  · have hup : Integrable (fun ω => 1 + l * X ω + l ^ 2 * (8 / η ^ 2 * Real.exp (η * |X ω|))) P :=
      hlin.add ((hK.const_mul (8 / η ^ 2)).const_mul (l ^ 2))
    calc ∫ ω, Real.exp (l * X ω) ∂P
        ≤ ∫ ω, (1 + l * X ω + l ^ 2 * (8 / η ^ 2 * Real.exp (η * |X ω|))) ∂P := by
          refine integral_mono hint hup fun ω => ?_
          have h1 := lcbb_exp_le_quad (l * X ω)
          have h2 := lcbb_sq_mul_exp_le (X := X ω) hη hl
          have h3 : (l * X ω) ^ 2 * Real.exp |l * X ω| =
              l ^ 2 * (X ω ^ 2 * Real.exp |l * X ω|) := by ring
          have h4 : l ^ 2 * (X ω ^ 2 * Real.exp |l * X ω|) ≤
              l ^ 2 * (8 / η ^ 2 * Real.exp (η * |X ω|)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg l)
          linarith
      _ = 1 + l ^ 2 * (8 / η ^ 2 * ∫ ω, Real.exp (η * |X ω|) ∂P) := by
          rw [integral_add hlin ((hK.const_mul (8 / η ^ 2)).const_mul (l ^ 2)), hlin_int,
            integral_const_mul, integral_const_mul]
      _ ≤ 1 + l ^ 2 * (8 / η ^ 2 * K) := by
          gcongr
/-! ## Exponential moments of block sums -/

/-- For an iid pair sequence, the exponential moment of a sum of `φ (Z i)` over a finite
index set is the power of the one-step exponential moment. -/
theorem lcbb_block_mgf [IsProbabilityMeasure P] (h : IIDPairs P Z) {φ : ℝ × ℕ → ℝ}
    (hφ : Measurable φ) (l : ℝ) (hint : Integrable (fun ω => Real.exp (l * φ (Z 0 ω))) P)
    (S : Finset ℕ) :
    Integrable (fun ω => Real.exp (l * ∑ i ∈ S, φ (Z i ω))) P ∧
      ∫ ω, Real.exp (l * ∑ i ∈ S, φ (Z i ω)) ∂P =
        (∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P) ^ S.card := by
  have hind : iIndepFun (fun i => φ ∘ Z i) P := h.indep.comp (fun _ => φ) (fun _ => hφ)
  have hm : ∀ i, Measurable (φ ∘ Z i) := fun i => hφ.comp (h.measurable i)
  have hid : ∀ i, IdentDistrib (fun ω => Real.exp (l * φ (Z i ω)))
      (fun ω => Real.exp (l * φ (Z 0 ω))) P P := fun i =>
    (h.ident i).comp (u := fun z => Real.exp (l * φ z)) (hφ.const_mul l).exp
  have hi : ∀ i, Integrable (fun ω => Real.exp (l * φ (Z i ω))) P := fun i =>
    (hid i).integrable_iff.2 hint
  constructor
  · have := hind.integrable_exp_mul_sum (t := l) hm (s := S) (fun i _ => hi i)
    simpa [Finset.sum_apply] using this
  · have := hind.mgf_sum (t := l) hm S
    simp only [mgf, Finset.sum_apply, Function.comp_apply] at this
    rw [this, Finset.prod_congr rfl (fun i _ => (hid i).integral_eq), Finset.prod_const]
/-! ## The first-passage maximal inequality -/

/-- **Maximal exponential inequality.**  For `V_j = ∑_{i<j} φ (Z i)`, `λ ≥ 0` and
`M = E e^{λ φ (Z 0)} ≥ 1`: `P(∃ j ≤ s, x ≤ V_j) e^{λ x} ≤ M^s`.  The proof decomposes the
event by the first passage index `j` and uses the independence of `1_{D_j} e^{λ V_j}` from
the future increments `V_s - V_j`. -/
theorem lcbb_maximal_exp [IsProbabilityMeasure P] (h : IIDPairs P Z) {φ : ℝ × ℕ → ℝ}
    (hφ : Measurable φ) {l : ℝ} (hl : 0 ≤ l)
    (hint : Integrable (fun ω => Real.exp (l * φ (Z 0 ω))) P)
    (hM : 1 ≤ ∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P) (s : ℕ) (x : ℝ) :
    P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} * Real.exp (l * x) ≤
      (∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P) ^ s := by
  classical
  set M := ∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P with hMdef
  set F := pairFiltration Z h.measurable with hF
  set V : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range j, φ (Z i ω) with hV
  set D : ℕ → Set Ω := fun j => {ω | x ≤ V j ω ∧ ∀ i < j, V i ω < x} with hDdef
  have hVF : ∀ i j, i ≤ j → Measurable[F j] (V i) := by
    intro i j hij
    exact Finset.measurable_sum _ fun k hk =>
      hφ.comp (pairFiltration_measurable_lt h.measurable
        (by rw [Finset.mem_range] at hk; omega))
  have hDF : ∀ j, MeasurableSet[F j] (D j) := by
    intro j
    have : D j = {ω | x ≤ V j ω} ∩ ⋂ i, ⋂ (_ : i < j), {ω | V i ω < x} := by
      ext ω; simp [D]
    rw [this]
    refine MeasurableSet.inter (measurableSet_le measurable_const (hVF j j le_rfl)) ?_
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      measurableSet_lt (hVF i j hi.le) measurable_const
  have hD : ∀ j, MeasurableSet (D j) := fun j => F.le j _ (hDF j)
  have hVm : ∀ j, Measurable (V j) := fun j => (hVF j j le_rfl).mono (F.le j) le_rfl
  have hVint : ∀ j, Integrable (fun ω => Real.exp (l * V j ω)) P := fun j =>
    (lcbb_block_mgf h hφ l hint (Finset.range j)).1
  have hVs : ∫ ω, Real.exp (l * V s ω) ∂P = M ^ s := by
    rw [(lcbb_block_mgf h hφ l hint (Finset.range s)).2, Finset.card_range]
  -- disjointness of the first-passage events
  have hdisj : ∀ j k ω, ω ∈ D j → ω ∈ D k → j = k := by
    intro j k ω hj hk
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · exact absurd (hk.2 j hjk) (not_lt.2 hj.1)
    · exact hjk
    · exact absurd (hj.2 k hjk) (not_lt.2 hk.1)
  -- the event is covered by the first-passage events
  have hcover : {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} ⊆
      ⋃ j ∈ Finset.range (s + 1), D j := by
    intro ω hω
    have hex : ∃ j, x ≤ V j ω := by
      obtain ⟨j, _, hj⟩ := hω
      exact ⟨j, hj⟩
    obtain ⟨j, hjs, hj⟩ := hω
    refine Set.mem_iUnion₂.2 ⟨Nat.find hex, ?_, Nat.find_spec hex, fun i hi => ?_⟩
    · rw [Finset.mem_range]
      have := Nat.find_min' hex hj
      omega
    · exact not_le.1 (Nat.find_min hex hi)
  -- the key estimate for each first-passage event
  have hkey : ∀ j ∈ Finset.range (s + 1), P.real (D j) * Real.exp (l * x) ≤
      ∫ ω, (D j).indicator (fun ω => Real.exp (l * V s ω)) ω ∂P := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjs : j ≤ s := by omega
    set A : Ω → ℝ := (D j).indicator (fun ω => Real.exp (l * V j ω)) with hA
    set G : (ℕ → ℝ × ℕ) → ℝ :=
      fun z => Real.exp (l * ∑ t ∈ Finset.range (s - j), φ (z t)) with hG
    set fut : Ω → ℕ → ℝ × ℕ := fun ω t => Z (j + t) ω with hfut
    have hGm : Measurable G :=
      ((Finset.measurable_sum _ fun t _ => hφ.comp (measurable_pi_apply t)).const_mul l).exp
    have hAF : Measurable[F j] A :=
      (((hVF j j le_rfl).const_mul l).exp).indicator (hDF j)
    have hAm : Measurable A := hAF.mono (F.le j) le_rfl
    have hfutm : Measurable fut := measurable_pi_lambda _ fun t => h.measurable (j + t)
    have hBm : Measurable (G ∘ fut) := hGm.comp hfutm
    have hind : IndepFun A (G ∘ fut) P := by
      have h1 := indep_future_pairFiltration h j
      have h2 : Indep (MeasurableSpace.comap (G ∘ fut) inferInstance)
          (MeasurableSpace.comap A inferInstance) P :=
        indep_of_indep_of_le_left (indep_of_indep_of_le_right h1 hAF.comap_le)
          (hGm.comp (comap_measurable fut)).comap_le
      exact ((IndepFun_iff_Indep _ _ _).2 h2).symm
    have hB : ∀ ω, (G ∘ fut) ω = Real.exp (l * ∑ i ∈ Finset.Ico j s, φ (Z i ω)) := by
      intro ω
      simp only [Function.comp_apply, hG, hfut]
      rw [Finset.sum_Ico_eq_sum_range]
    have hBint : ∫ ω, (G ∘ fut) ω ∂P = M ^ (s - j) := by
      simp_rw [hB]
      rw [(lcbb_block_mgf h hφ l hint (Finset.Ico j s)).2, Nat.card_Ico]
    have hprod : ∀ ω, A ω * (G ∘ fut) ω = (D j).indicator (fun ω => Real.exp (l * V s ω)) ω := by
      intro ω
      rw [hB, hA]
      by_cases hω : ω ∈ D j
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ← Real.exp_add, ← mul_add]
        simp only [hV]
        rw [Finset.sum_range_add_sum_Ico _ hjs]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    have hAint : P.real (D j) * Real.exp (l * x) ≤ ∫ ω, A ω ∂P := by
      rw [← smul_eq_mul, ← integral_indicator_const _ (hD j)]
      refine integral_mono ((integrable_const _).indicator (hD j)) ((hVint j).indicator (hD j))
        fun ω => ?_
      by_cases hω : ω ∈ D j
      · rw [hA, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω.1 hl)
      · rw [hA, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    have hA0 : 0 ≤ ∫ ω, A ω ∂P := integral_nonneg fun ω => by
      rw [hA]; exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) ω
    calc P.real (D j) * Real.exp (l * x) ≤ ∫ ω, A ω ∂P := hAint
      _ ≤ (∫ ω, A ω ∂P) * M ^ (s - j) := le_mul_of_one_le_right hA0 (one_le_pow₀ hM)
      _ = ∫ ω, A ω * (G ∘ fut) ω ∂P := by
        rw [← hBint]
        exact (hind.integral_mul_eq_mul_integral hAm.aestronglyMeasurable
          hBm.aestronglyMeasurable).symm
      _ = ∫ ω, (D j).indicator (fun ω => Real.exp (l * V s ω)) ω ∂P := by
        simp_rw [hprod]
  -- pointwise, the first-passage indicators sum to at most one
  have hsum_le : ∀ ω, ∑ j ∈ Finset.range (s + 1),
      (D j).indicator (fun ω => Real.exp (l * V s ω)) ω ≤ Real.exp (l * V s ω) := by
    intro ω
    by_cases hω : ∃ j ∈ Finset.range (s + 1), ω ∈ D j
    · obtain ⟨j₀, hj₀, hωj₀⟩ := hω
      rw [Finset.sum_eq_single j₀ (fun k _ hk => Set.indicator_of_notMem
        (fun hωk => hk (hdisj k j₀ ω hωk hωj₀)) _) (fun h => absurd hj₀ h),
        Set.indicator_of_mem hωj₀]
    · simp only [not_exists, not_and] at hω
      rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hω j hj) _]
      exact (Real.exp_pos _).le
  calc P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} * Real.exp (l * x)
      ≤ (∑ j ∈ Finset.range (s + 1), P.real (D j)) * Real.exp (l * x) := by
        gcongr
        exact (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    _ = ∑ j ∈ Finset.range (s + 1), P.real (D j) * Real.exp (l * x) := Finset.sum_mul _ _ _
    _ ≤ ∑ j ∈ Finset.range (s + 1),
        ∫ ω, (D j).indicator (fun ω => Real.exp (l * V s ω)) ω ∂P := Finset.sum_le_sum hkey
    _ = ∫ ω, ∑ j ∈ Finset.range (s + 1),
        (D j).indicator (fun ω => Real.exp (l * V s ω)) ω ∂P :=
        (integral_finsetSum _ fun j _ => (hVint s).indicator (hD j)).symm
    _ ≤ ∫ ω, Real.exp (l * V s ω) ∂P :=
        integral_mono (integrable_finsetSum _ fun j _ => (hVint s).indicator (hD j))
          (hVint s) hsum_le
    _ = M ^ s := hVs
/-! ## Gamma integrals -/

theorem lcbb_lintegral_Ioi_rpow_exp {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    ∫⁻ y in Set.Ioi 0, ENNReal.ofReal (c * (y ^ (a - 1) * Real.exp (-(r * y)))) =
      ENNReal.ofReal (c * ((1 / r) ^ a * Real.Gamma a)) := by
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have hint : IntegrableOn (fun y : ℝ => y ^ (a - 1) * Real.exp (-(r * y))) (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hval]; have := Real.Gamma_pos_of_pos ha; positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c)]
  · rw [integral_const_mul, hval]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg hc (mul_nonneg (Real.rpow_nonneg (le_of_lt hy) _) (Real.exp_pos _).le)

/-- Integrals against `Gamma(n, 1)` reduce to integrals over `(0, ∞)` against the density. -/
theorem lcbb_gamma_lintegral_eq (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫⁻ y, ENNReal.ofReal (f y) ∂(gammaMeasure n 1) =
      ∫⁻ y in Set.Ioi 0, ENNReal.ofReal
        (1 / Real.Gamma n * (y ^ ((n : ℝ) - 1) * Real.exp (-(1 * y))) * f y) := by
  have hm : Measurable (gammaPDF (n : ℝ) 1) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hm hf.ennreal_ofReal,
    ← lintegral_add_compl _ measurableSet_Ici, Set.compl_Ici]
  have h1 : ∫⁻ y in Set.Iio 0, (gammaPDF (n : ℝ) 1 * fun y => ENNReal.ofReal (f y)) y = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun y (hy : y < 0) => by simp [gammaPDF_of_neg hy]), lintegral_zero]
  rw [h1, add_zero, ← setLIntegral_congr Ioi_ae_eq_Ici]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  rw [Pi.mul_apply, gammaPDF_of_nonneg hy.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.one_rpow]
  ring

theorem lcbb_gamma_mgf (n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : u < 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (u * y)) ∂(gammaMeasure n 1) =
      ENNReal.ofReal ((1 - u)⁻¹ ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lcbb_gamma_lintegral_eq n (fun y => Real.exp (u * y)) (measurable_id.const_mul u).exp,
    setLIntegral_congr_fun measurableSet_Ioi (g := fun y => ENNReal.ofReal
      (1 / Real.Gamma n * (y ^ ((n : ℝ) - 1) * Real.exp (-((1 - u) * y))))) (fun y _ => by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]
        congr 5
        ring),
    lcbb_lintegral_Ioi_rpow_exp hn' (by linarith) (by positivity)]
  congr 1
  have hG : Real.Gamma n ≠ 0 := (Real.Gamma_pos_of_pos hn').ne'
  rw [Real.rpow_natCast, ← one_div, div_pow, one_pow]
  field_simp

theorem lcbb_gamma_mean (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ y, ENNReal.ofReal y ∂(gammaMeasure n 1) = n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lcbb_gamma_lintegral_eq n (fun y => y) measurable_id,
    setLIntegral_congr_fun measurableSet_Ioi (g := fun y => ENNReal.ofReal
      (1 / Real.Gamma n * (y ^ (((n : ℝ) + 1) - 1) * Real.exp (-(1 * y))))) (fun y hy => by
        have hy' : y ≠ 0 := ne_of_gt hy
        rw [add_sub_cancel_right, Real.rpow_sub_one hy']
        congr 1
        field_simp),
    lcbb_lintegral_Ioi_rpow_exp (by linarith) one_pos (by positivity),
    Real.Gamma_add_one hn'.ne']
  have hG : Real.Gamma n ≠ 0 := (Real.Gamma_pos_of_pos hn').ne'
  rw [div_one, Real.one_rpow, one_mul, one_div, ← mul_assoc, inv_mul_eq_div,
    div_mul_cancel₀ _ hG]
  exact ENNReal.ofReal_natCast n

theorem lcbb_gamma_Iio_zero (a : ℝ) : gammaMeasure a 1 (Set.Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl
/-! ## Gamma-kernel transfer -/

theorem lcbb_lintegral_partition (N : Ω → ℕ) (hN : Measurable N) (F : Ω → ENNReal) :
    ∫⁻ ω, F ω ∂P = ∑' n, ∫⁻ ω in {ω | N ω = n}, F ω ∂P := by
  have hU : (⋃ n, {ω | N ω = n}) = Set.univ := by
    ext ω; simp
  rw [← lintegral_iUnion (s := fun n => {ω | N ω = n})
    (fun n => (hN (measurableSet_singleton n) : MeasurableSet {ω | N ω = n}))
    (fun i j hij => Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj)) F, hU,
    Measure.restrict_univ]

theorem lcbb_setLIntegral_fst (hZ0 : Measurable (Z 0))
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) :
    ∫⁻ ω in {ω | (Z 0 ω).2 = n}, f (Z 0 ω).1 ∂P =
      P {ω | (Z 0 ω).2 = n} * ∫⁻ y, f y ∂(gammaMeasure n 1) := by
  have hg : Measurable fun ω => (Z 0 ω).1 := hZ0.fst
  have hmap : Measure.map (fun ω => (Z 0 ω).1) (P.restrict {ω | (Z 0 ω).2 = n}) =
      P {ω | (Z 0 ω).2 = n} • gammaMeasure n 1 := by
    ext A hA
    rw [Measure.map_apply hg hA, Measure.restrict_apply (hg hA), Measure.smul_apply, smul_eq_mul,
      ← hgam n A hA]
    rfl
  rw [← lintegral_map hf hg, hmap, lintegral_smul_measure, smul_eq_mul]

theorem lcbb_setLIntegral_snd (hZ0 : Measurable (Z 0)) (F : ℕ → ENNReal) (n : ℕ) :
    ∫⁻ ω in {ω | (Z 0 ω).2 = n}, F (Z 0 ω).2 ∂P = P {ω | (Z 0 ω).2 = n} * F n := by
  have hS : MeasurableSet {ω | (Z 0 ω).2 = n} := hZ0.snd (measurableSet_singleton n)
  rw [setLIntegral_congr_fun hS (g := fun _ => F n)
    (fun ω (hω : (Z 0 ω).2 = n) => by rw [hω]), setLIntegral_const, mul_comm]

theorem lcbb_count_zero_null (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) : P {ω | (Z 0 ω).2 = 0} = 0 :=
  measure_mono_null (fun ω (hω : (Z 0 ω).2 = 0) => by
    show ¬ 1 ≤ (Z 0 ω).2
    omega) (ae_iff.1 hpos)

theorem lcbb_fst_nonneg
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A) :
    ∀ᵐ ω ∂P, 0 ≤ (Z 0 ω).1 := by
  have : {ω | ¬ 0 ≤ (Z 0 ω).1} = ⋃ n : ℕ, {ω | (Z 0 ω).1 ∈ Set.Iio 0 ∧ (Z 0 ω).2 = n} := by
    ext ω; simp
  rw [ae_iff, this]
  exact measure_iUnion_null fun n => by
    rw [hgam n _ measurableSet_Iio, lcbb_gamma_Iio_zero, mul_zero]

theorem lcbb_lintegral_fst_eq_snd (hZ0 : Measurable (Z 0)) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2)
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A) :
    ∫⁻ ω, ENNReal.ofReal (Z 0 ω).1 ∂P = ∫⁻ ω, ENNReal.ofReal ((Z 0 ω).2 : ℝ) ∂P := by
  rw [lcbb_lintegral_partition _ hZ0.snd, lcbb_lintegral_partition _ hZ0.snd]
  refine tsum_congr fun n => ?_
  rw [lcbb_setLIntegral_fst hZ0 hgam ENNReal.measurable_ofReal n,
    lcbb_setLIntegral_snd hZ0 (fun k => ENNReal.ofReal (k : ℝ)) n]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · rw [h0, lcbb_count_zero_null hpos, zero_mul, zero_mul]
  · rw [lcbb_gamma_mean n hn, ENNReal.ofReal_natCast]

theorem lcbb_lintegral_exp_fst_le (hZ0 : Measurable (Z 0)) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2)
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A)
    {u c : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (hc : 2 * u ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (u * (Z 0 ω).1)) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * (Z 0 ω).2)) ∂P := by
  rw [lcbb_lintegral_partition _ hZ0.snd, lcbb_lintegral_partition _ hZ0.snd]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [lcbb_setLIntegral_fst hZ0 hgam (f := fun y => ENNReal.ofReal (Real.exp (u * y)))
      (measurable_id.const_mul u).exp.ennreal_ofReal n,
    lcbb_setLIntegral_snd hZ0 (fun k => ENNReal.ofReal (Real.exp (c * k))) n]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · rw [h0, lcbb_count_zero_null hpos, zero_mul, zero_mul]
  · rw [lcbb_gamma_mgf n hn (by linarith)]
    gcongr
    have hinv : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
    calc (1 - u)⁻¹ ^ n ≤ Real.exp (u + u ^ 2) ^ n :=
          pow_le_pow_left₀ hinv (inv_one_sub_le_exp hu0 hu) n
      _ = Real.exp (n * (u + u ^ 2)) := (Real.exp_nat_mul _ n).symm
      _ ≤ Real.exp (c * n) := by
          apply Real.exp_le_exp.2
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have : u ^ 2 ≤ u := by nlinarith
          nlinarith

/-! ## Moments of the normalized centred gap -/

/-- Consequences of the Gamma kernel, `E N = m₀` and `E e^{θ N/m₀} ≤ B` for the centred gap
`X = g/m₀ - 1`: `E X = 0` and `E e^{η₀ |X|} ≤ e^{η₀} B` with `η₀ = bernsteinEta θ`. -/
theorem lcbb_centred_moments [IsProbabilityMeasure P] (h : IIDPairs P Z) {m₀ θ B : ℝ}
    (hθ : 0 < θ) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2)
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A)
    (hm₀ : 0 < m₀) (hmean : ∫ ω, ((Z 0 ω).2 : ℝ) ∂P = m₀)
    (hexpint : Integrable (fun ω => Real.exp (θ * (Z 0 ω).2 / m₀)) P)
    (hexp : ∫ ω, Real.exp (θ * (Z 0 ω).2 / m₀) ∂P ≤ B) :
    Integrable (fun ω => (Z 0 ω).1 / m₀ - 1) P ∧ ∫ ω, ((Z 0 ω).1 / m₀ - 1) ∂P = 0 ∧
      Integrable (fun ω => Real.exp (bernsteinEta θ * |(Z 0 ω).1 / m₀ - 1|)) P ∧
      ∫ ω, Real.exp (bernsteinEta θ * |(Z 0 ω).1 / m₀ - 1|) ∂P ≤
        Real.exp (bernsteinEta θ) * B := by
  have hZ0 := h.measurable 0
  have hgm : Measurable fun ω => (Z 0 ω).1 := hZ0.fst
  have hNint : Integrable (fun ω => ((Z 0 ω).2 : ℝ)) P :=
    Integrable.of_integral_ne_zero (by rw [hmean]; exact hm₀.ne')
  have hN0 : 0 ≤ᵐ[P] fun ω => ((Z 0 ω).2 : ℝ) := ae_of_all _ fun ω => Nat.cast_nonneg _
  have hg0 : 0 ≤ᵐ[P] fun ω => (Z 0 ω).1 := lcbb_fst_nonneg hgam
  -- the gap has mean `m₀`
  have hlin : ∫⁻ ω, ENNReal.ofReal (Z 0 ω).1 ∂P = ENNReal.ofReal m₀ := by
    rw [lcbb_lintegral_fst_eq_snd hZ0 hpos hgam, ← hmean,
      ofReal_integral_eq_lintegral_ofReal hNint hN0]
  have hgint : Integrable (fun ω => (Z 0 ω).1) P :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable hg0).1
      (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  have hgmean : ∫ ω, (Z 0 ω).1 ∂P = m₀ := by
    rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm.aestronglyMeasurable, hlin,
      ENNReal.toReal_ofReal hm₀.le]
  have hXint : Integrable (fun ω => (Z 0 ω).1 / m₀ - 1) P :=
    (hgint.div_const m₀).sub (integrable_const 1)
  have hX0 : ∫ ω, ((Z 0 ω).1 / m₀ - 1) ∂P = 0 := by
    rw [integral_sub (hgint.div_const m₀) (integrable_const 1), integral_div, hgmean,
      div_self hm₀.ne']
    simp
  -- `m₀ ≥ 1`
  have hm1 : 1 ≤ m₀ := by
    rw [← hmean]
    have := integral_mono_ae (integrable_const (1 : ℝ)) hNint
      (hpos.mono fun ω hω => by show (1 : ℝ) ≤ ((Z 0 ω).2 : ℝ); exact_mod_cast hω)
    simpa using this
  -- exponential moment of the normalized gap
  set η := bernsteinEta θ with hη
  have hη0 : 0 < η := lcbb_eta_pos hθ
  have hη4 : η ≤ 1 / 4 := lcbb_eta_le_quarter θ
  have h2η : 2 * η ≤ θ := lcbb_two_eta_le θ
  set u := η / m₀ with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [hu, div_le_iff₀ hm₀]; nlinarith
  have hc : 2 * u ≤ θ / m₀ := by
    rw [hu, ← mul_div_assoc]; exact div_le_div_of_nonneg_right h2η hm₀.le
  have hexpY : ∀ ω, Real.exp (u * (Z 0 ω).1) = Real.exp (η * ((Z 0 ω).1 / m₀)) := fun ω => by
    rw [hu]; congr 1; field_simp
  have hexpN : ∀ ω, Real.exp (θ / m₀ * ((Z 0 ω).2 : ℝ)) = Real.exp (θ * (Z 0 ω).2 / m₀) :=
    fun ω => by congr 1; field_simp
  have hle := lcbb_lintegral_exp_fst_le hZ0 hpos hgam hu0 hu2 hc
  simp_rw [hexpY, hexpN] at hle
  rw [← ofReal_integral_eq_lintegral_ofReal hexpint
    (ae_of_all _ fun ω => (Real.exp_pos _).le)] at hle
  have hYm : Measurable fun ω => Real.exp (η * ((Z 0 ω).1 / m₀)) :=
    ((hgm.div_const m₀).const_mul η).exp
  have hYint : Integrable (fun ω => Real.exp (η * ((Z 0 ω).1 / m₀))) P :=
    (lintegral_ofReal_ne_top_iff_integrable hYm.aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  have hYle : ∫ ω, Real.exp (η * ((Z 0 ω).1 / m₀)) ∂P ≤ B := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
      hYm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal ((integral_nonneg fun ω => (Real.exp_pos _).le).trans
      hexp) (hle.trans (ENNReal.ofReal_le_ofReal hexp))
  -- domination of `e^{η |X|}`
  have hdom : ∀ᵐ ω ∂P, ‖Real.exp (η * |(Z 0 ω).1 / m₀ - 1|)‖ ≤
      Real.exp η * Real.exp (η * ((Z 0 ω).1 / m₀)) := by
    filter_upwards [hg0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hY : 0 ≤ (Z 0 ω).1 / m₀ := div_nonneg hω hm₀.le
    have : |(Z 0 ω).1 / m₀ - 1| ≤ (Z 0 ω).1 / m₀ + 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith
  have hKm : Measurable fun ω => Real.exp (η * |(Z 0 ω).1 / m₀ - 1|) := by
    have h1 : Measurable fun ω => (Z 0 ω).1 / m₀ - 1 := (hgm.div_const m₀).sub_const 1
    exact ((continuous_abs.measurable.comp h1).const_mul η).exp
  have hKint : Integrable (fun ω => Real.exp (η * |(Z 0 ω).1 / m₀ - 1|)) P :=
    (hYint.const_mul (Real.exp η)).mono' hKm.aestronglyMeasurable hdom
  refine ⟨hXint, hX0, hKint, ?_⟩
  calc ∫ ω, Real.exp (η * |(Z 0 ω).1 / m₀ - 1|) ∂P
      ≤ ∫ ω, Real.exp η * Real.exp (η * ((Z 0 ω).1 / m₀)) ∂P :=
        integral_mono_ae hKint (hYint.const_mul _)
          (hdom.mono fun ω hω => (le_abs_self _).trans hω)
    _ = Real.exp η * ∫ ω, Real.exp (η * ((Z 0 ω).1 / m₀)) ∂P := integral_const_mul _ _
    _ ≤ Real.exp η * B := by gcongr

/-! ## The maximal Bernstein estimate and the early stop -/

/-- One-sided maximal bound: if `E φ(Z 0) = 0` and `E e^{η |φ(Z 0)|} ≤ K`, then for
`0 ≤ λ ≤ η/2`, `P(∃ j ≤ s, x ≤ ∑_{i<j} φ(Z i)) ≤ exp((8/η²) K λ² s - λ x)`. -/
theorem lcbb_one_sided [IsProbabilityMeasure P] (h : IIDPairs P Z) {φ : ℝ × ℕ → ℝ}
    (hφ : Measurable φ) (hXi : Integrable (fun ω => φ (Z 0 ω)) P)
    (hX0 : ∫ ω, φ (Z 0 ω) ∂P = 0) {η K : ℝ} (hη : 0 < η)
    (hK : Integrable (fun ω => Real.exp (η * |φ (Z 0 ω)|)) P)
    (hKle : ∫ ω, Real.exp (η * |φ (Z 0 ω)|) ∂P ≤ K) {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ η / 2)
    (s : ℕ) (x : ℝ) :
    P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} ≤
      Real.exp (8 / η ^ 2 * K * l ^ 2 * s - l * x) := by
  obtain ⟨hint, h1, hup⟩ := lcbb_mgf_quad (X := fun ω => φ (Z 0 ω)) (hφ.comp (h.measurable 0))
    hXi hX0 hη hK hKle (l := l) (by rwa [abs_of_nonneg hl0])
  have hmax := lcbb_maximal_exp h hφ hl0 hint h1 s x
  have hM0 : 0 ≤ ∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P := le_trans zero_le_one h1
  have hpow : (∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P) ^ s ≤ Real.exp (8 / η ^ 2 * K * l ^ 2 * s) := by
    calc (∫ ω, Real.exp (l * φ (Z 0 ω)) ∂P) ^ s ≤ Real.exp (l ^ 2 * (8 / η ^ 2 * K)) ^ s := by
          refine pow_le_pow_left₀ hM0 (hup.trans ?_) s
          have := Real.add_one_le_exp (l ^ 2 * (8 / η ^ 2 * K))
          linarith
      _ = Real.exp (8 / η ^ 2 * K * l ^ 2 * s) := by
          rw [← Real.exp_nat_mul]; ring_nf
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  exact hmax.trans hpow

/-- **Uniform maximal Bernstein estimate** (klc:lem:maximal-bernstein).  For an iid pair
sequence with positive integer counts `N`, Gamma kernel `L(g | N = n) = Gamma(n, 1)`,
`E N = m₀` and `E e^{θ N/m₀} ≤ B`, for all `s ≥ 1` and `x > 0`,
`P(max_{j ≤ s} |∑_{i<j} (gᵢ/m₀ - 1)| > x) ≤ 2 exp(-c min(x²/s, x))` with
`c = bernsteinRate θ B`, which depends only on `θ` and `B`. -/
theorem maximal_bernstein [IsProbabilityMeasure P] (h : IIDPairs P Z) {m₀ θ B : ℝ}
    (hθ : 0 < θ) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2)
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A)
    (hm₀ : 0 < m₀) (hmean : ∫ ω, ((Z 0 ω).2 : ℝ) ∂P = m₀)
    (hexpint : Integrable (fun ω => Real.exp (θ * (Z 0 ω).2 / m₀)) P)
    (hexp : ∫ ω, Real.exp (θ * (Z 0 ω).2 / m₀) ∂P ≤ B)
    (s : ℕ) (hs : 1 ≤ s) {x : ℝ} (hx : 0 < x) :
    P.real {ω | ∃ j ≤ s, x < |gapWalk m₀ Z j ω|} ≤
      2 * Real.exp (-(bernsteinRate θ B * min (x ^ 2 / s) x)) := by
  obtain ⟨hXi, hX0, hKi, hKle⟩ :=
    lcbb_centred_moments h hθ hpos hgam hm₀ hmean hexpint hexp
  have hη := lcbb_eta_pos hθ
  have hB : 0 < B := (integral_exp_pos hexpint).trans_le hexp
  have hC₀ : 0 < bernsteinC0 θ B := lcbb_C0_pos hθ hB
  have hc0 : 0 < bernsteinRate θ B := bernsteinRate_pos hθ hB
  have hC₀eq : 8 / bernsteinEta θ ^ 2 * (Real.exp (bernsteinEta θ) * B) = bernsteinC0 θ B := by
    unfold bernsteinC0; ring
  set η := bernsteinEta θ with hηdef
  set C₀ := bernsteinC0 θ B with hC₀def
  set c := bernsteinRate θ B with hcdef
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set l := min (η / 2) (x / (2 * C₀ * s)) with hldef
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hlη : l ≤ η / 2 := min_le_left _ _
  have hlx : l ≤ x / (2 * C₀ * s) := min_le_right _ _
  -- the exponent
  have hexpo : C₀ * l ^ 2 * s - l * x ≤ -(c * min (x ^ 2 / s) x) := by
    have h1 : C₀ * l * s ≤ x / 2 := by
      have := mul_le_mul_of_nonneg_left hlx (by positivity : 0 ≤ C₀ * s)
      calc C₀ * l * s = C₀ * s * l := by ring
        _ ≤ C₀ * s * (x / (2 * C₀ * s)) := this
        _ = x / 2 := by field_simp
    have h2 : C₀ * l ^ 2 * s - l * x ≤ -(l * x / 2) := by nlinarith
    have h3 : c * min (x ^ 2 / s) x ≤ l * x / 2 := by
      rcases min_cases (η / 2) (x / (2 * C₀ * s)) with ⟨hl, _⟩ | ⟨hl, _⟩
      · rw [hldef, hl]
        calc c * min (x ^ 2 / s) x ≤ c * x := mul_le_mul_of_nonneg_left (min_le_right _ _) hc0.le
          _ ≤ η / 4 * x := mul_le_mul_of_nonneg_right (min_le_right _ _) hx.le
          _ = η / 2 * x / 2 := by ring
      · rw [hldef, hl]
        calc c * min (x ^ 2 / s) x ≤ c * (x ^ 2 / s) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le
          _ ≤ 1 / (4 * C₀) * (x ^ 2 / s) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
          _ = x / (2 * C₀ * s) * x / 2 := by field_simp; ring
    linarith
  -- the two one-sided bounds
  have hφm : Measurable fun z : ℝ × ℕ => z.1 / m₀ - 1 :=
    (measurable_fst.div_const m₀).sub_const 1
  have hup := lcbb_one_sided h hφm hXi hX0 hη hKi hKle hl0 hlη s x
  have hψm : Measurable fun z : ℝ × ℕ => -(z.1 / m₀ - 1) := hφm.neg
  have hdn := lcbb_one_sided (φ := fun z : ℝ × ℕ => -(z.1 / m₀ - 1)) h hψm hXi.neg
    (by rw [integral_neg, hX0, neg_zero]) hη
    (by simpa only [abs_neg] using hKi) (by simpa only [abs_neg] using hKle) hl0 hlη s x
  rw [hC₀eq] at hup hdn
  have hsub : {ω | ∃ j ≤ s, x < |gapWalk m₀ Z j ω|} ⊆
      {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, ((Z i ω).1 / m₀ - 1)} ∪
        {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -((Z i ω).1 / m₀ - 1)} := by
    rintro ω ⟨j, hj, hjx⟩
    rcases lt_abs.1 hjx with h1 | h1
    · exact Or.inl ⟨j, hj, h1.le⟩
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [Finset.sum_neg_distrib]
      exact h1.le
  have hE := Real.exp_le_exp.2 hexpo
  calc P.real {ω | ∃ j ≤ s, x < |gapWalk m₀ Z j ω|}
      ≤ P.real ({ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, ((Z i ω).1 / m₀ - 1)} ∪
          {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -((Z i ω).1 / m₀ - 1)}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, ((Z i ω).1 / m₀ - 1)} +
          P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -((Z i ω).1 / m₀ - 1)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (C₀ * l ^ 2 * s - l * x) + Real.exp (C₀ * l ^ 2 * s - l * x) :=
        add_le_add hup hdn
    _ ≤ 2 * Real.exp (-(c * min (x ^ 2 / s) x)) := by linarith

omit [MeasurableSpace Ω] in
/-- On the event `max_{j ≤ s} |W_j| ≤ eps` the first PLA segment has more than `s` keys: the line
of slope `1/m₀` through the origin has residuals `-W_j`. -/
theorem lcbb_lt_pairSegLen {m₀ eps : ℝ} {ω : Ω} {s : ℕ}
    (hW : ∀ j ≤ s, |gapWalk m₀ Z j ω| ≤ eps) : (s : ℕ∞) < pairSegLen eps (seq Z ω) := by
  unfold pairSegLen
  rw [lt_segLen_iff]
  refine ⟨1 / m₀, 0, fun i hi => ?_⟩
  have e : (i : ℝ) - (1 / m₀ * pairKeys (seq Z ω) i + 0) = -gapWalk m₀ Z i ω := by
    simp only [pairKeys, seq, gapWalk, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, ← Finset.sum_div]
    ring
  rw [e, abs_neg]
  exact hW i (by omega)

/-- **Early stop** (klc:eq:early-stop), probability part: for the PLA stop
`T = pairSegLen eps`, `P(T ≤ s) ≤ 2 exp(-c min(eps²/s, eps))`, `c = bernsteinRate θ B`. -/
theorem pairSegLen_le_prob [IsProbabilityMeasure P] (h : IIDPairs P Z) {m₀ θ B : ℝ}
    (hθ : 0 < θ) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2)
    (hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A)
    (hm₀ : 0 < m₀) (hmean : ∫ ω, ((Z 0 ω).2 : ℝ) ∂P = m₀)
    (hexpint : Integrable (fun ω => Real.exp (θ * (Z 0 ω).2 / m₀)) P)
    (hexp : ∫ ω, Real.exp (θ * (Z 0 ω).2 / m₀) ∂P ≤ B)
    {eps : ℝ} (heps : 0 < eps) (s : ℕ) (hs : 1 ≤ s) :
    P.real {ω | pairSegLen eps (seq Z ω) ≤ s} ≤
      2 * Real.exp (-(bernsteinRate θ B * min (eps ^ 2 / s) eps)) := by
  refine (measureReal_mono ?_).trans
    (maximal_bernstein h hθ hpos hgam hm₀ hmean hexpint hexp s hs heps)
  intro ω hω
  by_contra hne
  have hW : ∀ j ≤ s, |gapWalk m₀ Z j ω| ≤ eps := fun j hj =>
    not_lt.1 fun hlt => hne ⟨j, hj, hlt⟩
  exact absurd hω (not_le.2 (lcbb_lt_pairSegLen hW))

end PGM
