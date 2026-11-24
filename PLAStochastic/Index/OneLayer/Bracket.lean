import PLAStochastic.Index.OneLayer.UpperTail
import PLAStochastic.Index.OneLayer.LowerTail
import PLAStochastic.ForMathlib.Probability.StoppedSum.GeometricTailMoments

/-!
# Class-uniform bracket for one layer

For iid gaps `hX : GapLaw P X μ σ κ` and `eps > 0` write `G = μ² eps² / σ²` (that is `eps² / v`
with `v = σ² / μ²`), `T = layerSegLen eps X` and `Tn = T.toNat`.  Under the large-`eps`
conditions

`10000 ≤ G`,  `κ² ≤ σ⁶ G / 2304`,  `σ² ≤ 1296 eps μ²`,  `σ⁴ ≤ 18 eps² μ⁴`

the first segment satisfies, with absolute constants,

* `T < ⊤` almost surely, `T` is measurable and `Tn^q` is integrable for every `q`;
* `cMinus G ≤ E[Tn] ≤ cPlus G`, `E[Tn²] ≤ K2 G²`, `E[Tn³] ≤ K3 G³`;
* `∑_{t<n} √t √P(t < T) ≤ Kh G √G`;
* `Var[Tn] ≥ deltaVar (cPlus G)²`.

The upper bounds come from the geometric block tail `measureReal_layerSegLen_gt_le` with the
block length `L = 2 (⌊2592 G⌋ + 1) ∈ (5184 G, 5185 G]`, the lower mean from
`layerSegLen_gt_lowerBound` at `n = ⌊G/64⌋`, and the variance from the small-ball bound
`layerSegLen_smallBall` with blocks of length `B = ⌊G/1152⌋ ≥ G/2304`.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset

/-- Upper constant for the mean: `72 · 5185`. -/
def cPlus : ℝ := 373320

/-- Lower constant for the mean. -/
noncomputable def cMinus : ℝ := 1 / 128

/-- Number of small-ball blocks used for the variance lower bound. -/
def kVar : ℕ := 2 * 373320 * 2304

/-- Probability of the upper event in the variance lower bound. -/
noncomputable def deltaVar : ℝ := (1 / 72 : ℝ) ^ kVar

/-- Second-moment constant `2! · 72² · 5185²`. -/
def K2 : ℝ := 2 * 72 ^ 2 * 5185 ^ 2

/-- Third-moment constant `3! · 72³ · 5185³`. -/
def K3 : ℝ := 6 * 72 ^ 3 * 5185 ^ 3

/-- Constant of the weighted tail sum. -/
noncomputable def Kh : ℝ := 1 / (1 - Real.sqrt (71 / 72)) ^ 2 * (5185 * Real.sqrt 5185)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

/-- The first segment length is measurable. -/
theorem measurable_layerSegLen (hX : GapLaw P X μ σ κ) (eps : ℝ) :
    Measurable (layerSegLen eps X) :=
  wald_measurable_of_lt fun t => (gapFiltration X hX.iid.measurable).le t _
    (gapSegLen_lt_measurable hX.iid.measurable eps t)

/-- **Block tail at scale `G`.** Under the large-`eps` conditions there is a block length
`L ∈ [1, 5185 G]` with `P(j L < T) ≤ (71/72)^j`. -/
theorem layerSegLen_tail_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps G : ℝ}
    (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ 5185 * G ∧
      ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < layerSegLen eps X ω} ≤ (71 / 72 : ℝ) ^ j := by
  have hμ := hX.mu_pos
  have hσ := hX.sigma_pos
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hGσ : G * σ ^ 2 = μ ^ 2 * eps ^ 2 := by rw [hGdef]; field_simp
  set h : ℕ := ⌊2592 * G⌋₊ + 1 with hh
  have hfl1 : 2592 * G < (h : ℝ) := by
    rw [hh]; push_cast; exact Nat.lt_floor_add_one _
  have hfl2 : (h : ℝ) ≤ 2592 * G + 1 := by
    rw [hh]; push_cast; linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2592 * G)]
  have hLc : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
  have hL1 : 5184 * G < ((2 * h : ℕ) : ℝ) := by rw [hLc]; linarith
  refine ⟨2 * h, by omega, by rw [hLc]; linarith, ?_⟩
  refine measureReal_layerSegLen_gt_le hX (h := h) (by omega) rfl ?_ ?_ ?_ ?_ heps.le
  · -- `5184 μ² eps² < σ² L`
    have : 5184 * μ ^ 2 * eps ^ 2 = σ ^ 2 * (5184 * G) := by rw [mul_assoc, ← hGσ]; ring
    rw [this]
    exact mul_lt_mul_of_pos_left hL1 hσ2
  · -- `κ² ≤ σ⁶ L`
    calc κ ^ 2 ≤ σ ^ 6 * (G / 2304) := hβ
      _ ≤ σ ^ 6 * ((2 * h : ℕ) : ℝ) := by gcongr; linarith
  · -- `4 eps ≤ L`, from `eps ≤ 1296 G`
    have h1 : eps * (μ ^ 2 * eps) ≤ (1296 * G) * (μ ^ 2 * eps) := by
      have : G * σ ^ 2 ≤ G * (1296 * eps * μ ^ 2) := by gcongr
      nlinarith
    have h2 : eps ≤ 1296 * G := le_of_mul_le_mul_right h1 (by positivity)
    linarith
  · -- `288 σ² ≤ μ² L`, from `288 σ² ≤ 5184 μ² G`
    have h1 : (288 * σ ^ 2) * σ ^ 2 ≤ (5184 * μ ^ 2 * G) * σ ^ 2 := by
      have : (5184 * μ ^ 2 * G) * σ ^ 2 = 5184 * μ ^ 2 * (G * σ ^ 2) := by ring
      rw [this, hGσ]
      nlinarith
    have h2 : 288 * σ ^ 2 ≤ 5184 * μ ^ 2 * G := le_of_mul_le_mul_right h1 hσ2
    have h3 : μ ^ 2 * (5184 * G) ≤ μ ^ 2 * ((2 * h : ℕ) : ℝ) := by gcongr
    linarith

/-- Under the large-`eps` conditions the first segment is almost surely finite. -/
theorem layerSegLen_ae_lt_top_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤ := by
  obtain ⟨L, hL1, -, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  exact ae_lt_top_of_tail (measurable_layerSegLen hX eps) hL1 (by norm_num) (by norm_num) htail

/-- Under the large-`eps` conditions every power of `T.toNat` is integrable. -/
theorem integrable_layerSegLen_pow_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) (q : ℕ) :
    Integrable (fun ω => ((layerSegLen eps X ω).toNat : ℝ) ^ q) P := by
  obtain ⟨L, hL1, -, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  exact integrable_toNat_pow_of_tail (measurable_layerSegLen hX eps) hL1 (by norm_num)
    (by norm_num) htail q

/-- Under the large-`eps` conditions `T.toNat` is integrable. -/
theorem integrable_layerSegLen_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    Integrable (fun ω => ((layerSegLen eps X ω).toNat : ℝ)) P := by
  simpa using integrable_layerSegLen_pow_of_large hX heps hGdef hG hβ hv1 hv2 1

/-- **Upper mean.** `E[T] ≤ cPlus G`. -/
theorem integral_layerSegLen_le_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P ≤ cPlus * G := by
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  calc ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P ≤ L / (1 - 71 / 72) :=
        (integral_toNat_le_of_tail (measurable_layerSegLen hX eps) hL1 (by norm_num)
          (by norm_num) htail).2
    _ = 72 * L := by ring
    _ ≤ cPlus * G := by unfold cPlus; linarith

/-- **Second moment.** `E[T²] ≤ K2 G²`. -/
theorem integral_layerSegLen_sq_le_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 2 ∂P ≤ K2 * G ^ 2 := by
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  calc ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 2 ∂P
      ≤ ((Nat.factorial 2 : ℕ) : ℝ) / (1 - 71 / 72) ^ 2 * (L : ℝ) ^ 2 :=
        integral_toNat_pow_le_of_tail (measurable_layerSegLen hX eps) hL1 (by norm_num)
          (by norm_num) htail 2
    _ = 2 * 72 ^ 2 * (L : ℝ) ^ 2 := by norm_num [Nat.factorial]
    _ ≤ 2 * 72 ^ 2 * (5185 * G) ^ 2 := by gcongr
    _ = K2 * G ^ 2 := by unfold K2; ring

/-- **Third moment.** `E[T³] ≤ K3 G³`. -/
theorem integral_layerSegLen_cube_le_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 3 ∂P ≤ K3 * G ^ 3 := by
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  calc ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 3 ∂P
      ≤ ((Nat.factorial 3 : ℕ) : ℝ) / (1 - 71 / 72) ^ 3 * (L : ℝ) ^ 3 :=
        integral_toNat_pow_le_of_tail (measurable_layerSegLen hX eps) hL1 (by norm_num)
          (by norm_num) htail 3
    _ = 6 * 72 ^ 3 * (L : ℝ) ^ 3 := by norm_num [Nat.factorial]
    _ ≤ 6 * 72 ^ 3 * (5185 * G) ^ 3 := by gcongr
    _ = K3 * G ^ 3 := by unfold K3; ring

/-- **Weighted tail sum.** `∑_{t<n} √t √P(t < T) ≤ Kh G √G` for every `n`. -/
theorem sum_sqrt_tail_layerSegLen_le_of_large [IsProbabilityMeasure P]
    (hX : GapLaw P X μ σ κ) {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2)
    (hG : 10000 ≤ G) (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) (n : ℕ) :
    ∑ t ∈ range n, √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < layerSegLen eps X ω})
      ≤ Kh * (G * √G) := by
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  obtain ⟨hsum, hle⟩ := tsum_sqrt_mul_sqrt_tail_le (P := P) hL1 (r := 71 / 72) (by norm_num)
    (by norm_num) htail
  have hLL : (L : ℝ) * √(L : ℝ) ≤ 5185 * √5185 * (G * √G) := by
    have : 5185 * √5185 * (G * √G) = (5185 * G) * √(5185 * G) := by
      rw [Real.sqrt_mul (by norm_num)]; ring
    rw [this]
    exact mul_le_mul hLG (Real.sqrt_le_sqrt hLG) (Real.sqrt_nonneg _) (by positivity)
  calc ∑ t ∈ range n, √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < layerSegLen eps X ω})
      ≤ ∑' t : ℕ, √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < layerSegLen eps X ω}) :=
        hsum.sum_le_tsum _ fun t _ => by positivity
    _ ≤ 1 / (1 - √(71 / 72)) ^ 2 * (L * √(L : ℝ)) := hle
    _ ≤ 1 / (1 - √(71 / 72)) ^ 2 * (5185 * √5185 * (G * √G)) := by gcongr
    _ = Kh * (G * √G) := by unfold Kh; ring

/-- **Lower mean.** `cMinus G ≤ E[T]`. -/
theorem integral_layerSegLen_ge_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    cMinus * G ≤ ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P := by
  have hσ := hX.sigma_pos
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hGσ : G * σ ^ 2 = μ ^ 2 * eps ^ 2 := by rw [hGdef]; field_simp
  set n : ℕ := ⌊G / 64⌋₊ with hn
  have hn1 : (n : ℝ) ≤ G / 64 := Nat.floor_le (by positivity)
  have hn2 : G / 64 - 1 < (n : ℝ) := Nat.sub_one_lt_floor _
  have hp : (63 / 64 : ℝ) ≤ P.real {ω | (n : ℕ∞) < layerSegLen eps X ω} := by
    refine le_trans ?_ (layerSegLen_gt_lowerBound hX heps n)
    have h1 : (n : ℝ) * σ ^ 2 / (μ * eps) ^ 2 = n / G := by
      rw [mul_pow, ← hGσ]; field_simp
    have h2 : (n : ℝ) / G ≤ 1 / 64 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have := integral_toNat_ge_of_lower_tail (measurable_layerSegLen hX eps)
    (layerSegLen_ae_lt_top_of_large hX heps hGdef hG hβ hv1 hv2)
    (integrable_layerSegLen_of_large hX heps hGdef hG hβ hv1 hv2) n hp
  unfold cMinus
  linarith

/-- **Variance lower bound.** `deltaVar (cPlus G)² ≤ Var[T]`. -/
theorem variance_layerSegLen_ge_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    deltaVar * (cPlus * G) ^ 2 ≤ ∫ ω, (((layerSegLen eps X ω).toNat : ℝ) -
      ∫ ω', ((layerSegLen eps X ω').toNat : ℝ) ∂P) ^ 2 ∂P := by
  have hσ := hX.sigma_pos
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hGσ : G * σ ^ 2 = μ ^ 2 * eps ^ 2 := by rw [hGdef]; field_simp
  have hfin := layerSegLen_ae_lt_top_of_large hX heps hGdef hG hβ hv1 hv2
  have hmean := integral_layerSegLen_le_of_large hX heps hGdef hG hβ hv1 hv2
  set B : ℕ := ⌊G / 1152⌋₊ with hB
  have hB1 : (B : ℝ) ≤ G / 1152 := Nat.floor_le (by positivity)
  have hB2 : G / 1152 - 1 < (B : ℝ) := Nat.sub_one_lt_floor _
  have hBG : G / 2304 ≤ (B : ℝ) := by linarith
  have hBpos : 1 ≤ B := by
    have : (1 : ℝ) ≤ B := by linarith
    exact_mod_cast this
  have hvar : 1152 * B * σ ^ 2 ≤ μ ^ 2 * eps ^ 2 := by
    rw [← hGσ]
    exact mul_le_mul_of_nonneg_right (by linarith) hσ2.le
  have hκ : κ ^ 2 ≤ σ ^ 6 * B := hβ.trans (by gcongr)
  have hsb := layerSegLen_smallBall hX heps hBpos hvar hκ kVar
  set a : ℝ := 2 * (cPlus * G) with ha
  have hKB : a ≤ ((kVar * B : ℕ) : ℝ) := by
    have hk : (kVar : ℝ) = 2 * 373320 * 2304 := by unfold kVar; norm_num
    rw [ha, Nat.cast_mul, hk]
    unfold cPlus
    linarith
  have hevent : P.real {ω | ((kVar * B : ℕ) : ℕ∞) < layerSegLen eps X ω}
      ≤ P.real {ω | a ≤ ((layerSegLen eps X ω).toNat : ℝ)} := by
    have hae : ∀ᵐ ω ∂P, ω ∈ {ω | ((kVar * B : ℕ) : ℕ∞) < layerSegLen eps X ω} →
        ω ∈ {ω | a ≤ ((layerSegLen eps X ω).toNat : ℝ)} := by
      filter_upwards [hfin] with ω hω hs
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hω.ne
      simp only [← hm, ENat.toNat_natCast] at hs ⊢
      have : kVar * B < m := by exact_mod_cast hs
      refine hKB.trans ?_
      exact_mod_cast this.le
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  have hδ : deltaVar ≤ P.real {ω | a ≤ ((layerSegLen eps X ω).toNat : ℝ)} := hsb.trans hevent
  have hCa : ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P ≤ a / 2 := by rw [ha]; linarith
  have := integral_sq_sub_ge_of_upper_event (measurable_layerSegLen hX eps)
    (integrable_layerSegLen_pow_of_large hX heps hGdef hG hβ hv1 hv2 2) hCa hδ
  have ha2 : a / 2 = cPlus * G := by rw [ha]; ring
  rwa [ha2] at this

/-- **One-layer bracket.** Under the large-`eps` conditions, with `G = μ² eps² / σ²`,
`T = layerSegLen eps X` and `Tn = T.toNat`: `T` is measurable and almost surely finite,
`Tn`, `Tn²`, `Tn³` are integrable, `cMinus G ≤ E[Tn] ≤ cPlus G`, `E[Tn²] ≤ K2 G²`,
`E[Tn³] ≤ K3 G³`, `∑_{t<n} √t √P(t < T) ≤ Kh G √G`, and `Var[Tn] ≥ deltaVar (cPlus G)²`. -/
theorem oneLayer_bracket [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps G : ℝ}
    (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) :
    Measurable (layerSegLen eps X) ∧
      (∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) ∧
      Integrable (fun ω => ((layerSegLen eps X ω).toNat : ℝ)) P ∧
      Integrable (fun ω => ((layerSegLen eps X ω).toNat : ℝ) ^ 2) P ∧
      Integrable (fun ω => ((layerSegLen eps X ω).toNat : ℝ) ^ 3) P ∧
      cMinus * G ≤ ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P ∧
      ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ∂P ≤ cPlus * G ∧
      ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 2 ∂P ≤ K2 * G ^ 2 ∧
      ∫ ω, ((layerSegLen eps X ω).toNat : ℝ) ^ 3 ∂P ≤ K3 * G ^ 3 ∧
      (∀ n : ℕ, ∑ t ∈ range n, √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < layerSegLen eps X ω})
        ≤ Kh * (G * √G)) ∧
      deltaVar * (cPlus * G) ^ 2 ≤ ∫ ω, (((layerSegLen eps X ω).toNat : ℝ) -
        ∫ ω', ((layerSegLen eps X ω').toNat : ℝ) ∂P) ^ 2 ∂P :=
  ⟨measurable_layerSegLen hX eps,
    layerSegLen_ae_lt_top_of_large hX heps hGdef hG hβ hv1 hv2,
    integrable_layerSegLen_of_large hX heps hGdef hG hβ hv1 hv2,
    integrable_layerSegLen_pow_of_large hX heps hGdef hG hβ hv1 hv2 2,
    integrable_layerSegLen_pow_of_large hX heps hGdef hG hβ hv1 hv2 3,
    integral_layerSegLen_ge_of_large hX heps hGdef hG hβ hv1 hv2,
    integral_layerSegLen_le_of_large hX heps hGdef hG hβ hv1 hv2,
    integral_layerSegLen_sq_le_of_large hX heps hGdef hG hβ hv1 hv2,
    integral_layerSegLen_cube_le_of_large hX heps hGdef hG hβ hv1 hv2,
    sum_sqrt_tail_layerSegLen_le_of_large hX heps hGdef hG hβ hv1 hv2,
    variance_layerSegLen_ge_of_large hX heps hGdef hG hβ hv1 hv2⟩

end PGM
