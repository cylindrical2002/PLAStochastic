import PLAStochastic.Index.Endpoint.NextLayerMoments
import PLAStochastic.Index.Endpoint.LargeEpsThreshold
import PLAStochastic.Index.Endpoint.ExpectedHeight
import PLAStochastic.Index.Algorithm.HeightAsymptotics

/-!
# Model G, endpoint promotion: the layer induction

`LayerOK P Z b β vmin Kc` says that the pair sequence `Z` of one layer is iid, its gap
component has relative variance in `[vmin, b]` and normalised third moment at most `β`,
and its count component has `E N² ≤ Kc (E N)²`.  `layerOK_step` shows that for
`eps ≥ epsZero b β` the next layer satisfies the same invariant with the same
constants, provided `b, β, Kc` dominate the absolute constants `bAbs, βAbs, KcAbs`
and `vmin ≤ deltaVar / 2`.  It also gives `E N' = E N · C` with
`eps²/(128 b) ≤ C ≤ cPlus eps² / vmin`, the constant-factor compression that drives
the height asymptotics.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## Layer parameters -/

/-- Mean of the layer gaps. -/
def lmean (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := ∫ ω, (Z 0 ω).1 ∂P
/-- Variance of the layer gaps. -/
def lvar (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := ∫ ω, ((Z 0 ω).1 - lmean P Z) ^ 2 ∂P
/-- Standard deviation of the layer gaps. -/
def lsig (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := Real.sqrt (lvar P Z)
/-- Centred absolute third moment of the layer gaps. -/
def lkap (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := ∫ ω, |(Z 0 ω).1 - lmean P Z| ^ 3 ∂P
/-- Mean hyper-segment count. -/
def lcount (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := ∫ ω, ((Z 0 ω).2 : ℝ) ∂P
/-- Second moment of the hyper-segment count. -/
def lcount2 (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := ∫ ω, ((Z 0 ω).2 : ℝ) ^ 2 ∂P

/-- Absolute bound on the relative variance of every layer after the first. -/
def bAbs : ℝ := 2 * K2 * 128 ^ 2
/-- Absolute bound on the normalised third moment of every layer after the first. -/
def βAbs : ℝ := (16 * (128 ^ 3 * K3 + 1) + 2) / (deltaVar / 2) ^ ((3 : ℝ) / 2)
/-- Absolute bound for the normalised count second moment. -/
def KcAbs : ℝ := 4 * K2 * 128 ^ 2

theorem K2_pos : 0 < K2 := by unfold K2; norm_num
theorem K3_pos : 0 < K3 := by unfold K3; norm_num
theorem bAbs_pos : 0 < bAbs := by unfold bAbs; have := K2_pos; positivity
theorem KcAbs_pos : 0 < KcAbs := by unfold KcAbs; have := K2_pos; positivity
theorem cPlus_pos : 0 < cPlus := by unfold cPlus; norm_num

/-- The layer invariant. -/
structure LayerOK (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) (b β vmin Kc : ℝ) : Prop where
  iid : IIDPairs P Z
  law : GapLaw P (fun t ω => (Z t ω).1) (lmean P Z) (lsig P Z) (lkap P Z)
  var_le : lsig P Z ^ 2 ≤ b * lmean P Z ^ 2
  var_ge : vmin * lmean P Z ^ 2 ≤ lsig P Z ^ 2
  third_le : lkap P Z ≤ β * lsig P Z ^ 3
  cnt2 : MemLp (fun ω => ((Z 0 ω).2 : ℝ)) 2 P
  cnt_pos : 0 < lcount P Z
  cnt_sq : lcount2 P Z ≤ Kc * lcount P Z ^ 2

/-! ## Auxiliary facts -/

theorem lvar_nonneg (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : 0 ≤ lvar P Z :=
  integral_nonneg fun _ => sq_nonneg _

theorem lsig_sq (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : lsig P Z ^ 2 = lvar P Z :=
  Real.sq_sqrt (lvar_nonneg P Z)

/-- A layer with an `L³` gap of positive mean and positive variance is a `GapLaw`
    with its own parameters. -/
theorem gapLaw_of_moments {Z : ℕ → Ω → ℝ × ℕ} (hiid : IIDSeq P (fun t ω => (Z t ω).1))
    (h3 : MemLp (fun ω => (Z 0 ω).1) 3 P) (hμ : 0 < lmean P Z) (hv : 0 < lvar P Z) :
    GapLaw P (fun t ω => (Z t ω).1) (lmean P Z) (lsig P Z) (lkap P Z) where
  iid := hiid
  memLp3 := h3
  mean := rfl
  var := (lsig_sq P Z).symm
  third := le_rfl
  mu_pos := hμ
  sigma_pos := Real.sqrt_pos.2 hv

/-- `x^{3/2} = (√x)³`. -/
theorem rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `Var ≤` second moment. -/
theorem integral_sub_mean_sq_le [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂P) ^ 2 ∂P ≤ ∫ ω, f ω ^ 2 ∂P := by
  set c := ∫ ω', f ω' ∂P
  have hf1 : Integrable f P := hf.integrable one_le_two
  have hexp : (fun ω => (f ω - c) ^ 2) = fun ω => f ω ^ 2 + (-(2 * c) * f ω + c ^ 2) := by
    funext ω; ring
  rw [hexp, integral_add (f := fun ω => f ω ^ 2) (g := fun ω => -(2 * c) * f ω + c ^ 2)
    hf.integrable_sq ((hf1.const_mul _).add (integrable_const _)),
    integral_add (f := fun ω => -(2 * c) * f ω) (g := fun _ => c ^ 2) (hf1.const_mul _)
      (integrable_const _), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  nlinarith [sq_nonneg c]

/-! ## One step of the layer induction -/

/-- The next layer of a pair sequence. -/
def nextLayer (eps : ℝ) (Z : ℕ → Ω → ℝ × ℕ) : ℕ → Ω → ℝ × ℕ :=
  fun j ω => layerMap eps (seq Z ω) j

/-- Mean number of layer keys in the first segment. -/
def segMean (P : Measure Ω) (eps : ℝ) (Z : ℕ → Ω → ℝ × ℕ) : ℝ :=
  ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P

omit mΩ in
theorem nextLayer_zero (eps : ℝ) (Z : ℕ → Ω → ℝ × ℕ) (ω : Ω) :
    nextLayer eps Z 0 ω = firstBlock eps (seq Z ω) := rfl

theorem one_le_epsZero (b β : ℝ) : 1 ≤ epsZero b β := by
  unfold epsZero
  have hb := one_le_bOne b
  have t1 : 0 ≤ 10000 * bOne b := by linarith
  have t2 : 0 ≤ 2304 * β ^ 2 * bOne b :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg β)) (by linarith)
  have t3 : 0 ≤ 8192 * bOne b ^ 2 / deltaVar := div_nonneg (by positivity) deltaVar_pos.le
  have t4 : 0 ≤ 12 * 128 ^ 3 * Kh * bOne b ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) Kh_nonneg) (pow_nonneg (by linarith) 6)
  have t5 : 0 ≤ 4 * 128 ^ 2 * |β| * bOne b ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg β)) (pow_nonneg (by linarith) 7)
  linarith

theorem layerOK_step [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ} {b β vmin Kc eps : ℝ}
    (hL : LayerOK P Z b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β) (hvmin0 : 0 < vmin)
    (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc) (heps : epsZero b β ≤ eps) :
    (∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) ∧
      LayerOK P (nextLayer eps Z) b β vmin Kc ∧
      lcount P (nextLayer eps Z) = lcount P Z * segMean P eps Z ∧
      eps ^ 2 / (128 * b) ≤ segMean P eps Z ∧
      segMean P eps Z ≤ cPlus * eps ^ 2 / vmin := by
  set μ := lmean P Z with hμdef
  set σ := lsig P Z with hσdef
  set κ := lkap P Z with hκdef
  have hX := hL.law
  have hμ : 0 < μ := hX.mu_pos
  have hσ : 0 < σ := hX.sigma_pos
  have hκ : 0 ≤ κ := hX.kappa_nonneg
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero b β) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ :=
    largeConditions hμ hσ hκ hL.var_le hL.third_le heps
  set G := μ ^ 2 * eps ^ 2 / σ ^ 2 with hGdef
  have hGpos : 0 < G := by positivity
  obtain ⟨-, hfin, hT1, hT2, hT3, hCm, hCp, hM2, hM3, hBh, hVar⟩ :=
    oneLayer_bracket hX hepspos hGdef c1 c2 c3 c4
  have hLP : ∀ ω, layerSegLen eps (fun t ω => (Z t ω).1) ω = pairSegLen eps (seq Z ω) :=
    fun ω => rfl
  simp only [hLP] at hfin hT1 hT2 hT3 hCm hCp hM2 hM3 hBh hVar
  have hfin' : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤ := hfin.mono fun ω h => h.ne
  set C := segMean P eps Z with hCdef
  have hCdef' : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P := rfl
  have hC1 : G / 128 ≤ C := by
    have := hCm; unfold cMinus at this; rw [hCdef']; linarith
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC1
  -- variance of the segment length
  set VarT := ∫ ω, (((pairSegLen eps (seq Z ω)).toNat : ℝ) - C) ^ 2 ∂P with hVarT
  have hV1 : deltaVar * (cPlus * G) ^ 2 ≤ VarT := hVar
  have hV2 : VarT ≤ K2 * G ^ 2 :=
    (integral_sub_mean_sq_le (memLp_toNat_pairSegLen_two hL.iid hT2)).trans hM2
  -- next-layer mean, variance and third moment
  set Z' := nextLayer eps Z with hZ'
  have hmean' : lmean P Z' = μ * C := integral_nextGap hL.iid hX hfin' hT1 hCdef'
  have hvar' : lvar P Z' = ∫ ω, ((firstBlock eps (seq Z ω)).1 - μ * C) ^ 2 ∂P := by
    unfold lvar; rw [hmean']; rfl
  have hkap' : lkap P Z' = ∫ ω, |(firstBlock eps (seq Z ω)).1 - μ * C| ^ 3 ∂P := by
    unfold lkap; rw [hmean']; rfl
  have hS := abs_integral_nextGap_sub_sq_sub_le hL.iid hX hfin' hT2 hCdef'
  rw [← hvar'] at hS
  obtain ⟨hS2lo, hS2hi⟩ := class_variance_bounds hμ hσ hepspos hGdef deltaVar_pos hC1 hCp hV1
    hV2 hS c5
  have hcube := integral_abs_nextGap_sub_cube_le hL.iid hX hfin' hT3 hCdef' hBh
  rw [← hkap'] at hcube
  have hTC3 := integral_abs_toNat_sub_cube_le (fun ω => pairSegLen eps (seq Z ω)) hT3 hC0
    le_rfl
  have hK3' : lkap P Z' ≤ 4 * μ ^ 3 * (4 * (∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 3 ∂P +
      C ^ 3)) + 4 * (3 * σ ^ 3 * (Kh * (G * Real.sqrt G)) + κ * C) := by
    have hμ3 : 0 ≤ 4 * μ ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hTC3 hμ3
    linarith
  have hthird := class_third_bound hμ hσ hepspos hGdef deltaVar_pos hL.third_le hC1 hM3
    K3_pos.le le_rfl hK3' hS2lo c6 c7
  -- positivity of the next-layer parameters
  have hμ' : 0 < lmean P Z' := by rw [hmean']; positivity
  have hv' : 0 < lvar P Z' :=
    lt_of_lt_of_le (mul_pos (half_pos deltaVar_pos) (pow_pos (mul_pos hμ hCpos) 2)) hS2lo
  have hiid' : IIDPairs P Z' := hL.iid.layerMap eps hfin'
  have h3' : MemLp (fun ω => (Z' 0 ω).1) 3 P := memLp_nextGap hL.iid hX hfin' hT3 hBh
  -- counts
  set m := lcount P Z with hmdef
  set s2 := lcount2 P Z with hs2def
  have hm := hL.cnt_pos
  have hcnt' : lcount P Z' = m * C := integral_nextCount hL.iid hL.cnt2 rfl hfin' hT1 hCdef'
  have hcnt2' : lcount2 P Z' ≤ 2 * s2 * C + 2 * m ^ 2 * (K2 * G ^ 2) :=
    integral_nextCount_sq_le hL.iid hL.cnt2 rfl rfl hfin' hT2 hCdef' hM2
  have hC4 : 4 ≤ C := by linarith
  have hGC : G ≤ 128 * C := by linarith
  have hcc := class_count_bound hm hC4 hGC hGpos.le le_rfl K2_pos.le hcnt2'
    (integral_nonneg fun _ => sq_nonneg _)
  have hs2m : s2 / m ^ 2 ≤ Kc := by rw [div_le_iff₀ (by positivity)]; exact hL.cnt_sq
  refine ⟨hfin', ?_, hcnt', ?_, ?_⟩
  · refine
      { iid := hiid'
        law := gapLaw_of_moments hiid'.fst h3' hμ' hv'
        var_le := ?_
        var_ge := ?_
        third_le := ?_
        cnt2 := memLp_nextCount hL.iid hL.cnt2 hfin' hT2
        cnt_pos := by rw [hcnt']; positivity
        cnt_sq := ?_ }
    · rw [lsig_sq, hmean']
      calc lvar P Z' ≤ 2 * K2 * 128 ^ 2 * (μ * C) ^ 2 := hS2hi
        _ = bAbs * (μ * C) ^ 2 := by unfold bAbs; ring
        _ ≤ b * (μ * C) ^ 2 := by gcongr
    · rw [lsig_sq, hmean']
      calc vmin * (μ * C) ^ 2 ≤ deltaVar / 2 * (μ * C) ^ 2 := by gcongr
        _ ≤ lvar P Z' := hS2lo
    · have hl3 : lvar P Z' ^ ((3 : ℝ) / 2) = lsig P Z' ^ 3 :=
        rpow_three_halves_eq (lvar_nonneg P Z')
      rw [hl3] at hthird
      calc lkap P Z' ≤ βAbs * lsig P Z' ^ 3 := by unfold βAbs; exact hthird
        _ ≤ β * lsig P Z' ^ 3 :=
          mul_le_mul_of_nonneg_right hβ (pow_nonneg (Real.sqrt_nonneg _) 3)
    · rw [hcnt']
      have hle : lcount2 P Z' / (m * C) ^ 2 ≤ Kc := by
        have : 2 * K2 * 128 ^ 2 ≤ Kc / 2 := by unfold KcAbs at hKc; linarith
        linarith
      rwa [div_le_iff₀ (by positivity)] at hle
  · -- lower compression bound
    have hGb : eps ^ 2 / b ≤ G := by
      have hbpos : 0 < b := lt_of_lt_of_le bAbs_pos hb
      rw [hGdef, div_le_div_iff₀ hbpos (by positivity)]
      calc eps ^ 2 * σ ^ 2 ≤ eps ^ 2 * (b * μ ^ 2) :=
            mul_le_mul_of_nonneg_left hL.var_le (sq_nonneg eps)
        _ = μ ^ 2 * eps ^ 2 * b := by ring
    calc eps ^ 2 / (128 * b) = eps ^ 2 / b / 128 := by ring
      _ ≤ G / 128 := by gcongr
      _ ≤ C := hC1
  · -- upper compression bound
    have hGv : G ≤ eps ^ 2 / vmin := by
      rw [hGdef, div_le_div_iff₀ (by positivity) hvmin0]
      calc μ ^ 2 * eps ^ 2 * vmin = eps ^ 2 * (vmin * μ ^ 2) := by ring
        _ ≤ eps ^ 2 * σ ^ 2 := mul_le_mul_of_nonneg_left hL.var_ge (sq_nonneg eps)
    calc C ≤ cPlus * G := hCp
      _ ≤ cPlus * (eps ^ 2 / vmin) := by gcongr; exact cPlus_pos.le
      _ = cPlus * eps ^ 2 / vmin := by ring

/-! ## The input layer and the induction -/

/-- The input pairs `(g t, 1)`. -/
def inputPairs (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ × ℕ := fun t ω => (g t ω, 1)

/-- Layer `ℓ` of the endpoint hierarchy built on the input pairs. -/
def epLayerSeq (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℕ → Ω → ℝ × ℕ :=
  (nextLayer eps)^[ℓ] (inputPairs g)

omit mΩ in
theorem seq_epLayerSeq (eps : ℝ) (g : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ ℓ, seq (epLayerSeq eps g ℓ) ω = pairLayer eps ℓ (seq (inputPairs g) ω)
  | 0 => rfl
  | ℓ + 1 => by
    rw [pairLayer_succ, ← seq_epLayerSeq eps g ω ℓ]
    simp only [epLayerSeq, Function.iterate_succ_apply']
    rfl

omit mΩ in
theorem epLayerSeq_eq (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    epLayerSeq eps g ℓ = fun j ω => pairLayer eps ℓ (seq (inputPairs g) ω) j := by
  funext j ω
  rw [← seq_epLayerSeq eps g ω ℓ]; rfl

theorem IIDPairs.inputPairs {g : ℕ → Ω → ℝ} (hg : IIDSeq P g) : IIDPairs P (inputPairs g) where
  measurable t := (hg.measurable t).prodMk measurable_const
  indep := hg.indep.comp (fun _ x => (x, (1 : ℕ))) (fun _ => measurable_id.prodMk measurable_const)
  ident t := (hg.ident t).comp (measurable_id.prodMk measurable_const)

/-- The class constants attached to an input law. -/
def bIn (μ₀ σ₀ : ℝ) : ℝ := max (σ₀ ^ 2 / μ₀ ^ 2) bAbs
def βIn (σ₀ κ₀ : ℝ) : ℝ := max (κ₀ / σ₀ ^ 3) βAbs
def vIn (μ₀ σ₀ : ℝ) : ℝ := min (σ₀ ^ 2 / μ₀ ^ 2) (deltaVar / 2)
def KcIn : ℝ := max 1 KcAbs

theorem layerOK_input [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) :
    LayerOK P (inputPairs g) (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) (vIn μ₀ σ₀) KcIn := by
  have hμ0 : lmean P (inputPairs g) = μ₀ := hg.mean
  have hv0 : lvar P (inputPairs g) = σ₀ ^ 2 := by
    unfold lvar; rw [hμ0]; exact hg.var
  have hs0 : lsig P (inputPairs g) = σ₀ := by
    unfold lsig; rw [hv0]; exact Real.sqrt_sq hg.sigma_pos.le
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hiid := IIDPairs.inputPairs (P := P) hg.iid
  refine
    { iid := hiid
      law := gapLaw_of_moments hiid.fst hg.memLp3 (by rw [hμ0]; exact hμ)
        (by rw [hv0]; positivity)
      var_le := ?_
      var_ge := ?_
      third_le := ?_
      cnt2 := ?_
      cnt_pos := ?_
      cnt_sq := ?_ }
  · rw [hs0, hμ0]
    calc σ₀ ^ 2 = σ₀ ^ 2 / μ₀ ^ 2 * μ₀ ^ 2 := by field_simp
      _ ≤ bIn μ₀ σ₀ * μ₀ ^ 2 := by gcongr; exact le_max_left _ _
  · rw [hs0, hμ0]
    calc vIn μ₀ σ₀ * μ₀ ^ 2 ≤ σ₀ ^ 2 / μ₀ ^ 2 * μ₀ ^ 2 := by gcongr; exact min_le_left _ _
      _ = σ₀ ^ 2 := by field_simp
  · rw [hs0]
    calc lkap P (inputPairs g) = lkap P (inputPairs g) / σ₀ ^ 3 * σ₀ ^ 3 := by field_simp
      _ ≤ βIn σ₀ (lkap P (inputPairs g)) * σ₀ ^ 3 := by gcongr; exact le_max_left _ _
  · simp only [inputPairs, Nat.cast_one]; exact memLp_const 1
  · simp [lcount, inputPairs]
  · simp only [lcount2, lcount, inputPairs, Nat.cast_one, one_pow, integral_const,
      probReal_univ, smul_eq_mul, mul_one]
    exact le_max_left _ _

theorem bAbs_le_bIn (μ₀ σ₀ : ℝ) : bAbs ≤ bIn μ₀ σ₀ := le_max_right _ _
theorem βAbs_le_βIn (σ₀ κ₀ : ℝ) : βAbs ≤ βIn σ₀ κ₀ := le_max_right _ _
theorem vIn_le (μ₀ σ₀ : ℝ) : vIn μ₀ σ₀ ≤ deltaVar / 2 := min_le_right _ _
theorem KcAbs_le_KcIn : KcAbs ≤ KcIn := le_max_right _ _
theorem one_le_KcIn : 1 ≤ KcIn := le_max_left _ _
theorem vIn_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < vIn μ₀ σ₀ :=
  lt_min (by positivity) (half_pos deltaVar_pos)

/-- **Layer induction.** For `eps ≥ epsZero`, every layer satisfies the invariant, every
    first segment is almost surely finite, and the mean hyper-segment count grows by a
    factor in `[eps²/(128 b), cPlus eps²/vmin]` per layer. -/
theorem layerOK_all [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}
    (h0 : LayerOK P (inputPairs g) b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc)
    (heps : epsZero b β ≤ eps) :
    ∀ ℓ, LayerOK P (epLayerSeq eps g ℓ) b β vmin Kc ∧
      (∀ᵐ ω ∂P, pairSegLen eps (seq (epLayerSeq eps g ℓ) ω) ≠ ⊤) ∧
      lcount P (epLayerSeq eps g (ℓ + 1)) =
        lcount P (epLayerSeq eps g ℓ) * segMean P eps (epLayerSeq eps g ℓ) ∧
      eps ^ 2 / (128 * b) ≤ segMean P eps (epLayerSeq eps g ℓ) ∧
      segMean P eps (epLayerSeq eps g ℓ) ≤ cPlus * eps ^ 2 / vmin := by
  have key : ∀ ℓ, LayerOK P (epLayerSeq eps g ℓ) b β vmin Kc := by
    intro ℓ
    induction ℓ with
    | zero => exact h0
    | succ ℓ ih =>
      have := (layerOK_step ih hb hβ hvmin0 hvmin hKc heps).2.1
      simpa only [epLayerSeq, Function.iterate_succ_apply'] using this
  intro ℓ
  obtain ⟨hf, -, hc, hlo, hhi⟩ := layerOK_step (key ℓ) hb hβ hvmin0 hvmin hKc heps
  refine ⟨key ℓ, hf, ?_, hlo, hhi⟩
  have e : epLayerSeq eps g (ℓ + 1) = nextLayer eps (epLayerSeq eps g ℓ) := by
    simp only [epLayerSeq, Function.iterate_succ_apply']
  rw [e, hc]

/-! ## Expected height for fixed `n` and `eps` -/

/-- The mean hyper-segment counts of the layers. -/
def meanSpan (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  lcount P (epLayerSeq eps g ℓ)

/-- The compression constant of the bracket. -/
def cBr (b vmin : ℝ) : ℝ := max (128 * b) (cPlus / vmin)

omit mΩ in
theorem gapKeys_inputPairs (g : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    gapKeys (seq g ω) t = pairKeys (seq (inputPairs g) ω) t := rfl

omit mΩ in
theorem pairRank_inputPairs (g : ℕ → Ω → ℝ) (ω : Ω) (j : ℕ) :
    pairRank (seq (inputPairs g) ω) j = j := by
  simp [pairRank, seq, inputPairs]

/-- Geometric comparison: `m j ≤ m k · r^{k-j}` when every ratio is at least `1/r`. -/
theorem le_mul_pow_of_ratio {m : ℕ → ℝ} {r : ℝ} (hr : 0 < r) (hpos : ∀ ℓ, 0 < m ℓ)
    (hratio : ∀ ℓ, m ℓ ≤ r * m (ℓ + 1)) : ∀ d j, m j ≤ m (j + d) * r ^ d
  | 0, j => by simp
  | d + 1, j => by
    have ih := le_mul_pow_of_ratio hr hpos hratio d j
    have h1 := hratio (j + d)
    calc m j ≤ m (j + d) * r ^ d := ih
      _ ≤ r * m (j + d + 1) * r ^ d := by gcongr
      _ = m (j + (d + 1)) * r ^ (d + 1) := by rw [← add_assoc]; ring

theorem sum_pow_reflect_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    ∀ L : ℕ, ∑ i ∈ range L, r ^ (L - i) ≤ 1
  | 0 => by simp
  | L + 1 => by
    have ih := sum_pow_reflect_le_one hr0 hr L
    have hrec : ∑ i ∈ range (L + 1), r ^ (L + 1 - i) = r * (∑ i ∈ range L, r ^ (L - i) + 1) := by
      rw [sum_range_succ, mul_add, mul_sum, mul_one, show L + 1 - L = 1 by omega, pow_one]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have : L + 1 - i = (L - i) + 1 := by have := mem_range.1 hi; omega
      rw [this, pow_succ]; ring
    rw [hrec]
    nlinarith

theorem integral_epHeight_bounds [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) (x0 : Ω → ℝ) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hbig : 2 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    (firstPassage (meanSpan P eps g) n : ℝ) - 2 ≤
        ∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P ∧
      ∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P ≤
        firstPassage (meanSpan P eps g) (2 * n) + 4 * KcIn := by
  set b := bIn μ₀ σ₀
  set β := βIn σ₀ (lkap P (inputPairs g))
  set vmin := vIn μ₀ σ₀
  set Kc := KcIn
  set c := cBr b vmin with hcdef
  set m := meanSpan P eps g with hmdef
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hvmin0 : 0 < vmin := vIn_pos hμ hσ
  have hbpos : 0 < b := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _) hvmin0
    (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hepspos : 0 < eps := by linarith
  have hZ := (IIDPairs.inputPairs (P := P) hg.iid).measurable
  -- almost sure finiteness of all layers
  have hfinAll : ∀ᵐ ω ∂P, AllLayersFinite eps (seq (inputPairs g) ω) := by
    refine ae_allLayersFinite (IIDPairs.inputPairs hg.iid) eps fun ℓ => ?_
    have := (hall ℓ).2.1
    simpa only [seq_epLayerSeq] using this
  have hpos0 : ∀ t ω, 1 ≤ (inputPairs g t ω).2 := fun _ _ => le_rfl
  -- the finite height equals the span height almost surely
  have hH : (fun ω => (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ)) =ᵐ[P]
      fun ω => (spanHeight eps (seq (inputPairs g) ω) n : ℝ) := by
    filter_upwards [hfinAll] with ω hω
    simp only [gapKeys_inputPairs]
    rw [epHeight_eq_spanHeight (by linarith) hω (fun t => le_rfl)
      (pairRank_inputPairs g ω) (x0 ω) hn]
  rw [integral_congr_ae hH]
  -- growth of the mean counts
  have hmpos : ∀ ℓ, 0 < m ℓ := fun ℓ => (hall ℓ).1.cnt_pos
  have hc1 : 128 * b ≤ c := le_max_left _ _
  have hc2 : cPlus / vmin ≤ c := le_max_right _ _
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have hratio_lo : ∀ ℓ, eps ^ 2 / c ≤ m (ℓ + 1) / m ℓ := by
    intro ℓ
    rw [show m (ℓ + 1) = m ℓ * segMean P eps (epLayerSeq eps g ℓ) from (hall ℓ).2.2.1,
      mul_div_cancel_left₀ _ (hmpos ℓ).ne']
    calc eps ^ 2 / c ≤ eps ^ 2 / (128 * b) := by gcongr
      _ ≤ _ := (hall ℓ).2.2.2.1
  have hq : 1 < eps ^ 2 / c := by rw [lt_div_iff₀ hcpos]; linarith
  have hex : ∀ x : ℝ, ∃ ℓ, x ≤ m ℓ := fun x =>
    geometric_exists_ge (m := m) (Γ := eps ^ 2) (c := c) hq (by
      show lcount P (epLayerSeq eps g 0) = 1
      simp [lcount, epLayerSeq, inputPairs]) hratio_lo x
  -- upper bound
  have hupper : ∫ ω, (spanHeight eps (seq (inputPairs g) ω) n : ℝ) ∂P ≤
      firstPassage m (2 * n) + 4 * Kc := by
    set ℓp := firstPassage m (2 * n)
    have hhit : 2 * (n : ℝ) ≤ m ℓp := firstPassage_hit (hex _)
    have hℓp : 1 ≤ ℓp := by
      by_contra h0
      have : ℓp = 0 := by omega
      rw [this] at hhit
      have : m 0 = 1 := by simp [hmdef, meanSpan, lcount, epLayerSeq, inputPairs]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hL := (hall ℓp).1
    rw [epLayerSeq_eq] at hL
    have hhit' : 2 * (n : ℝ) ≤ ∫ ω, ((pairLayer eps ℓp (seq (inputPairs g) ω) 0).2 : ℝ) ∂P := by
      have := hhit; simp only [hmdef, meanSpan, lcount, epLayerSeq_eq] at this; exact this
    have hsq := hL.cnt_sq
    simp only [lcount2, lcount] at hsq
    exact integral_spanHeight_le hZ heps1 hfinAll hpos0 hn hℓp hL.iid one_le_KcIn
      hL.cnt2.integrable_sq hhit' hsq
  -- lower bound
  have hlower : (firstPassage m n : ℝ) - 2 ≤
      ∫ ω, (spanHeight eps (seq (inputPairs g) ω) n : ℝ) ∂P := by
    set fp := firstPassage m n
    set L := fp - 2
    have hint : ∀ ℓ, Integrable (fun ω => (leadSpan eps (seq (inputPairs g) ω) ℓ : ℝ)) P := by
      intro ℓ
      have h := (hall ℓ).1.cnt2
      rw [epLayerSeq_eq] at h
      exact h.integrable one_le_two
    have hge := integral_spanHeight_ge hZ heps1 hfinAll hpos0 hn L hint
    have hlead : ∀ ℓ, ∫ ω, (leadSpan eps (seq (inputPairs g) ω) ℓ : ℝ) ∂P = m ℓ := by
      intro ℓ; simp only [hmdef, meanSpan, lcount, epLayerSeq_eq]; rfl
    simp only [hlead] at hge
    -- the Markov sum is at most one
    set r := c / eps ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hr2 : r ≤ 1 / 2 := by
      rw [hr, div_le_iff₀ (by positivity)]; linarith
    have hstep : ∀ ℓ, m ℓ ≤ r * m (ℓ + 1) := by
      intro ℓ
      have h := hratio_lo ℓ
      rw [div_le_div_iff₀ hcpos (hmpos ℓ)] at h
      rw [hr, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hsum : ∑ i ∈ range L, m (i + 1) / n ≤ 1 := by
      rcases Nat.lt_or_ge fp 2 with hfp | hfp
      · have : L = 0 := by omega
        simp [this]
      have hfp1 : m (fp - 1) < n := lt_of_lt_firstPassage (by omega)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      calc ∑ i ∈ range L, m (i + 1) / n ≤ ∑ i ∈ range L, r ^ (L - i) := by
            refine sum_le_sum fun i hi => ?_
            have hi' := mem_range.1 hi
            have hcmp := le_mul_pow_of_ratio (by positivity) hmpos hstep (L - i) (i + 1)
            have heq : i + 1 + (L - i) = fp - 1 := by omega
            rw [heq] at hcmp
            rw [div_le_iff₀ hn0]
            calc m (i + 1) ≤ m (fp - 1) * r ^ (L - i) := hcmp
              _ ≤ n * r ^ (L - i) := by gcongr
              _ = r ^ (L - i) * n := by ring
        _ ≤ 1 := sum_pow_reflect_le_one hr0 hr2 L
    have hL : (fp : ℝ) - 2 ≤ L := by
      have : fp ≤ L + 2 := by omega
      have : (fp : ℝ) ≤ L + 2 := by exact_mod_cast this
      linarith
    linarith
  exact ⟨hlower, hupper⟩

end

end PGM
