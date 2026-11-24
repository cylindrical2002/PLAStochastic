import PLAStochastic.Index.CEPS.StripError.EntranceTop
import PLAStochastic.Index.CEPS.StripError.BridgeFinal

/-!
# WP9, S-6: the pair error

The actual pair `J_t(μ) = e^{tl} H_t² 𝔘` (`cepsActualPair`, `q = t(1+μ)`, `l = 2ε(1+μ)`) and the
complete normal pair (C15) in its regular divided-difference form `cepsNormalRegularPair`
(`e^{tl} Ĥ_t² (-∂_q Û - w Û)`, which is `cepsNormalPair` at nondegenerate points) differ by
`K ε^{33} e^{-c₀ ε/32}` on the marked curve, uniformly over the class (`ceps_pair_error`).

The marked bridge is `𝔘 = -∂_q U - w U` (`cepsMarkedBridge_eq_deriv`, termwise differentiation of
the absolutely convergent discount series), so the error follows from S-3 (a)
(`ceps_strip_entrance_error_top`), S-4 (`ceps_strip_bridge_error`) and the X3/X7 polynomial
bounds of `H_t`, `U` and `∂_q U`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf
open scoped NNReal

/-- The complete normal pair (C15) in the regular divided-difference form, with `𝒟 = -∂_q` taken
before the substitution `q = t(1+μ)`, `l = w(1+μ)`. -/
def cepsNormalRegularPair (A : ℂ → ℂ → CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ t w : ℂ) : ℂ :=
  let q := t * (1 + μ)
  let l := w * (1 + μ)
  exp (t * l) * ((A μ q).regularEntrance L μ q l t) ^ 2 *
    (-deriv (fun q' => (A μ q').regularBridge L μ q' l) q - w * (A μ q).regularBridge L μ q l)

/-- **The marked bridge is the time operator applied to the bridge**: `𝔘 = -∂_q U - w U`. -/
theorem cepsMarkedBridge_eq_deriv {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ}
    (hf : CepsGapDensity ν f D) {l : ℝ} (hl : 2 ≤ l) (w μ : ℝ) {q : ℂ} (hq : 0 ≤ q.re) :
    cepsMarkedBridge ν f w μ q l =
      -deriv (fun z => cepsBridge ν f μ z l) q - (w : ℂ) * cepsBridge ν f μ q l := by
  set b := -(krKappa D vlo vhi / (16 * l ^ 2)) with hbdef
  set c : ℕ → ℂ := fun n => (krDens (Icc 0 l) ν f (1 + μ) 1 (n + 1) 0 l : ℂ) with hcdef
  have he : ∀ n : ℕ, ‖Complex.exp (-(b : ℂ) * (n + 1 : ℕ)) * c n‖ =
      ‖Complex.exp (-(b : ℂ) * ((n : ℂ) + 1))‖ *
        krDens (Icc 0 l) ν f (1 + μ) 1 (n + 1) 0 l := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)]
    simp
  have hM : CepsDiscMoments c 1 b := by
    intro j
    simpa only [he, mul_assoc] using
      (cepsBand_density_moments hD hθ hvlo hvhi hν hf (w := l) (l := l) hl (by linarith)
        (by linarith) (1 + μ) (a := 1) (by norm_num) (q := (b : ℂ))
        (by change b ≤ b; exact le_rfl) j 0 l).1
  have hb : b < q.re := by
    have := krKappa_pos hD hvlo hvhi
    have : 0 < krKappa D vlo vhi / (16 * l ^ 2) := by positivity
    linarith
  have hfun : cepsDiscJet c 1 0 = fun z => cepsBridge ν f μ z l := by
    funext z
    simp [cepsDiscJet, cepsBridge, cepsBridgeDens, c]
  have hd := (cepsDiscJet_hasDerivAt (by omega : 1 ≤ 1) hM hb 0).deriv
  rw [hfun] at hd
  have hU : cepsBridge ν f μ q l = cepsDiscJet c 1 0 q := by rw [hfun]
  rw [hd, hU]
  have hs0 := cepsDiscJet_summable (by omega : 1 ≤ 1) hM hb.le 0
  have hs1 := cepsDiscJet_summable (by omega : 1 ≤ 1) hM hb.le 1
  have hsum : cepsMarkedBridge ν f w μ q l = ∑' n : ℕ,
      (-((-((n + 1 : ℕ) : ℂ)) ^ (0 + 1) * Complex.exp (-q * (n + 1 : ℕ)) * c n) -
        (w : ℂ) * ((-((n + 1 : ℕ) : ℂ)) ^ 0 * Complex.exp (-q * (n + 1 : ℕ)) * c n)) := by
    unfold cepsMarkedBridge
    refine tsum_congr fun n => ?_
    simp only [c, cepsBridgeDens]
    push_cast
    ring
  rw [hsum, Summable.tsum_sub hs1.neg (hs0.mul_left _), tsum_neg, tsum_mul_left]
  rfl

/-- The algebra of the pair error. -/
theorem norm_sq_mul_sub_le {H Hh M Mh : ℂ} {a e u d : ℝ} (hH : ‖H‖ ≤ a) (he : ‖H - Hh‖ ≤ e)
    (hM : ‖M‖ ≤ u) (hd : ‖M - Mh‖ ≤ d) :
    ‖H ^ 2 * M - Hh ^ 2 * Mh‖ ≤ e * (2 * a + e) * u + (a + e) ^ 2 * d := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hH
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have h1 : H ^ 2 * M - Hh ^ 2 * Mh = (H - Hh) * (H + Hh) * M + Hh ^ 2 * (M - Mh) := by ring
  have hHh : ‖Hh‖ ≤ a + e := by
    calc ‖Hh‖ = ‖H - (H - Hh)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖H‖ + ‖H - Hh‖ := norm_sub_le _ _
      _ ≤ a + e := add_le_add hH he
  have hsum : ‖H + Hh‖ ≤ 2 * a + e := (norm_add_le _ _).trans (by linarith)
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul he hsum (norm_nonneg _) he0) hM (norm_nonneg _)
      (by positivity)
  · rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hHh 2) hd (norm_nonneg _) (sq_nonneg _)

/-- The polynomial budget of the pair error. -/
theorem pair_budget_le {X E KE CH CU KU a e u d : ℝ} (hX : 1 ≤ X) (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hKE : 0 ≤ KE) (hCH : 0 ≤ CH) (hCU : 0 ≤ CU) (hKU : 0 ≤ KU) (ha0 : 0 ≤ a) (he0 : 0 ≤ e)
    (hu0 : 0 ≤ u) (hdd : 0 ≤ d) (ha : a ≤ CH * X ^ 3) (he : e ≤ KE * X ^ 7 * E) (hu : u ≤ CU * X ^ 5)
    (hd : d ≤ 2 * KU * X ^ 19 * E) :
    e * (2 * a + e) * u + (a + e) ^ 2 * d ≤
      (KE * (2 * CH + KE) * CU + 2 * (CH + KE) ^ 2 * KU) * X ^ 33 * E := by
  have hX0 : 0 ≤ X := by linarith
  have hp37 : X ^ 3 ≤ X ^ 7 := pow_le_pow_right₀ hX (by norm_num)
  have hp1933 : X ^ 19 ≤ X ^ 33 := pow_le_pow_right₀ hX (by norm_num)
  have ha' : a ≤ CH * X ^ 7 := ha.trans (mul_le_mul_of_nonneg_left hp37 hCH)
  have he' : e ≤ KE * X ^ 7 :=
    he.trans (by
      calc KE * X ^ 7 * E ≤ KE * X ^ 7 * 1 :=
            mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ = _ := mul_one _)
  have h2ae : 2 * a + e ≤ (2 * CH + KE) * X ^ 7 := by nlinarith
  have hae : a + e ≤ (CH + KE) * X ^ 7 := by nlinarith
  have hd0 : 0 ≤ 2 * KU * X ^ 19 * E := by positivity
  have h1 : e * (2 * a + e) * u ≤ KE * (2 * CH + KE) * CU * X ^ 33 * E := by
    calc e * (2 * a + e) * u ≤ (KE * X ^ 7 * E) * ((2 * CH + KE) * X ^ 7) * (CU * X ^ 5) :=
          mul_le_mul (mul_le_mul he h2ae (by positivity) (by positivity)) hu hu0 (by positivity)
      _ = KE * (2 * CH + KE) * CU * X ^ 19 * E := by ring
      _ ≤ KE * (2 * CH + KE) * CU * X ^ 33 * E := by
          have : 0 ≤ KE * (2 * CH + KE) * CU := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1933 this) hE0
  have h2 : (a + e) ^ 2 * d ≤ 2 * (CH + KE) ^ 2 * KU * X ^ 33 * E := by
    calc (a + e) ^ 2 * d ≤ ((CH + KE) * X ^ 7) ^ 2 * (2 * KU * X ^ 19 * E) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hae 2) hd hdd (by positivity)
      _ = 2 * (CH + KE) ^ 2 * KU * X ^ 33 * E := by ring
  linarith

theorem pair_width_bounds {eps μ : ℝ} (heps : 0 ≤ eps) (hμ : |μ| ≤ 1 / 2) :
    eps ≤ 2 * eps * (1 + μ) ∧ 2 * eps * (1 + μ) ≤ 3 * eps := by
  have hμa := abs_le.mp hμ
  constructor <;> nlinarith

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The drift window of S-6. -/
def CepsCanonDomain.stripPairMu (dom : CepsCanonDomain D θ v) (Dg : ℝ) : ℝ :=
  min (min dom.renewalMu (1 / (64 * Dg))) (1 / 2)

/-- The mark window of S-6. -/
def CepsCanonDomain.stripPairMark (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.stripMarkBound (dom.renewalDiscount / 6)

/-- The scale threshold `ε₀` of S-6. -/
def CepsCanonDomain.stripPairWidth (dom : CepsCanonDomain D θ v) : ℝ :=
  max (max dom.stripEntranceWidth 4) 1

include hD in
theorem CepsCanonDomain.stripPairMu_pos {Dg : ℝ} (hDg : 0 < Dg) : 0 < dom.stripPairMu Dg :=
  lt_min (lt_min (dom.renewalMu_pos hD) (by positivity)) (by norm_num)

include hD in
theorem CepsCanonDomain.stripPairMark_pos (hv : 0 ≤ v) : 0 < dom.stripPairMark := by
  have h1 := dom.c₀_pos
  have h2 := dom.renewalDiscount_pos hD
  exact lt_min (lt_min (by positivity) (lt_min (by positivity) (by positivity))) (by positivity)

include hθ hD in
/-- **S-6: the pair error**, class-uniform, on the marked curve `t ∈ iℝ`, `q = t(1+μ)`,
`l = 2ε(1+μ)`. -/
theorem ceps_pair_error {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) (Kf : ℝ≥0) :
    ∃ K : ℝ, ∀ (ν : ProbabilityMeasure ℝ) (f fW : ℝ → ℝ), RegLaw Dg θg vlo vhi ν →
      CepsGapDensity ν f Dg → LipschitzWith Kf f →
      IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v →
      ∀ μ : ℝ, |μ| ≤ dom.stripPairMu Dg → ∀ t : ℂ, t.re = 0 → ‖t‖ ≤ dom.stripPairMark →
      ∀ eps : ℝ, dom.stripPairWidth ≤ eps →
        ‖cepsActualPair ν f eps t μ -
          cepsNormalRegularPair (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x))
            (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ t ((2 * eps : ℝ) : ℂ)‖ ≤
          K * eps ^ 33 * Real.exp (-(dom.c₀ / 32) * eps) := by
  obtain ⟨KU, hKU⟩ := ceps_strip_bridge_error dom hθ hD hDg hθg hvlo hvhi Kf
  set KE := max (stripEntranceConst dom Dg vlo vhi) 0 with hKEdef
  set CH := max (cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0) 0
    with hCHdef
  set C0 := max (cepsBandMomentConst (cepsBandPinDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0) 0
    with hC0def
  set C1 := max (cepsBandMomentConst (cepsBandPinDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 1) 0
    with hC1def
  set KU' := max KU 0 with hKU'def
  have hKE : 0 ≤ KE := le_max_right _ _
  have hCH : 0 ≤ CH := le_max_right _ _
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hKU' : 0 ≤ KU' := le_max_right _ _
  set Kin := KE * (2 * CH + KE) * (C1 + 2 * C0) + 2 * (CH + KE) ^ 2 * KU' with hKindef
  have hKin : 0 ≤ Kin := by positivity
  refine ⟨4 ^ 33 * Kin, ?_⟩
  intro ν f fW hν hf hLip hW μ hμ t ht htn eps heps
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  have hc0 := dom.c₀_pos
  -- windows
  have hμ1 : |μ| ≤ 1 / 2 := hμ.trans (min_le_right _ _)
  have hμ4 : |μ| ≤ min dom.renewalMu (1 / (64 * Dg)) := hμ.trans (min_le_left _ _)
  have hμR : |μ| ≤ dom.renewalMu := hμ4.trans (min_le_left _ _)
  have hμa := abs_le.mp hμ1
  have heps1 : 1 ≤ eps := (le_max_right _ _).trans heps
  have hepsW : max dom.stripEntranceWidth 4 ≤ eps := (le_max_left _ _).trans heps
  obtain ⟨hll, hlu⟩ := pair_width_bounds (by linarith : 0 ≤ eps) hμ1
  set l := 2 * eps * (1 + μ) with hldef
  have hlW : max dom.stripEntranceWidth 4 ≤ l := hepsW.trans hll
  have hlE : dom.stripEntranceWidth ≤ l := (le_max_left _ _).trans hlW
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hlW
  have hl0 : 0 ≤ l := by linarith
  have hX : 1 ≤ 1 + l := by linarith
  have htM : ‖t‖ ≤ dom.stripMarkBound := htn.trans (min_le_left _ _)
  have htD : ‖t‖ ≤ dom.renewalDiscount / 6 := htn.trans (min_le_right _ _)
  set q := t * ((1 + μ : ℝ) : ℂ) with hqdef
  have hqre : q.re = 0 := by simp [hqdef, ht]
  have hq0 : 0 ≤ q.re := hqre.ge
  have hqn : ‖q‖ ≤ dom.renewalDiscount / 4 := by
    have h1 : ‖((1 + μ : ℝ) : ℂ)‖ ≤ 3 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
    calc ‖q‖ = ‖t‖ * ‖((1 + μ : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ (dom.renewalDiscount / 6) * (3 / 2) :=
          mul_le_mul htD h1 (norm_nonneg _) (by have := dom.renewalDiscount_pos hD; positivity)
      _ = dom.renewalDiscount / 4 := by ring
  -- S-3 (a), S-4, the marked bridge
  have hHerr := (ceps_strip_entrance_error_top dom hθ hD hDg hθg hvlo hvhi hν hf hW hμR hlE).2
    t ht htM
  have hUerr := hKU ν f fW hν hf hLip hW μ hμ4 q hq0 hqn l hlW
  have hmk := cepsMarkedBridge_eq_deriv hDg hθg hvlo hvhi hν hf (l := l) (by linarith)
    (2 * eps) μ hq0
  -- X3 / X7 bounds of the actual objects
  have hκ := krKappa_pos hDg hvlo hvhi
  have hq32 : -(krKappa Dg vlo vhi / (32 * l ^ 2)) ≤ q.re := by
    rw [hqre]
    have : 0 ≤ krKappa Dg vlo vhi / (32 * l ^ 2) := by positivity
    linarith
  have hHb := cepsBandDisc_stripEntrance_iteratedDeriv_le hDg hθg hvlo hvhi hν (w := l) (l := l)
    (by linarith) (by linarith) (by linarith) (t := t) (by rw [ht]) hq32 μ 0
  rw [iteratedDeriv_zero] at hHb
  have hU0 := cepsBandDisc_bridge_iteratedDeriv_le hDg hθg hvlo hvhi hν hf (w := l) (l := l)
    (by linarith) (by linarith) (by linarith) hq32 μ 0
  rw [iteratedDeriv_zero] at hU0
  have hU1 := cepsBandDisc_bridge_iteratedDeriv_le hDg hθg hvlo hvhi hν hf (w := l) (l := l)
    (by linarith) (by linarith) (by linarith) hq32 μ 1
  rw [iteratedDeriv_one] at hU1
  -- the two pairs
  have hq' : t * (1 + ((μ : ℝ) : ℂ)) = q := by rw [hqdef]; push_cast; ring
  have hl' : ((2 * eps : ℝ) : ℂ) * (1 + ((μ : ℝ) : ℂ)) = (l : ℂ) := by
    rw [hldef]; push_cast; ring
  have hpair : cepsNormalRegularPair (cepsNormalData D θ ρ) (dom.canonL ρ) μ t ((2 * eps : ℝ) : ℂ) =
      exp (t * (l : ℂ)) * ((cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t) ^ 2 *
        (-deriv (fun q' => (cepsNormalData D θ ρ μ q').regularBridge (dom.canonL ρ) μ q' l) q -
          ((2 * eps : ℝ) : ℂ) * (cepsNormalData D θ ρ μ q).regularBridge (dom.canonL ρ) μ q l) := by
    unfold cepsNormalRegularPair
    dsimp only
    rw [hq', hl']
  have hact : cepsActualPair ν f eps t μ = exp (t * (l : ℂ)) * (cepsStripEntrance ν t μ q l) ^ 2 *
      cepsMarkedBridge ν f (2 * eps) μ q l := rfl
  rw [hact, hpair, hmk]
  set H := cepsStripEntrance ν t μ q l with hHdef
  set Hh := (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t with hHhdef
  set U := cepsBridge ν f μ q l with hUdef
  set Uh := (cepsNormalData D θ ρ μ q).regularBridge (dom.canonL ρ) μ q l with hUhdef
  set dU := deriv (fun z => cepsBridge ν f μ z l) q with hdUdef
  set dUh := deriv (fun q' => (cepsNormalData D θ ρ μ q').regularBridge (dom.canonL ρ) μ q' l) q
    with hdUhdef
  set w : ℂ := ((2 * eps : ℝ) : ℂ) with hwdef
  have hw : ‖w‖ = 2 * eps := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hfac : exp (t * (l : ℂ)) * H ^ 2 * (-dU - w * U) - exp (t * (l : ℂ)) * Hh ^ 2 * (-dUh - w * Uh) =
      exp (t * (l : ℂ)) * (H ^ 2 * (-dU - w * U) - Hh ^ 2 * (-dUh - w * Uh)) := by ring
  have hexp : ‖exp (t * (l : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp [ht]
  rw [hfac, norm_mul, hexp, one_mul]
  -- the four inputs of the algebra
  set E := Real.exp (-(dom.c₀ / 32) * l) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hcl : 0 ≤ dom.c₀ * l := mul_nonneg hc0.le hl0
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE8 : Real.exp (-(dom.c₀ / 8) * l) ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hpl : ∀ k : ℕ, l ^ k ≤ (1 + l) ^ k := fun k => pow_le_pow_left₀ hl0 (by linarith) k
  have ha : ‖H‖ ≤ CH * (1 + l) ^ 3 := by
    refine hHb.trans ?_
    norm_num only [Nat.mul_zero, Nat.zero_add]
    exact mul_le_mul (le_max_left _ _) (hpl 3) (by positivity) hCH
  have he : ‖H - Hh‖ ≤ KE * (1 + l) ^ 7 * E := by
    refine hHerr.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hE8
      (Real.exp_pos _).le (by positivity)
  have hu : ‖-dU - w * U‖ ≤ (C1 + 2 * C0) * (1 + l) ^ 5 := by
    have h1 : ‖dU‖ ≤ C1 * (1 + l) ^ 5 := by
      refine hU1.trans ?_
      norm_num only [Nat.mul_one]
      exact mul_le_mul (le_max_left _ _) (hpl 5) (by positivity) hC1
    have h2 : ‖U‖ ≤ C0 * (1 + l) ^ 3 := by
      refine hU0.trans ?_
      norm_num only [Nat.mul_zero, Nat.zero_add]
      exact mul_le_mul (le_max_left _ _) (hpl 3) (by positivity) hC0
    have h3 : ‖w * U‖ ≤ 2 * C0 * (1 + l) ^ 5 := by
      rw [norm_mul, hw]
      have hp : 2 * eps * (1 + l) ^ 3 ≤ 2 * (1 + l) ^ 5 := by
        have h5 : 2 * (1 + l) ^ 5 = 2 * (1 + l) ^ 2 * (1 + l) ^ 3 := by ring
        rw [h5]
        have hsq : 1 + l ≤ (1 + l) ^ 2 := le_self_pow₀ hX (by norm_num)
        have h12 : 2 * eps ≤ 2 * (1 + l) ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right h12 (by positivity)
      calc 2 * eps * ‖U‖ ≤ 2 * eps * (C0 * (1 + l) ^ 3) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = C0 * (2 * eps * (1 + l) ^ 3) := by ring
        _ ≤ C0 * (2 * (1 + l) ^ 5) := mul_le_mul_of_nonneg_left hp hC0
        _ = 2 * C0 * (1 + l) ^ 5 := by ring
    calc ‖-dU - w * U‖ ≤ ‖dU‖ + ‖w * U‖ := by
          rw [show -dU - w * U = -(dU + w * U) by ring, norm_neg]; exact norm_add_le _ _
      _ ≤ C1 * (1 + l) ^ 5 + 2 * C0 * (1 + l) ^ 5 := add_le_add h1 h3
      _ = (C1 + 2 * C0) * (1 + l) ^ 5 := by ring
  have hd : ‖(-dU - w * U) - (-dUh - w * Uh)‖ ≤ 2 * KU' * (1 + l) ^ 19 * E := by
    have hU' : ‖U - Uh‖ + ‖dU - dUh‖ ≤ KU' * (1 + l) ^ 18 * E :=
      hUerr.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hE0)
    have hn : ‖(-dU - w * U) - (-dUh - w * Uh)‖ ≤ ‖dU - dUh‖ + 2 * eps * ‖U - Uh‖ := by
      rw [show (-dU - w * U) - (-dUh - w * Uh) = -((dU - dUh) + w * (U - Uh)) by ring, norm_neg]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hw]
    have hS : 0 ≤ ‖U - Uh‖ := norm_nonneg _
    have hT : 0 ≤ ‖dU - dUh‖ := norm_nonneg _
    have hw2 : 2 * eps ≤ 2 * (1 + l) := by linarith
    calc ‖(-dU - w * U) - (-dUh - w * Uh)‖ ≤ ‖dU - dUh‖ + 2 * eps * ‖U - Uh‖ := hn
      _ ≤ 2 * (1 + l) * (‖U - Uh‖ + ‖dU - dUh‖) := by
          have h1 := mul_le_mul_of_nonneg_right hw2 hS
          have h2 : ‖dU - dUh‖ ≤ 2 * (1 + l) * ‖dU - dUh‖ :=
            le_mul_of_one_le_left hT (by linarith)
          rw [mul_add]
          linarith
      _ ≤ 2 * (1 + l) * (KU' * (1 + l) ^ 18 * E) :=
          mul_le_mul_of_nonneg_left hU' (by linarith)
      _ = 2 * KU' * (1 + l) ^ 19 * E := by ring
  -- back to `ε`
  have hX4 : 1 + l ≤ 4 * eps := by linarith
  have hp33 : (1 + l) ^ 33 ≤ 4 ^ 33 * eps ^ 33 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hX4 33
  have hEe : E ≤ Real.exp (-(dom.c₀ / 32) * eps) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hll (by positivity : 0 ≤ dom.c₀ / 32)
    linarith
  have hX0 : 0 ≤ 1 + l := by linarith
  have hCU : 0 ≤ C1 + 2 * C0 := add_nonneg hC1 (mul_nonneg zero_le_two hC0)
  have hpow0 : 0 ≤ 4 ^ 33 * eps ^ 33 := mul_nonneg (by norm_num) (pow_nonneg (by linarith) 33)
  have hbud := pair_budget_le (X := 1 + l) (E := E) (KE := KE) (CH := CH) (CU := C1 + 2 * C0)
    (KU := KU') (a := CH * (1 + l) ^ 3) (e := KE * (1 + l) ^ 7 * E) (u := (C1 + 2 * C0) * (1 + l) ^ 5)
    (d := 2 * KU' * (1 + l) ^ 19 * E) hX hE0 hE1 hKE hCH hCU hKU' (mul_nonneg hCH (pow_nonneg hX0 3))
    (mul_nonneg (mul_nonneg hKE (pow_nonneg hX0 7)) hE0) (mul_nonneg hCU (pow_nonneg hX0 5))
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hKU') (pow_nonneg hX0 19)) hE0)
    le_rfl le_rfl le_rfl le_rfl
  have hmain := (norm_sq_mul_sub_le ha he hu hd).trans hbud
  refine hmain.trans ?_
  calc Kin * (1 + l) ^ 33 * E ≤ Kin * (4 ^ 33 * eps ^ 33) * Real.exp (-(dom.c₀ / 32) * eps) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp33 hKin) hEe hE0 (mul_nonneg hKin hpow0)
    _ = 4 ^ 33 * Kin * eps ^ 33 * Real.exp (-(dom.c₀ / 32) * eps) := by ring

end

end PGM
