import PLAStochastic.Index.GEP.RawDisc.OneLetterLaws

/-!
# WP4 `RawDisc` assembly, part 7: the derivative of the occupation series at `0`

The derivative of `Ψ_k` at `0` (`occDeriv`, `PLAStochastic/Index/GEP/RawDisc/SurvivalPolynomials.lean`) is
`α_k(G_σ) - α_k(G_ν) + ∑_{i<k} (β_{k,i}(G_ν) - α_k(G_ν))`, with `α_k(G) = E_ν[G(S_k) 1{k<T}]` and
`β_{k,i}(G) = E_{wordLaw ν σ {i}}[G(S_k) 1{k<T}]`.  On the other side,
`∫ I_F dσ - ∫ I_F dν = ∑_i D_i`, `D_i = E_{wLaw ν σ i}[1{i<T} F(S_T)] - E_ν[1{i<T} F(S_T)]`
(`integral_insTerm`).  Telescoping each `D_i` from `S_i` (the `1{i<T} F(S_i)` parts agree: they
read only `g 0, …, g (i-1)`) gives `D_i = ∑_j c(i, j)` with the pair terms
`c(i, j) = E_{wLaw ν σ i}[1{i+j<T}(F(S_{i+j+1}) - F(S_{i+j}))] - E_ν[⋯]` (`hasSum_pairC`); the
next gap is independent, so `c(i, 0) = α_i(G_σ) - α_i(G_ν)` and
`c(i, j+1) = β_{i+j+1,i}(G_ν) - α_{i+j+1}(G_ν)`.  Hence `∑_{i ≤ k} c(i, k-i) = Ψ_k'(0)`
(`sum_pairC_eq`).  The pair terms are absolutely summable, `|c(i,j)| ≤ 3 sW σ i (i+j) + 3 sW ν i (i+j)`
(`WSummable`), so the double series may be summed along rows and along diagonals
(`hasSum_occDeriv`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {eps l : ℝ} {ν σ ρ : ProbabilityMeasure ℝ} {F : ℝ → ℝ}

/-! ## The telescoping terms under one-letter laws -/

/-- The telescoping terms `E_{wLaw ν ρ i}[1{i+j<T}(F(S_{i+j+1}) - F(S_{i+j}))]`. -/
def termW (eps : ℝ) (ν ρ : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (i j : ℕ) : ℝ :=
  ∫ g, incInd eps F (i + j) g ∂(wLaw ν ρ i)

theorem termW_eq (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i j : ℕ) :
    termW eps ν ρ F i j = survInt eps (wLaw ν ρ i) (i + j)
      (incFn F (Function.update (fun _ => ν) i ρ (i + j))) := by
  unfold termW wLaw
  exact integral_incInd _ eps hF (i + j)
    (integrable_incInd (smallMgf_wLaw hν hρ i) eps hF hFb (i + j))

theorem survInt_wLaw_self {G : ℝ → ℝ} (hG : Measurable G) (i : ℕ) :
    survInt eps (wLaw ν ρ i) i G = survInt eps (iidLaw ν) i G := by
  unfold survInt wLaw
  rw [iidLaw_eq_piLaw]
  exact integral_piLaw_prefix (wLaw_agree ν ρ i) (measurable_survInd eps i hG)
    (depPrefix_survInd eps i G)

theorem termW_zero (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i : ℕ) :
    termW eps ν ρ F i 0 = survInt eps (iidLaw ν) i (incFn F ρ) := by
  rw [termW_eq hν hρ hF hFb, add_zero, Function.update_self,
    survInt_wLaw_self (measurable_incFn hF ρ)]

theorem termW_succ (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i j : ℕ) :
    termW eps ν ρ F i (j + 1) = survInt eps (wLaw ν ρ i) (i + (j + 1)) (incFn F ν) := by
  rw [termW_eq hν hρ hF hFb, Function.update_of_ne (by omega)]

/-- A survival integral with a test `|G| ≤ 3 e^{l s}` is at most three survival values of the
exponential test. -/
theorem abs_survInt_le {ρs : ℕ → ProbabilityMeasure ℝ} (hρs : ∀ j, SmallMgf l (ρs j)) (k : ℕ)
    {G : ℝ → ℝ} (hGb : ∀ y, 0 ≤ y → |G y| ≤ 3 * Real.exp (l * y)) :
    |survInt eps (piLaw ρs) k G| ≤ 3 * survInt eps (piLaw ρs) k (expTest l) := by
  have hE : Integrable ((survSet eps k).indicator (fun g => expTest l (gapKeys g k)))
      (piLaw ρs) :=
    integrable_survInd (C := 1) eps k (fun j => (hρs j).pos) (fun j => (hρs j).lle)
      (measurable_expTest l) (fun y _ => by rw [one_mul, expTest, abs_of_pos (Real.exp_pos _)])
  have h := norm_integral_le_of_norm_le (hE.const_mul 3)
    (f := (survSet eps k).indicator (fun g => G (gapKeys g k))) (by
      filter_upwards [ae_pos_piLaw fun j => (hρs j).pos] with g hg
      by_cases hs : g ∈ survSet eps k
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs, expTest]
        exact hGb _ (gapKeys_nonneg (fun j => (hg j).le) k)
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero, mul_zero])
  rw [integral_const_mul] at h
  rw [← Real.norm_eq_abs]
  exact h

theorem abs_termW_le (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i j : ℕ) :
    |termW eps ν ρ F i j| ≤ 3 * sW eps l ν ρ i (i + j) := by
  rw [termW_eq hν hρ hF hFb]
  exact abs_survInt_le (smallMgf_wLaw hν hρ i) (i + j)
    fun y hy => abs_incFn_le (smallMgf_wLaw hν hρ i (i + j)) hFb hy

/-! ## The pair terms -/

/-- The pair terms `c(i, j)`. -/
def pairC (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (i j : ℕ) : ℝ :=
  termW eps ν σ F i j - termW eps ν ν F i j

theorem abs_pairC_le (hν : SmallMgf l ν) (hσ : SmallMgf l σ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i j : ℕ) :
    |pairC eps ν σ F i j| ≤ 3 * sW eps l ν σ i (i + j) + 3 * sW eps l ν ν i (i + j) :=
  (abs_sub _ _).trans (add_le_add (abs_termW_le hν hσ hF hFb i j) (abs_termW_le hν hν hF hFb i j))

/-- **Row sums**: `∑_j c(i, j) = D_i`. -/
theorem hasSum_pairC (hl : 0 ≤ l) (hν : SmallMgf l ν) (hσ : SmallMgf l σ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (hWν : WSummable eps l ν ν)
    (hWσ : WSummable eps l ν σ) (i : ℕ) (hs : Summable fun j => pairC eps ν σ F i j) :
    HasSum (fun j => pairC eps ν σ F i j)
      (∫ g, stopInd eps F i g ∂(wLaw ν σ i) - ∫ g, stopInd eps F i g ∂(wLaw ν ν i)) := by
  obtain ⟨finσ, intEσ, -, -⟩ := hWσ.facts hl hν hσ hF hFb
  obtain ⟨finν, intEν, -, -⟩ := hWν.facts hl hν hν hF hFb
  have tσ := tendsto_telescope (μ := wLaw ν σ i) hl hF hFb (ae_nonneg_wLaw hν hσ i) (finσ i) i
    (intEσ i)
  have tν := tendsto_telescope (μ := wLaw ν ν i) hl hF hFb (ae_nonneg_wLaw hν hν i) (finν i) i
    (intEν i)
  have hbase : ∫ g, (survSet eps i).indicator (fun g => F (gapKeys g i)) g ∂(wLaw ν σ i) =
      ∫ g, (survSet eps i).indicator (fun g => F (gapKeys g i)) g ∂(wLaw ν ν i) := by
    unfold wLaw
    exact integral_piLaw_prefix (wLaw_agree' ν σ ν i) (measurable_survInd eps i hF)
      (depPrefix_survInd eps i F)
  have t := tσ.sub tν
  have e1 : (fun n => ∑ j ∈ Finset.range n, ∫ g, incInd eps F (i + j) g ∂(wLaw ν σ i) -
      ∑ j ∈ Finset.range n, ∫ g, incInd eps F (i + j) g ∂(wLaw ν ν i)) =
      fun n => ∑ j ∈ Finset.range n, pairC eps ν σ F i j := by
    funext n
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [e1, hbase, sub_sub_sub_cancel_right] at t
  have hu := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat t
  unfold stopInd
  rw [← hu]
  exact hs.hasSum

/-- **Diagonal sums**: `∑_{i ≤ k} c(i, k - i) = Ψ_k'(0)`. -/
theorem sum_pairC_eq (hν : SmallMgf l ν) (hσ : SmallMgf l σ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), pairC eps ν σ F i (k - i) =
      occDeriv eps ν σ (incFn F ν) (incFn F σ) k := by
  rw [Finset.sum_range_succ, Nat.sub_self]
  have hk0 : pairC eps ν σ F k 0 =
      survInt eps (iidLaw ν) k (incFn F σ) - survInt eps (iidLaw ν) k (incFn F ν) := by
    rw [pairC, termW_zero hν hσ hF hFb, termW_zero hν hν hF hFb]
  have hi : ∀ i ∈ Finset.range k, pairC eps ν σ F i (k - i) =
      survInt eps (wordLaw ν σ {i}) k (incFn F ν) - survInt eps (iidLaw ν) k (incFn F ν) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e : k - i = (k - i - 1) + 1 := by omega
    have e' : i + (k - i - 1 + 1) = k := by omega
    rw [e, pairC, termW_succ hν hσ hF hFb, termW_succ hν hν hF hFb, e', wLaw_sigma, wLaw_self]
  rw [Finset.sum_congr rfl hi, hk0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, occDeriv, survLin]
  ring

/-! ## The double series -/

/-- The pair terms indexed by `(i, k)`, `i ≤ k`. -/
def pairC' (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (p : ℕ × ℕ) : ℝ :=
  if p.1 ≤ p.2 then pairC eps ν σ F p.1 (p.2 - p.1) else 0

theorem summable_pairC' (hν : SmallMgf l ν) (hσ : SmallMgf l σ) (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (hWν : WSummable eps l ν ν)
    (hWσ : WSummable eps l ν σ) : Summable (pairC' eps ν σ F) := by
  set b : ℕ × ℕ → ℝ := fun q =>
    if q.2 ≤ q.1 then 3 * sW eps l ν σ q.2 q.1 + 3 * sW eps l ν ν q.2 q.1 else 0 with hb
  have hb0 : 0 ≤ b := fun q => by
    simp only [hb, Pi.zero_apply]
    split_ifs
    · exact add_nonneg (mul_nonneg (by norm_num) (sW_nonneg _ _ _ _ _ _))
        (mul_nonneg (by norm_num) (sW_nonneg _ _ _ _ _ _))
    · exact le_rfl
  have hfib : ∀ k, ∑' i, b (k, i) =
      3 * ∑ i ∈ Finset.range (k + 1), sW eps l ν σ i k +
        3 * ∑ i ∈ Finset.range (k + 1), sW eps l ν ν i k := by
    intro k
    rw [tsum_eq_sum (s := Finset.range (k + 1)) fun i hi => by
      rw [Finset.mem_range] at hi
      simp only [hb]
      rw [if_neg (by omega)]]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp only [hb]
    rw [if_pos (by omega)]
  have hbs : Summable b := by
    refine (summable_prod_of_nonneg hb0).2 ⟨fun k => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := Finset.range (k + 1)) fun i hi => by
        rw [Finset.mem_range] at hi
        simp only [hb]
        rw [if_neg (by omega)]
    · simp_rw [hfib]
      exact (hWσ.mul_left 3).add (hWν.mul_left 3)
  have hbs' : Summable (b ∘ Equiv.prodComm ℕ ℕ) := (Equiv.prodComm ℕ ℕ).summable_iff.2 hbs
  refine Summable.of_norm_bounded hbs' fun p => ?_
  obtain ⟨i, k⟩ := p
  change ‖pairC' eps ν σ F (i, k)‖ ≤ b (k, i)
  simp only [pairC', hb]
  split_ifs with h
  · rw [Real.norm_eq_abs]
    have := abs_pairC_le (eps := eps) hν hσ hF hFb i (k - i)
    rwa [show i + (k - i) = k by omega] at this
  · rw [norm_zero]

/-- **The derivative identity**: `∑_k Ψ_k'(0) = ∫ I_F dσ - ∫ I_F dν`. -/
theorem hasSum_occDeriv (hl : 0 ≤ l) (hν : SmallMgf l ν) (hσ : SmallMgf l σ)
    (hF : Measurable F) (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y))
    (hWν : WSummable eps l ν ν) (hWσ : WSummable eps l ν σ) :
    HasSum (fun k => occDeriv eps ν σ (incFn F ν) (incFn F σ) k)
      ((∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(σ : Measure ℝ)) -
        ∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(ν : Measure ℝ)) := by
  obtain ⟨-, -, intSσ, totσ⟩ := hWσ.facts hl hν hσ hF hFb
  obtain ⟨-, -, intSν, totν⟩ := hWν.facts hl hν hν hF hFb
  -- the insertion kernel as a series
  have hker : ∀ {ρ : ProbabilityMeasure ℝ},
      ∑' i, ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ) ≠ ⊤ →
      HasSum (fun i => ∫ x, insTerm eps ν F i x ∂(ρ : Measure ℝ))
        (∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(ρ : Measure ℝ)) := by
    intro ρ htot
    have h1 := integral_tsum (μ := (ρ : Measure ℝ)) (f := fun i x => insTerm eps ν F i x)
      (fun i => (measurable_insTerm eps ν hF i).aestronglyMeasurable) htot
    have hs : Summable fun i => ∫ x, insTerm eps ν F i x ∂(ρ : Measure ℝ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal htot) fun i => ?_
      have hne : ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ) ≠ ⊤ :=
        ne_top_of_le_ne_top htot (ENNReal.le_tsum (f := fun i =>
          ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ)) i)
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hne (enorm_integral_le_lintegral_enorm _)
    have e : ∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(ρ : Measure ℝ) =
        ∑' i, ∫ x, insTerm eps ν F i x ∂(ρ : Measure ℝ) := h1
    rw [e]
    exact hs.hasSum
  have hD : HasSum (fun i => ∫ g, stopInd eps F i g ∂(wLaw ν σ i) -
      ∫ g, stopInd eps F i g ∂(wLaw ν ν i))
      ((∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(σ : Measure ℝ)) -
        ∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(ν : Measure ℝ)) := by
    have h := (hker totσ).sub (hker totν)
    refine h.congr_fun fun i => ?_
    rw [integral_insTerm hF i (intSσ i), integral_insTerm hF i (intSν i)]
  -- the double series
  have hsum := summable_pairC' hν hσ hF hFb hWν hWσ
  have hrow : ∀ i, HasSum (fun k => pairC' eps ν σ F (i, k))
      (∫ g, stopInd eps F i g ∂(wLaw ν σ i) - ∫ g, stopInd eps F i g ∂(wLaw ν ν i)) := by
    intro i
    have hsi : Summable fun k => pairC' eps ν σ F (i, k) := hsum.prod_factor i
    have e : ∀ n, pairC' eps ν σ F (i, n + i) = pairC eps ν σ F i n := fun n => by
      simp only [pairC']
      rw [if_pos (by omega), Nat.add_sub_cancel]
    have hs' : Summable fun j => pairC eps ν σ F i j := by
      have := (summable_nat_add_iff i).2 hsi
      simp_rw [e] at this
      exact this
    have h := hasSum_pairC hl hν hσ hF hFb hWν hWσ i hs'
    have h0 : ∑ j ∈ Finset.range i, pairC' eps ν σ F (i, j) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [Finset.mem_range] at hj
        simp only [pairC']
        rw [if_neg (by omega)]
    rw [← hasSum_nat_add_iff' i, h0, sub_zero]
    simp_rw [e]
    exact h
  have hLD := hsum.hasSum.prod_fiberwise hrow
  have hLeq := hLD.unique hD
  have hsw : HasSum (pairC' eps ν σ F ∘ Equiv.prodComm ℕ ℕ) (∑' p, pairC' eps ν σ F p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hsum.hasSum
  have hcol : ∀ k, HasSum (fun i => (pairC' eps ν σ F ∘ Equiv.prodComm ℕ ℕ) (k, i))
      (occDeriv eps ν σ (incFn F ν) (incFn F σ) k) := by
    intro k
    rw [← sum_pairC_eq hν hσ hF hFb k]
    have h : HasSum (fun i => (pairC' eps ν σ F ∘ Equiv.prodComm ℕ ℕ) (k, i))
        (∑ i ∈ Finset.range (k + 1), (pairC' eps ν σ F ∘ Equiv.prodComm ℕ ℕ) (k, i)) :=
      hasSum_sum_of_ne_finset_zero fun i hi => by
        rw [Finset.mem_range] at hi
        change pairC' eps ν σ F (i, k) = 0
        unfold pairC'
        rw [if_neg (show ¬ (i ≤ k) by omega)]
    convert h using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    change _ = pairC' eps ν σ F (i, k)
    unfold pairC'
    rw [if_pos (show i ≤ k by omega)]
  have := hsw.prod_fiberwise hcol
  rw [hLeq] at this
  exact this

end

end PGM
