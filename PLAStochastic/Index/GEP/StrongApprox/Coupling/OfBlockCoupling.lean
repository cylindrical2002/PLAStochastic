import PLAStochastic.Index.GEP.StrongApprox.Coupling.BadEvents
import PLAStochastic.Index.GEP.StrongApprox.Coupling.Desmoothing

/-! # From a finite block coupling to the frozen strong-approximation interface -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set
open scoped NNReal

/-- Lift a finite leaf coupling, add the within-block probability budgets, and remove smoothing.
Every error term and marginal probability is explicit; the leaf coupling is the only input
that the dyadic construction must supply. -/
theorem sa_coupling_of_leaf_coupling (ν : ProbabilityMeasure ℝ) (hv : 0 < lawVar ν)
    {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) (L : ℕ)
    (π : Measure ((Fin L → ℝ) × (Fin L → ℝ))) [IsProbabilityMeasure π]
    (hleft : π.fst = Measure.pi (fun _ : Fin L =>
      ((saDensity_centeredSum ν hs hm).law : Measure ℝ)))
    (hright : π.snd = Measure.pi (fun _ : Fin L =>
      gaussianReal 0 ((m : ℝ≥0) * Real.toNNReal (lawVar ν + s ^ 2))))
    {a p : ℝ} (hleaf : π.real (saLeafBad L a) ≤ p) (b c r : ℝ) :
    HasSACoupling ν (L * m)
      (a + |s| * r + b + Real.sqrt (lawVar ν + s ^ 2) * c +
        s ^ 2 / (2 * Real.sqrt (lawVar ν)) * r)
      (p + (iidLaw ν).real (saBlocksBad m L 1 b) +
        (iidLaw gaussPM).real (saBlocksBad m L 0 c) +
        2 * (iidLaw gaussPM).real (saWalkBad (L * m) 0 r)) := by
  let S := saSmoothedBlockTotals m L s
  let T := saScaledBlockTotals m L (Real.sqrt (lawVar ν + s ^ 2))
  have hS : Measurable S := measurable_saSmoothedBlockTotals m L s
  have hT : Measurable T := measurable_saScaledBlockTotals m L _
  have hSlaw := saSmoothedBlockTotals_law ν hs hm L
  have hTlaw := saScaledBlockTotals_law m L (Real.sqrt (lawVar ν + s ^ 2))
  rw [Real.sq_sqrt (by positivity : 0 ≤ lawVar ν + s ^ 2)] at hTlaw
  obtain ⟨P, hP, hPleft, hPright, hPstat⟩ := sa_exists_coupling_lift
    ((iidLaw ν).prod (iidLaw gaussPM)) (iidLaw gaussPM) hS hT π
    (hleft.trans hSlaw.symm) (hright.trans hTlaw.symm)
  let := hP
  let X : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) → ℕ → ℝ := fun q => q.1.1
  let Ξ : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) → ℕ → ℝ := fun q => q.1.2
  let Z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) → ℕ → ℝ := fun q => q.2
  have hX : Measurable X := measurable_fst.fst
  have hΞ : Measurable Ξ := measurable_fst.snd
  have hZ : Measurable Z := measurable_snd
  have hXlaw : P.map X = iidLaw ν := by
    change P.map (Prod.fst ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_fst measurable_fst]
    change P.fst.map Prod.fst = _
    rw [hPleft]
    simp
  have hΞlaw : P.map Ξ = iidLaw gaussPM := by
    change P.map (Prod.snd ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_snd measurable_fst]
    change P.fst.map Prod.snd = _
    rw [hPleft]
    simp
  have hZlaw : P.map Z = iidLaw gaussPM := hPright
  let E := (Prod.map S T) ⁻¹' saLeafBad L a
  let BX := X ⁻¹' saBlocksBad m L 1 b
  let BZ := Z ⁻¹' saBlocksBad m L 0 c
  let BΞ := Ξ ⁻¹' saWalkBad (L * m) 0 r
  let BG := Z ⁻¹' saWalkBad (L * m) 0 r
  let G := (E ∪ BX ∪ BZ ∪ BΞ ∪ BG)ᶜ
  have hEprob : P.real E = π.real (saLeafBad L a) := by
    rw [← hPstat, map_measureReal_apply (hS.prodMap hT) (measurableSet_saLeafBad _ _)]
  have hBXprob : P.real BX = (iidLaw ν).real (saBlocksBad m L 1 b) := by
    rw [← hXlaw, map_measureReal_apply hX (measurableSet_saBlocksBad _ _ _ _)]
  have hBZprob : P.real BZ = (iidLaw gaussPM).real (saBlocksBad m L 0 c) := by
    rw [← hZlaw, map_measureReal_apply hZ (measurableSet_saBlocksBad _ _ _ _)]
  have hBΞprob : P.real BΞ = (iidLaw gaussPM).real (saWalkBad (L * m) 0 r) := by
    rw [← hΞlaw, map_measureReal_apply hΞ (measurableSet_saWalkBad _ _ _)]
  have hBGprob : P.real BG = (iidLaw gaussPM).real (saWalkBad (L * m) 0 r) := by
    rw [← hZlaw, map_measureReal_apply hZ (measurableSet_saWalkBad _ _ _)]
  apply sa_coupling_of_good_event P ν hX hZ hXlaw hZlaw (G := G)
  · intro q hq
    change q ∉ E ∪ BX ∪ BZ ∪ BΞ ∪ BG at hq
    simp only [mem_union, not_or] at hq
    obtain ⟨⟨⟨⟨hqE, hqX⟩, hqZ⟩, hqΞ⟩, hqG⟩ := hq
    have hdiv : L * m / m = L := Nat.mul_div_cancel L hm
    apply sa_block_desmoothing_error (ξ := Ξ q) (s := s) (m := m) hv hm
    · intro j hj
      rw [hdiv] at hj
      have he : |vkeys (S q.1) j - vkeys (T q.2) j| ≤ a := by
        by_contra herr
        exact hqE ⟨j, hj, lt_of_not_ge herr⟩
      rw [saSmoothedBlockTotals_prefix m L s q.1 hj,
        saScaledBlockTotals_prefix m L _ q.2 hj] at he
      exact he
    · intro j hj k hk _
      rw [hdiv] at hj
      have he : |gapKeys (X q) (j * m + k) - gapKeys (X q) (j * m) - 1 * k| ≤ b := by
        by_contra herr
        exact hqX ⟨j, hj, k, hk.le, lt_of_not_ge herr⟩
      simpa only [one_mul] using he
    · intro j hj k hk _
      rw [hdiv] at hj
      have he : |gapKeys (Z q) (j * m + k) - gapKeys (Z q) (j * m) - 0 * k| ≤ c := by
        by_contra herr
        exact hqZ ⟨j, hj, k, hk.le, lt_of_not_ge herr⟩
      simpa only [zero_mul, sub_zero] using he
    · intro k hk
      have he : |gapKeys (Ξ q) k - 0 * k| ≤ r := by
        by_contra herr
        exact hqΞ ⟨k, hk, lt_of_not_ge herr⟩
      simpa only [zero_mul, sub_zero] using he
    · intro k hk
      have he : |gapKeys (Z q) k - 0 * k| ≤ r := by
        by_contra herr
        exact hqG ⟨k, hk, lt_of_not_ge herr⟩
      simpa only [zero_mul, sub_zero] using he
  · have hu : P.real (E ∪ BX ∪ BZ ∪ BΞ ∪ BG) ≤
        P.real E + P.real BX + P.real BZ + P.real BΞ + P.real BG := by
      linarith [measureReal_union_le (μ := P) E BX,
        measureReal_union_le (μ := P) (E ∪ BX) BZ,
        measureReal_union_le (μ := P) (E ∪ BX ∪ BZ) BΞ,
        measureReal_union_le (μ := P) (E ∪ BX ∪ BZ ∪ BΞ) BG]
    change P.real (E ∪ BX ∪ BZ ∪ BΞ ∪ BG)ᶜᶜ ≤ _
    rw [compl_compl]
    rw [hEprob, hBXprob, hBZprob, hBΞprob, hBGprob] at hu
    linarith

end

end PGM
