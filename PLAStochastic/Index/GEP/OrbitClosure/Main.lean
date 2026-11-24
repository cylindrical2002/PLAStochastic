import PLAStochastic.Index.GEP.OrbitClosure.OneLayerEnvelope
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.Additive.OfInputs

/-!
# WP2: `OrbitClosure`

Design note: `research/2026-09-28-lean-gep-additive/wp2-design.md`.

For a regular class `RegLaw D θ vlo vhi` put `b = regB vhi`, `β = regBeta D θ vlo`,
`v = regV vlo`, `θu = min(θ/2, θK)`, `Bu = max(2D/θ, CK)`.  `lawPhi_envelope` for these
constants gives `K, c`; set `Ds = max(D, K)` and `θ' = min(θ, c)`.  For `eps` beyond the
thresholds of `lawPhi_momClass`, `lawPhi_expMom` and `lawPhi_envelope` (the last taken at the
fixed density bound `Ds`), induction on `j` keeps

`MomClass b β v ν_j`, `ExpMom θu Bu ν_j`, `EnvBd Ds θ' ν_j`,  `ν_j = (lawPhi eps)^[j] ν`:

the moment class by `lawPhi_momClass`; the exponential moment by `lawPhi_expMom` (absolute
output constants `θK, CK`); the envelope by `lawPhi_envelope`, whose constants `K, c` do not
depend on the input density bound, fed with `LocBd Ds ν_j` from the envelope of `ν_j`.
`regLaw_of_envBd` turns the invariant into `RegLaw Ds θ' v b ν_j`.

The orbit is handled law by law, so WP1's `layer_law_orbit` is not needed here; it is what
identifies this orbit with the actual layers.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- **Orbit closure**: the layer-map orbit of a regular law stays in one regular class, for
all large `eps`, uniformly over the class. -/
theorem orbitClosure : OrbitClosure := by
  intro D θ vlo vhi hD hθ hvlo hv
  set b := regB vhi with hbdef
  set β := regBeta D θ vlo with hβdef
  set v := regV vlo with hvdef
  have hb : bAbs ≤ b := bAbs_le_regB vhi
  have hβ : βAbs ≤ β := βAbs_le_regBeta D θ vlo
  have hβ1 : 1 ≤ β := one_le_regBeta D θ vlo
  have hv0 : 0 < v := regV_pos hvlo
  have hvδ : v ≤ deltaVar / 2 := regV_le_half vlo
  have hvb : v ≤ b := regV_le_regB hv
  -- the exponential-moment constants of the whole orbit
  set θu := min (θ / 2) θK with hθudef
  set Bu := max (2 * D / θ) CK with hBudef
  have hθu : 0 < θu := lt_min (half_pos hθ) θK_pos
  have hBu : 0 < Bu := lt_of_lt_of_le CK_pos (le_max_right _ _)
  obtain ⟨e2, he2⟩ := lawPhi_expMom (b := b) (β := β) hv0 hθu hBu
  -- the envelope constants, independent of the input density bound
  obtain ⟨K, c, hK, hc, henv⟩ := lawPhi_envelope hv0 hvb hβ1 hθu hBu
  set Ds := max D K with hDsdef
  have hDs : 0 < Ds := lt_of_lt_of_le hD (le_max_left _ _)
  obtain ⟨e1, he1⟩ := henv Ds hDs
  set θ' := min θ c with hθ'def
  have hθ' : 0 < θ' := lt_min hθ hc
  refine ⟨Ds, θ', v, b, max (epsZero b β) (max e1 e2), hDs, hθ', hv0, hvb, ?_⟩
  intro eps heps ν hν
  have heps0 : epsZero b β ≤ eps := le_trans (le_max_left _ _) heps
  have heps1 : e1 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have heps2 : e2 ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  -- the orbit invariant
  have key : ∀ j, MomClass b β v ((lawPhi eps)^[j] ν) ∧ ExpMom θu Bu ((lawPhi eps)^[j] ν) ∧
      EnvBd Ds θ' (((lawPhi eps)^[j] ν : ProbabilityMeasure ℝ) : Measure ℝ) := by
    intro j
    induction j with
    | zero =>
      simp only [Function.iterate_zero_apply]
      have hM := hν.momClass hθ hvlo
      exact ⟨hM, (hν.expMom hθ).mono hM.pos hθu.le (min_le_left _ _) (le_max_left _ _),
        hν.envBd.mono hD.le (le_max_left _ _) (min_le_left _ _)⟩
    | succ j ih =>
      obtain ⟨hM, hE, hB⟩ := ih
      rw [Function.iterate_succ_apply']
      have hM' := lawPhi_momClass hb hβ hv0 hvδ heps0 hM
      exact ⟨hM',
        (he2 eps heps2 _ hM hE).mono hM'.pos hθu.le (min_le_right _ _) (le_max_right _ _),
        (he1 eps heps1 _ hM hE (hB.locBd hDs.le hθ'.le)).mono hK.le (le_max_right _ _)
          (min_le_right _ _)⟩
  intro j
  exact regLaw_of_envBd (key j).1 (key j).2.2 hDs.le

end

end PGM
