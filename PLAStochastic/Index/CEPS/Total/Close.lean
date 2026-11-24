import PLAStochastic.Index.CEPS.Total.LevelClose
import PLAStochastic.Index.CEPS.Total.LevelClass

/-!
# WP10: S-9 in the form `CepsNormalClose`

Every input class `CepsInputClass D θ vlo vhi m η 1` (`m = cepsLevelOrder`) lies in the levels
`0, …, N` (`cepsInputClass_level`), so `cepsLevelIndex ν ≤ N`, and on each level S-9 holds
uniformly (`ceps_close_level`). Taking the worst constants over the finitely many levels gives
`CepsNormalClose cepsNormalGn` (`cepsNormalClose_of_pairClose`), from the S-6 pair error on each
level (`CepsPairCloseLevel`, premise until WP9 lands).
-/

noncomputable section
open Complex Set MeasureTheory

namespace PGM

/-- **S-9 (C20) in the form of `Glue/Defs.lean`.** -/
theorem cepsNormalClose_of_pairClose (hS6 : ∀ n, CepsPairCloseLevel n) :
    CepsNormalClose cepsNormalGn := by
  have hlev := fun n => ceps_close_level n (hS6 n)
  choose K c t₀ eps₀ p hK hc ht₀ he hbd using hlev
  refine ⟨cepsLevelOrder, fun D θ vlo vhi η hD hθ hvlo _hvv hη => ⟨1, one_pos, ?_⟩⟩
  -- the number of levels
  set X := max (max (max D θ⁻¹) (max vlo⁻¹ vhi))
    (max η⁻¹ (Real.exp η * (cepsSobolev cepsLevelOrder η cepsLambdaDensity + 1)))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
  have hXN : X ≤ cepsLevelScale N := hN.le
  have hrateN : ∀ a : ℝ, 0 < a → a⁻¹ ≤ X → cepsLevelRate N ≤ a := by
    intro a ha hax
    unfold cepsLevelRate
    have := hax.trans hXN
    unfold cepsLevelScale at this
    rw [inv_le_comm₀ (by positivity) ha]
    exact this
  have h1 : D ≤ cepsLevelScale N :=
    (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_left _ _)).trans hXN
  have h2 : cepsLevelRate N ≤ θ := hrateN θ hθ
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have h3 : cepsLevelRate N ≤ vlo := hrateN vlo hvlo
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have h4 : vhi ≤ cepsLevelScale N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hXN
  have h5 : cepsLevelRate N ≤ η := hrateN η hη
    ((le_max_left _ _).trans (le_max_right _ _))
  have h6 : Real.exp η * (cepsSobolev cepsLevelOrder η cepsLambdaDensity + 1) ≤
      cepsLevelScale N := ((le_max_right _ _).trans (le_max_right _ _)).trans hXN
  -- the worst constants over the levels `0, …, N`
  set S := Finset.range (N + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  set Kmax := ∑ n ∈ S, K n
  set cmin := S.inf' hS c
  set tmin := S.inf' hS t₀
  set emax := ∑ n ∈ S, eps₀ n
  set pmax := ∑ n ∈ S, p n
  have hcmin : 0 < cmin := (Finset.lt_inf'_iff hS).mpr fun n _ => hc n
  have htmin : 0 < tmin := (Finset.lt_inf'_iff hS).mpr fun n _ => ht₀ n
  refine ⟨Kmax, cmin, tmin, emax, hcmin, htmin, pmax, fun eps heps ν hν y hy => ?_⟩
  -- the level of `ν`
  have hlevN := cepsInputClass_level le_rfl hη h1 h2 h3 h4 h5 h6 hν
  obtain ⟨hlevn, hnN⟩ := cepsLevelIndex_spec hlevN
  set n := cepsLevelIndex ν
  have hnS : n ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)
  have hK_le : K n ≤ Kmax := Finset.single_le_sum (fun i _ => hK i) hnS
  have he_le : eps₀ n ≤ emax := Finset.single_le_sum (fun i _ => (zero_le_one.trans (he i))) hnS
  have hp_le : p n ≤ pmax := Finset.single_le_sum (fun i _ => Nat.zero_le _) hnS
  have hc_le : cmin ≤ c n := Finset.inf'_le _ hnS
  have ht_le : tmin ≤ t₀ n := Finset.inf'_le _ hnS
  have heps1 : 1 ≤ eps := (he n).trans (he_le.trans heps)
  have hmain := hbd n eps (he_le.trans heps) ν hlevn y (hy.trans ht_le)
  have hG : cepsNormalGn eps ν (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) =
      cepsScaledTrueNormalExpression (cepsLevelDomain n) ((ν : Measure ℝ).map fun x => 1 - x)
        (2 * eps)⁻¹ (cepsLevelCutoff n) (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) := rfl
  rw [hG]
  refine hmain.trans ?_
  have hpow : eps ^ p n ≤ eps ^ pmax := pow_le_pow_right₀ heps1 hp_le
  have hexp : Real.exp (-c n * eps) ≤ Real.exp (-cmin * eps) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hKn := hK n
  calc K n * eps ^ p n * Real.exp (-c n * eps) ≤ Kmax * eps ^ pmax * Real.exp (-cmin * eps) := by
        have hKm : 0 ≤ Kmax := Finset.sum_nonneg fun i _ => hK i
        gcongr

end PGM
