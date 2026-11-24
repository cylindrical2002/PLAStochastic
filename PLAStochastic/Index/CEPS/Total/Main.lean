import PLAStochastic.Index.CEPS.Total.MeanRaw
import PLAStochastic.Index.CEPS.Total.MeanReality
import PLAStochastic.Index.CEPS.Total.Taylor
import PLAStochastic.Index.CEPS.Total.Mid
import PLAStochastic.Index.CEPS.Total.DrawupClass
import PLAStochastic.Index.CEPS.Total.Discharge

import PLAStochastic.Index.CEPS.Total.KernelCoefficients
import PLAStochastic.Index.CEPS.Total.LowRaw

/-!
# WP10 (S-8, S-9): entry of `Index/CEPS/Total`

* S-8, the fixed-drift drawup: `drawup_close` (normal-side algebra (3.9) in `DrawupAlgebra`,
  class-uniform bounds in `DrawupBounds`, reflection of the bottom-started exits in
  `Reflection`, local form `drawup_close_of_exit_error` in `Drawup`, WP9 S-3 discharged).
* S-9, the assembly (C20): `cepsNormalClose : CepsNormalClose cepsNormalGn`, with the
  class-independent normal transform `cepsNormalGn` (`Level`), the assembly algebra
  (`Assembly`), (P12) on `[b, δ]` (`HalfLine`), the identification of the scaled normal
  expression with (3.11) (`Identify`), S-9 at one point (`Instance`), uniformly on a level
  (`LevelClose`), input classes in finitely many levels (`LevelClass`), WP9 S-6 discharged
  (`PairForm`, `SobolevSup`, `Discharge`).

See `research/2026-10-02-lean-ceps/track-WP10.md`.
-/
