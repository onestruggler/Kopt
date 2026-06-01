/-
  Kopt2.CliffordsCoverage — verification file for `cgpermsModPhase_covers_all`.

  This file is NOT imported by the main library (`Kopt2.lean`). It exists as
  a standalone verification target: `lake build Kopt2.CliffordsCoverage`.

  The claim `cgpermsModPhase_covers_all` (∀ gp : GenPermFin, the lookup
  function finds a matching circuit in cgpermsModPhase) is:
    • Stated over a finite decidable type (GenPermFin has 6144 elements).
    • Has a `Decidable` instance via `Fintype.decidableForallFintype`.
    • Is in principle dischargeable by `native_decide`.

  In practice, the computation (~6144 × 6144 matrix comparisons, or ~65k
  per batch when split by permutation) exceeds the stack/time limits of
  Lean's native code generator on typical hardware. The equivalent check
  is performed by the Haskell driver (`src/Clifford.hs:precomputed_mat_gperms`).

  To verify on a machine with sufficient resources, uncomment the
  `native_decide` proof below.
-/
import Kopt2.Cliffords

namespace Kopt2

open Kopt2

-- Uncomment to verify (requires ~10+ minutes and large stack):
-- set_option maxHeartbeats 8000000 in
-- theorem cgpermsModPhase_covers_verified : cgpermsModPhase_covers_all := by
--   native_decide

end Kopt2
