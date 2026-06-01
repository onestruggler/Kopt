/-
  Kopt2: A from-scratch formalization of

    Bian & Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis of
    Two-Qubit Clifford+CS Operators."

  Sections of the paper map to files in this library:

    Section 2 (Algebra)              → Kopt2.Algebra
    Section 3 (Special unitaries)    → Kopt2.SpecialUnitaries
    Section 4 (Synthesis algorithm)  → Kopt2.Synthesis,  Kopt2.Lde
    Section 5 (Optimality, CS bounds)→ Kopt2.Optimality, Kopt2.Synth
-/
import Kopt2.Algebra
import Kopt2.SpecialUnitaries
import Kopt2.Cliffords
import Kopt2.Synthesis
import Kopt2.Lde
import Kopt2.Synth
import Kopt2.Optimality
