/-
  Kopt: A from-scratch formalization of

    Bian & Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis of
    Two-Qubit Clifford+CS Operators."

  Sections of the paper map to files in this library:

    Section 2 (Algebra)              → Kopt.Algebra
    Section 3 (Special unitaries)    → Kopt.SpecialUnitaries
    Section 4 (Synthesis algorithm)  → Kopt.Synthesis,  Kopt.Lde
    Section 5 (Optimality, CS bounds)→ Kopt.Optimality, Kopt.Synth
-/
import Kopt.Algebra
import Kopt.SpecialUnitaries
import Kopt.Cliffords
import Kopt.Synthesis
import Kopt.Lde
import Kopt.Synth
import Kopt.Optimality
