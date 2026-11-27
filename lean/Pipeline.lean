-- Root module of the standalone Lean project for this result.
-- It imports only the Ozawa files. Pipeline/Ozawa/Main.lean imports Rational, Scalar, Spectral
-- and Witness, and ends with the `#print axioms` lines that scripts/lean_check.sh checks.
-- The files under Pipeline/Ozawa/ are byte-identical copies of the files that passed
-- `scripts/lean_check.sh Ozawa` in the original (private) pipeline repository on 2026-11-27.
import Pipeline.Ozawa.Main
