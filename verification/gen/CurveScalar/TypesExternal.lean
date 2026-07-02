-- Hand-written external types for the Scalar52 arithmetic extraction.
-- This fork's function-level scalar extraction pulls in NO external types
-- (unlike the v5 dalek template, whose sub/conditional_select route through
-- subtle::Choice). Kept as a (decl-free) module so the check manifest is
-- uniform across forks.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
