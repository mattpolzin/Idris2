module OnlyFixity

-- Test that even a module that only declares a fixity
-- is determined to be used if a relevant operator is
-- used in the importing module.

infix 2 .-=
