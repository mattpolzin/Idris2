module Main

-- Foo is left unused
import Foo
-- The rest are used
import Foo2
import Bar
import Namespaced
import Inlined
import Third
import Proxy
import CoolFactor
import UseCoolFactor
import TestType
import ReturnsTestType
import Record
import UsedByRecord
import OnlyFixity

useBar : String
useBar = Bar.dep1

useNamesapced : String
useNamesapced = namespaced "hi"

useInlined : String
useInlined = inlined

useThird : Third
useThird = "three"

usePubliclyExported : String
usePubliclyExported = indirectly

useProxy : String
useProxy = twiceRemoved

-- specifically, don't use the interface's method, only
-- use the interface in so far as Idris needs to create a
-- witness via search.
useViaSearch : String
useViaSearch = cool "beans"

-- Use test type by way of calling `ReturnsTestType.retType`
-- but not by directly using `TestType.TestType`.
useTestType : ()
useTestType = let x = retType
              in  ()

-- Test the case where the record needs `ThisThing` defined even though
-- this function does not use it (creates Nothing instead of Just a ThisThing).
-- Linearity checking is where the def ends up being required.
useRecord : UsualSuspect
useRecord = MkUsual {
  storage = Nothing
}

-- define an operator for which a fixity is defined in a different module
(.-=) : String -> String -> ()
(.-=) _ _ = ()
-- and use that operator (or else the module in question is not actually
-- a needed import).
useOpeartor : ()
useOpeartor = "hello" .-= "world"

