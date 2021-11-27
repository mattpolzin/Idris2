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

