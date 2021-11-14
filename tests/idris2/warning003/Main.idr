module Main

-- Foo is left unused
import Foo
-- The rest are used
import Bar
import Namespaced
import Inlined
import Third

useBar : String
useBar = Bar.dep1

useNamesapced : String
useNamesapced = namespaced "hi"

useInlined : String
useInlined = inlined

useThird : Third
useThird = "three"

