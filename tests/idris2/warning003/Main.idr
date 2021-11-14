module Main

-- Foo is left unused
import Foo
-- The rest are used
import Bar
import Namespaced
import Inlined
import Third

%logging "import.used" 2

useBar : String
useBar = Bar.dep1

useNamesapced : String
useNamesapced = namespaced "hi"

useInlined : String
useInlined = inlined

useThird : Third
useThird = "three"

