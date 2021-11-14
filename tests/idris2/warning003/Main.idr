module Main

-- Foo is left unused
import Foo
-- Bar, Namespaced, and Inlined are used
import Bar
import Namespaced
import Inlined

%logging "import.used" 2

useBar : String
useBar = Bar.dep1

useNamesapced : String
useNamesapced = namespaced "hi"

inlined : String
inlined = Inlined.inlined

