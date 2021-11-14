module Foo

export
dep1 : String
dep1 = "hello"

export
dep2 : String
dep2 = "world"

namespace Fooer
  export
  dep3 : String -> String
  dep3 x = x ++ "!"

