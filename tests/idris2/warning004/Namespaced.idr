module Namespaced

namespace Fooer
  export
  namespaced : String -> String
  namespaced x = x ++ "!"
