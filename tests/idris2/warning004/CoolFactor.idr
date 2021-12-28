module CoolFactor

export
interface HasCoolFactor x where
  cooool : x -> String

export
HasCoolFactor String where
  cooool x = "cool \{x}!"

