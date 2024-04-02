module LotsOfArgs

contrived : Int -> Int -> Int -> Int
         -> Int -> Int -> Int -> Int
         -> Int -> Int -> Int -> Int
         -> Int -> Int -> Int -> Int
         -> Int -> Int -> Int -> Int
contrived a b c d e f g h i j k l m n o p q r s =
  a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s


main : IO ()
main = printLn $
  contrived 0 0 1 0
            0 1 0 0
            1 0 0 0
            0 1 0 0
            0 0 1
