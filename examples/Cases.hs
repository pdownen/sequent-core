{-# OPTIONS_GHC -O0 -dcore-lint #-}

{-# NOINLINE frob #-}
frob b = case case b of { True -> False; False -> True }
                     of { True -> False; False -> True }

main = print $ frob True
