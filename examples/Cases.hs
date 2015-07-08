{-# OPTIONS_GHC -O0 -dcore-lint #-}

frob b = case case b of { True -> False; False -> True }
                     of { True -> False; False -> True }

main = print $ frob (frob True)
