{-# OPTIONS_GHC -dcore-lint #-}
module Cases where

frob :: Bool -> Bool
frob b = case case b of { True -> False; False -> True }
                     of { True -> False; False -> True }

main :: IO ()
main = print $ frob (frob True)

-- The built-in case-of-case transform will pull the outer case into the
-- branches of the inner case, which does little good. We instead pull it into
-- the definition of j and then all the way into the branches of the if.
caseOfJoinedCases :: Bool -> Int
caseOfJoinedCases b
  = case let {-# NOINLINE j #-}
             j :: Int -> Int
             j x = if even x then 1 else x
         in case b of True  -> j 1
                      False -> j 2 of 1 -> 2
                                      _ -> 3
