{-# LANGUAGE GADTs, RankNTypes #-}

data E a b where
  E :: forall a b. (b ~ a, Ord a) => b -> E a [a]

test :: E Int b -> Int
test x = _
