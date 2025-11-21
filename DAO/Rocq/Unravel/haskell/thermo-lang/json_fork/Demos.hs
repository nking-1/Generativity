module Demos where

demoPhysics :: String
demoPhysics = unlines
  [ "let gravity = 10 in"
  , "let trajectory = [5, 4, 3, 2, 1, 0, 1, 2] in"
  , "let forces = map(r -> "
  , "    shield (gravity / r) recover 100"
  , ", trajectory) in"
  , "fold(acc, f -> acc + f, 0, forces)"
  ]

demoFinance :: String
demoFinance = unlines
  [ "let metrics = map(row -> "
  , "    1000 / row"
  , ", [5, 0, 100, 3]) in" 
  , "fold(acc, m -> acc + m, 0, metrics)"
  ]

demoConsensus :: String
demoConsensus = unlines
  [ "let pathA = 10 / 0 in"
  , "let pathB = shield (10 / 0) recover 0 in"
  , "if 1 == 1 then pathB else pathA" 
  ]