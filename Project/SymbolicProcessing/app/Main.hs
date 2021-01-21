module Main where

import Lib

main :: IO ()
main = someFunc

--TUTORIAL
{-

Block comment

-}

-- native types
{-

Int
Integer
Float
Double
Bool --> True False
Char '
Tuple

-}

{-
permanent variables

always5 :: Int
always5 = 5

-}

{-
-- mod is a prefix operator
modEx = mod 5 4
 
-- With back ticks we can use it as an infix operator
modEx2 = 5 `mod` 4

-- Negative numbers must be surrounded with parentheses
negNumEx = 5 + (-4)
-}

{-
trueAndFalse = True && False
trueOrFalse = True || False
notTrue = not(True)
-}