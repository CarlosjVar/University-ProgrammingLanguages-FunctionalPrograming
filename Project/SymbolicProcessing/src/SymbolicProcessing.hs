

import Data.Bool
import Numeric (showHex, showIntAtBase)
import Data.Char (intToDigit)
import Data.List (sort,map)


-- Data Types

data Proposition =  Constant    Bool
                |   Variable    String
                |   Negation    Proposition
                |   Conjunction Proposition Proposition
                |   Disjunction Proposition Proposition
                |   Implication Proposition Proposition
                |   Equivalence Proposition Proposition
                deriving Show

data TautologyEvaluation =  ItIs
                        |   ItsNot  [(String, Bool)]    -- This would contain one assignment that makes the proposition fail the evaluation.

{-
PROPOSITION EXAMPLE
( Negation ( Conjunction ( Disjunction ( Implication ( Negation ( Variable "a" ) ) ( Variable "b" ) ) ( Constant False ) ) (Equivalence ( Variable "a" ) ( Variable "c" ) ) ) )

( Implication (Conjunction (Variable "p")(Variable "q")) (Variable "p")))

VARIABLES
["a","b","c"]

POSSIBLES VALUES EXAMPLE
[False,True,True]

ASSIGNMENTS EXAMPLE
[("a",False),("b",True),("c",True)]

-}

{-
PRINTERS
-}

printProposition :: Proposition -> String
printProposition    prop        =
    case prop of
        (Constant    False)        -> "False"
        (Constant    True)         -> "True"
        (Variable    name)         -> name
        (Negation    prop1)        -> "negacion (" ++ printProposition  prop1 ++ ")"
        (Conjunction prop1 prop2)  -> "conjuncion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        (Disjunction prop1 prop2)  -> "disyuncion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        (Implication prop1 prop2)  -> "implicacion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        (Equivalence prop1 prop2)  -> "equivalencia (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"

printAssignment ::  [(String, Bool)] ->  String
printAssignment     []               =   ""
printAssignment     ((v,b):vbs)      =   "(" ++ v ++ ","++ (if b then "true" else "false") ++ ") " ++ printAssignment  vbs


{-
    AUXILIAR
-}

-- Removes duplicate elements from a list
-- Recovered from https://stackoverflow.com/questions/16108714/removing-duplicates-from-a-list-in-haskell-without-elem
removeDuplicates = 
    foldl (\seen x  ->  if x `elem` seen
                        then seen
                        else seen ++ [x]) []

-- Concatenates a given boolean value into a given boolean array.
concatBools :: Bool -> [Bool] -> [Bool]
concatBools    x       xs      = (x:xs)


-- With a given variable name searchs its assigned boolean value in a [(String,Bool)]. Throws error if doesn't exist.
getAssignment :: String -> [(String, Bool)] -> Bool
getAssignment string ((varName,value):rest) = 
    if string == varName
    then value
    else getAssignment string rest
getAssignment string [] = error "El nombre no se encuentra entre la lista de variables."

{-
    VARS
    Applies obtains all the different variables contained in a proposition.
    
    Auxiliar functions: 
        - removeDuplicates
-}

vars :: Proposition ->  [String]
vars    proposition =   
    let
        extract ::  Proposition -> [String]
        extract     proposition = 
            case proposition of
            (Constant _) ->  
                []
            (Variable string) ->   
                [string]
            (Negation proposition) -> 
                extract proposition
            (Conjunction proposition1 proposition2) ->  
                let 
                    variables1 = extract proposition1
                    variables2 = extract proposition2
                in 
                    concat [variables1, variables2]
            (Disjunction proposition1 proposition2) -> 
                let 
                    variables1 = extract proposition1
                    variables2 = extract proposition2
                in 
                    concat [variables1, variables2]
            (Implication proposition1 proposition2) -> 
                let 
                    variables1 = extract proposition1
                    variables2 = extract proposition2
                in 
                    concat [variables1, variables2]
            (Equivalence proposition1 proposition2) -> 
                let 
                    variables1 = extract proposition1
                    variables2 = extract proposition2
                in 
                    concat [variables1, variables2]

    in
        removeDuplicates (extract proposition)

{-
    GEN_BOOLS
    Calculates all possible boolean values combination in a given list of strings.
    
    Auxiliar functions: 
        - vars
-}

gen_bools ::    Proposition -> [[Bool]]
gen_bools       proposition = 
    let
        variablesQuantity = length (  vars proposition )

        getCombinations ::  Int ->  [[Bool]]
        getCombinations     0   =   [[]]
        getCombinations     n   =   concat [ map (concatBools True) (getCombinations (n-1)) , map (concatBools False) (getCombinations (n-1))]        
    in 
        getCombinations variablesQuantity

{-
    AS_VALS
    Combines a variables list with a boolean list in a tuple typle list. They have to be the same length.
    
    Auxiliar functions: (none)
-}

as_vals ::  [String] ->         [Bool]                  -> [(String, Bool)]
as_vals     []                  []                       = []
as_vals     (firstVar:restVars) (firstBool:restBools)    = concat  [ [(firstVar,firstBool)], as_vals restVars restBools ]
as_vals     _                   _                        = error "Los arreglos tienen diferente largo."



{-
    EVALPROP
    Evaluates a proposition with a given value assignment.
    
    Auxiliar functions: 
        - getAssignment
-}

evalProp :: Proposition ->  [(String, Bool)]    -> Bool
evalProp    proposition     assignment          =
    case proposition of
    (Constant value) ->  
        value
    (Variable string) ->   
        getAssignment string assignment
    (Negation proposition) -> 
        not ( evalProp proposition assignment )
    (Conjunction proposition1 proposition2) ->  
        let 
            value1 = evalProp proposition1 assignment
            value2 = evalProp proposition2 assignment
        in 
            value1 && value2
    (Disjunction proposition1 proposition2) -> 
        let 
            value1 = evalProp proposition1 assignment
            value2 = evalProp proposition2 assignment
        in 
            value1 || value2
    (Implication proposition1 proposition2) -> 
        let 
            value1 = evalProp proposition1 assignment
            value2 = evalProp proposition2 assignment
        in 
            case (value1, value2) of
                (True, False)   -> False
                _               -> True  
    (Equivalence proposition1 proposition2) -> 
        let 
            value1 = evalProp proposition1 assignment
            value2 = evalProp proposition2 assignment
        in 
            value1 == value2

{-
    TAUT
    Evaluates if a proposition is a tautology.
        
    Auxiliar functions: 
        - as_vals
        - evalProp
        - bonita
        - printAssignment
-}

-- 
taut :: Proposition -> String
taut    proposition =
    let
        variables       =   vars proposition
        possibleValues  =   gen_bools proposition
        
        isTaut ::   [[Bool]]                        -> TautologyEvaluation
        isTaut      []                              = ItIs
        isTaut      (boolCombination:restBoolCombs) = 
            let
                assignment  =   as_vals variables boolCombination
                evaluation  =   evalProp proposition assignment
            in
                case evaluation of
                    (True)  -> isTaut restBoolCombs
                    (False) -> ItsNot assignment
    in
        case isTaut possibleValues of
            (ItIs)              -> bonita proposition ++ ": es una tautologia :)"
            (ItsNot assignment) -> bonita proposition ++ ": no es una tautologia :( Culpa de: ["++ printAssignment assignment++"].. como minimo."

{-
-- Finds the disjunctive normal form of a given proposition
fnd :: Proposition -> Proposition
-}

{-
    BONITA
    Prints a proposition in a pretty and understandable way, removing all the unnecesary parenthesis on the way.
    
    Auxiliar functions: 
        - removeDuplicates
-}

bonita ::   Proposition -> String
bonita      proposition =
    case proposition of
    (Constant True) ->  
        "True"
    (Constant False) ->
        "False"
    (Variable string) ->   
        string
    (Negation proposition) -> 
        let
            string = bonita proposition
        in
            "~"++string++""
    (Conjunction proposition1 proposition2) ->  
        let 
            string1 = bonita proposition1
            string2 = bonita proposition2
        in 
            "("++string1++" /\\ "++string2++")"
    (Disjunction proposition1 proposition2) -> 
        let 
            string1 = bonita proposition1
            string2 = bonita proposition2
        in 
            "("++string1++" \\/ "++string2++")"
    (Implication proposition1 proposition2) -> 
        let 
            string1 = bonita proposition1
            string2 = bonita proposition2
        in 
            "("++string1++" => "++string2++")"
    (Equivalence proposition1 proposition2) -> 
        let 
            string1 = bonita proposition1
            string2 = bonita proposition2
        in 
            "("++string1++" <=> "++string2++")"

    let
        binary = showIntAtBase 2 intToDigit n ""
    in
        concat [[binary], func (n-1)]