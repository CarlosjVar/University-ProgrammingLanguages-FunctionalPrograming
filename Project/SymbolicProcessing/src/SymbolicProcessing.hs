

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
( Implication (Conjunction (Variable "p")(Variable "q")) (Variable "p"))


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

-- Returns the precedence of a given proposition operation. If doesn't have one assigned, returns precedence 0.
getPrecedence :: Proposition -> Int
getPrecedence    proposition =
    case proposition of
        (Conjunction prop1 prop2) -> 7
        (Disjunction prop1 prop2) -> 6
        (Implication prop1 prop2) -> 5
        (Equivalence prop1 prop2) -> 4
        _                         -> 0 -- Just to handle the exception, precedence value as 0 is never actually used.


-- Returns the pretty string of an operation, with a given operator to write, and a function to call the next iteration with.
getPrettyString ::    Proposition ->  Proposition ->  Proposition -> String     -> (Proposition -> String) -> String
getPrettyString       proposition     subprop1        subprop2       operator      func                     =
    let 
        prop1Precedence = getPrecedence subprop1
        prop2Precedence = getPrecedence subprop2

        string1 = 
            (
                if prop1Precedence > getPrecedence proposition
                then "("++func subprop1++")"
                else func subprop1
                )
        
        string2 = 
            (
                if prop2Precedence > getPrecedence proposition
                then "("++func subprop2++")"
                else func subprop2
                )
    in 
        string1++operator++string2

-- Determines if a proposition is a variable.
isVariable :: Proposition -> Bool
isVariable    (Variable _) = True
isVariable    _            = False

-- Determines if a proposition is a constant.
isConstant :: Proposition -> Bool
isConstant    (Constant _) = True
isConstant    _            = False

-- Negates a proposition until reaching a doble negation, variable or constant.
exhaustiveNegate :: Proposition -> Proposition
exhaustiveNegate    proposition  =
    case proposition of 
        (Conjunction prop1 prop2)   ->  Disjunction (exhaustiveNegate prop1) (exhaustiveNegate prop2)
        (Disjunction prop1 prop2)   ->  Conjunction (exhaustiveNegate prop1) (exhaustiveNegate prop2)
        (Implication prop1 prop2)   ->  Disjunction (exhaustiveNegate (Negation prop1)) (exhaustiveNegate prop2)
        (Equivalence prop1 prop2)   ->  Disjunction (Conjunction (exhaustiveNegate prop1) (exhaustiveNegate prop2) ) (Negation (exhaustiveNegate prop2))
        (Negation prop)             ->  prop
        (Variable string)           ->  Negation (Variable string)
        (Constant True)             ->  (Constant False)  
        (Constant False)            ->  (Constant True) 

-- Either removes the constants of a proposition, or colapses the proposition into the boolean value it is dominated to. (applies Neutral and Domination boolean rules).
removeConstants ::  Proposition -> Proposition
removeConstants     proposition =   
    let
        withoutNeutrals = removeNeutrals proposition
    in  
        if hasConstants withoutNeutrals
        then Constant (findDomination proposition (vars proposition) (gen_bools proposition))
        else withoutNeutrals

-- Removes the neutral constants contained in a proposition.
removeNeutrals ::   Proposition                                 ->  Proposition
removeNeutrals      (Conjunction proposition (Constant True))   =   removeNeutrals proposition
removeNeutrals      (Disjunction proposition (Constant False))  =   removeNeutrals proposition
removeNeutrals      (Conjunction (Constant True) proposition )  =   removeNeutrals proposition
removeNeutrals      (Disjunction (Constant False) proposition ) =   removeNeutrals proposition

removeNeutrals      (Conjunction proposition1 proposition2 )    =   (Conjunction (removeNeutrals proposition1) (removeNeutrals proposition2) )
removeNeutrals      (Disjunction proposition1 proposition2 )    =   (Disjunction (removeNeutrals proposition1) (removeNeutrals proposition2) )
removeNeutrals      (Negation proposition)                      =   (Negation (removeNeutrals proposition))

removeNeutrals      (Constant bool)                             =   (Constant bool)
removeNeutrals      (Variable string)                           =   (Variable string)

-- Colapses a proposition into its domination boolean value.
findDomination ::   Proposition ->  [String] -> [[Bool]]                        ->  Bool
findDomination      proposition     variables   []                              =   True
findDomination      proposition     variables   (boolCombination:restBoolCombs) = 
    let
        assignment  =   as_vals variables boolCombination
        evaluation  =   evalProp proposition assignment
    in
        case evaluation of
            (True)  -> findDomination proposition variables restBoolCombs
            (False) -> False

hasConstants :: Proposition                 -> Bool
hasConstants    (Constant _)                 = True
hasConstants    (Variable _)                 = False
hasConstants    (Disjunction prop1 prop2)    = False || hasConstants prop1 || hasConstants prop2
hasConstants    (Conjunction prop1 prop2)    = False || hasConstants prop1 || hasConstants prop2
hasConstants    (Equivalence prop1 prop2)    = False || hasConstants prop1 || hasConstants prop2
hasConstants    (Implication prop1 prop2)    = False || hasConstants prop1 || hasConstants prop2
hasConstants    (Negation prop)              = False || hasConstants prop

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
        - isTaut
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
            (ItsNot assignment) -> bonita proposition ++ ": no es una tautologia :( Culpa de: ["++printAssignment assignment++"].. como minimo."

{-

    FND
    Finds the disjunctive normal form of a given proposition

    Auxiliar functions:
        - exhaustiveNegate
        - removeConstants

-}

fnd ::  Proposition ->   Proposition
fnd     proposition =
    let
        clean ::  Proposition                   -> Proposition
        clean     (Implication prop1 prop2)     =   (Disjunction (clean (Negation  prop1)) (clean prop2))
        clean     (Equivalence prop1 prop2)     =   (Disjunction (Conjunction (clean prop1) (clean prop2) ) (clean (Negation prop2)))
        clean     (Conjunction prop1 prop2)     =   (Conjunction (clean prop1) (clean prop2))
        clean     (Disjunction prop1 prop2)     =   (Disjunction (clean prop1) (clean prop2) )
        clean     (Constant bool)               =   (Constant bool)
        clean     (Variable string)             =   (Variable string)
        clean     (Negation prop)               =   (
                                                    if isVariable prop 
                                                    then (Negation prop) 
                                                    else clean (exhaustiveNegate prop)
                                                    )
    in
        removeConstants (clean proposition)


    
                      

{-
    BONITA
    Prints a proposition in a pretty and understandable way, removing all the unnecesary parenthesis on the way.
    
    Auxiliar functions: 
        - getPrettyString
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
            (
                case proposition of
                (Constant True)     -> "False"
                (Constant False)    -> "True"
                (Variable string)   -> "~"++string
                (_)                 -> "~("++string++")"
            )
            
    (Conjunction proposition1 proposition2) ->  
        getPrettyString proposition proposition1 proposition2 " /\\ " bonita

    (Disjunction proposition1 proposition2) -> 
        getPrettyString proposition proposition1 proposition2 " \\/ " bonita

    (Implication proposition1 proposition2) -> 
        getPrettyString proposition proposition1 proposition2 " => " bonita

    (Equivalence proposition1 proposition2) -> 
        getPrettyString proposition proposition1 proposition2 " <=> " bonita