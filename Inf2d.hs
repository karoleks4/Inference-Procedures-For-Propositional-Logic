-- Inf2D Assignment 1

-- Good Scholarly Practice
-- Please remember the University requirement as regards all assessed work for credit. 
-- Details about this can be found at:
-- http://www.ed.ac.uk/academic-services/students/undergraduate/discipline/academic-misconduct
-- and at:
-- http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct
-- Furthermore, you are required to take reasonable measures to protect your assessed work from 
-- unauthorised access.For example, if you put any such work on a public repository then you must 
-- set access permissions appropriately (generally permitting access only to yourself, or your 
-- group in the case of group practicals).

module Inf2d where
import Data.List
import Debug.Trace
import Data.Ord
import Data.Maybe
-- Type synonyms for the data structures
-- Symbols are integers (negative integers represent negated symbols)
type Symbol = String  
-- Clause = a disjuntion of symbols
type Clause = [Symbol] 
-- Sentence = Statements. This is a list of a list of symbols
type Sentence = [[Symbol]] 
-- Models are represented as a list of (Symbol,Boolean) tuples
type Model = [(Symbol, Bool)]
-- The knowledge base is represented as a list of statements
type KB = [Sentence]


-----------------------------------------------
-- STUDENT MATRICULATION NUMBER:
-----------------------------------------------
studentId::String
studentId = "s1448320"

--------------------------------------------------
-- ASSIGNMENT TASKS
-- Refer to assignment sheet for details of tasks
--------------------------------------------------

----------TASK 1: REPRESENTATION (2 marks)----------------------------------------------------------
wumpusFact::Sentence
wumpusFact = [["-B11","P11","P22","P31"],["B11","-P11"],["B11","-P22"], ["B11","-P31"]]

----------TASK 2: GENERAL HELPER FUNCTIONS (10 marks)-----------------------------------------------

-- Finds the assigned literal to a symbol from a given model

-- Variable c indicates the number of negations ('-' signs) of the symbol.
-- If c is an even number, it means that the symbol is not negated.
-- If c is an odd number, it means that the symbol is negated and we have to change its Bool value.
-- This function considers the cases when more than 1 negation sign can occur next to the symbol.

lookupAssignment :: Symbol -> Model -> Maybe Bool
lookupAssignment symbol model
	| even c && elem (drop c symbol, True) model 	= Just True
	| even c && elem (drop c symbol, False) model 	= Just False
	| odd c && elem (drop c symbol, True) model 	= Just False
	| odd c && elem (drop c symbol, False) model 	= Just True
	| otherwise 									= Nothing
		where c = length $ filter (== '-') symbol

-- Negate a symbol

-- Variable c indicates the number of negations ('-' signs) of the symbol.
-- If c is equal to zero (the symbol does not have any negation sign next to it) the function just adds a negation sign to it.
-- If c is even, simply drop all negation sign except one in order ro negate the symbol.
-- If c is odd, cut all negation signs in order to make it negated.
-- This function considers the cases when more than 1 negation sign can occur next to the symbol.

negateSymbol :: Symbol -> Symbol
negateSymbol symbol
	| c == 0			= "-" ++ symbol 
	| even c == True 	= drop (c-1)  symbol
	| otherwise 		= drop c symbol
		where c = length $ filter (== '-') symbol 

-- For a given symbol, this function checks if it is negated(i.e., has a negation sign).
isNegated :: Symbol -> Bool
isNegated symbol
	| elem '-' (negateSymbol symbol) == True 	= False
	| otherwise 								= True

-- This function takes a symbol and returns an Symbol without any negation sign if the original 
-- symbol had one.

-- Variable c indicates the number of negations ('-' signs) of the symbol.

getUnsignedSymbol :: Symbol -> Symbol
getUnsignedSymbol symbol = drop c symbol
	where c = length $ filter (== '-') symbol

-- Gets a list of all symbols in for all given sentences.
getSymbols :: [Sentence] -> [Symbol]
getSymbols [] = []
getSymbols (s:stmts) = nub ((map getUnsignedSymbol (concat s)) `union` getSymbols stmts)


----------TASK 3: TRUTH TABLE ENUMERATION AND ENTAILMENT (40 marks)---------------------------------


-- Function takes as input a list of symbols, and returns a list of models (all possible assignment 
-- of True or False to the symbols.)
generateModels :: [Symbol] -> [Model]
generateModels symbols = sequence[[(s,True),(s,False)] | s <- nub symbols]

-- This function evaluates the truth value of a propositional sentence using the symbols 
-- assignments in the model.

-- In this function we are considering a list of Maybe Bool values of all symbols present in the given sentence.
-- If the list contains at least on "Nothing" value, then an error occur.
-- Otherwise, we are performing calculations on Bool values. First we join them (Bool values of the symbols in a clause) by "or" function
-- then all the Bool values of the clauses are joint with "and" function in order to get the Bool value of the sentence in the given model.

pLogicEvaluate :: Sentence -> Model -> Bool
pLogicEvaluate stmt model 
	| any (== Nothing) [lookupAssignment s model | sen <- stmt, s <- sen] == True = error "Symbol not in model!"
	| otherwise = and [or [fromJust (lookupAssignment s model) | s <- sen] | sen <- stmt]

-- This function checks the truth value of list of a propositional sentence using the symbols 
-- assignments in the model. It returns true only when all sentences in the list are true.

-- We are simply using previous function and list of comprehension.

plTrue :: [Sentence]-> Model -> Bool 
plTrue sentences model = and [pLogicEvaluate s model | s <- sentences]


----------ttCheckAll function:


-- This helper function compares two lists. If both lists contain the same values it returns True.
-- We couldn't use "==" function since for this one the order of the elements in both lists matter (e.g. [1,2] == [2,1] returns False)

compareLists :: (Eq a) => [a] -> [a] -> Bool
compareLists xs ys = null (xs \\ ys) && null (ys \\ xs)

-- This function takes as input a knowledgebase (i.e. a list of propositional sentences), 
-- a query (i.e. a propositional sentence), and a list of symbols.
-- IT recursively enumerates the models of the domain using its symbols to check if there 
-- is a model that satisfies the knowledge base and the query. It returns a list of all such models. 

-- This function simply checks if two lists of models (model1 and model2) contin the same elements.
-- If they do that means that the same list of models satisfy knowledge base and the query therefore the knowledge base entails the query.
-- Models1 represents a list of models generated by the function generateModels for which satisfy the knowledge base.
-- Models2 represents a list of models from the list Models1 which satisfy the query.

ttCheckAll :: [Sentence] -> Sentence -> [Symbol] -> [Model]
ttCheckAll kb query symbols
	| compareLists models1 models2 == True	=  models2
	| otherwise 			= []
		where {models1 = [x | x <- generateModels symbols, plTrue kb x == True];
				models2 = [xs | xs <- models1, pLogicEvaluate query xs == True]}

-- This function determines if a model satisfes both the knowledge base and the query, returning
-- true or false.

-- This function simply uses ttCheckAll function but in order to implement it we need a lisst of symbols which occur in the knowledge base and the query.
-- This list is generated by using previous functions and is represented by variable symbols.

ttEntails :: [Sentence] -> Sentence -> Bool
ttEntails kb query
	| ttCheckAll kb query symbols == [] = False
	| otherwise 						= True
		where symbols = nub (getSymbols kb ++ (concat query))


-- This function determines if a model satisfes both the knowledge base and the query. 
-- It returns a list of all models for which the knowledge base entails the query.

-- This function is almost the same as the previous onebut it returns a list of models which satisfy both knwledge base and the query (when query is entailed by knowledge base).
-- This function uses variable symbols the same as in ttEntails.

ttEntailsModels :: [Sentence] -> Sentence -> [Model]
ttEntailsModels kb query = ttCheckAll kb query symbols
	where symbols = nub (getSymbols kb ++ (concat query))

----------TASK 4: DPLL (43 marks)-------------------------------------------------------------------

-- The early termination function checks if a sentence is true or false even with a 
-- partially completed model.

-- Variable sen (Bool value) takes a list of Bool values of all symbols in a clause form the input sentence and checkes if 
-- there is any "Just True" which means that there is a symbol (or symbols) in the clause which is true and that makes the whole clause true.

earlyTerminate :: Sentence -> Model -> Bool
earlyTerminate [] model = True
earlyTerminate (a:sentence) model 
	| sen == False = False  -- If one of the clauses in the sentence is false it makes the whole sentence false (because it is conjunction of disjunctions)
	| otherwise = earlyTerminate sentence model
		where sen = any (== Just True) [lookupAssignment s model | s <- a]  


----------FindPureSymbol function:


-- This helper function checks if a clause contains any symbols with Bool value of True.
-- If a clause does contain such symbol (or symbols), it is ignored (the function returns Nothing). Otherwise the clause is returned.
-- This helper function is needed to create a new list of clauses which do not contain any symbols which are assigned to True (list that ignores clauses which are already true).
-- The variable a is a list of Maybe Bool values of all symbols from the clause.

helpf :: Clause -> Model -> Maybe Clause
helpf clause model
	| any (== Just True) a == True = Nothing
	| otherwise = Just clause
		where a = [lookupAssignment c model | c <- clause]

-- This helper function helps with determining if the symbol is pure. It returnes a list of Bool values which determine 
-- the appearance of the symbol in the given list of clauses. It searches each clause for the symbol. 
-- If the clause does not contain the symbol the function ignores it and goes to another one. 
-- If the clause contains the symbol it adds True to the list.
-- If the clause contains the symbol but in negated form it adds False to the list.

alt :: Symbol -> [Clause] -> Model -> [Bool]
alt symbol [] model = []
alt symbol (c:clauses) model 
	| helpf c model == Nothing = alt symbol clauses model
	| elem symbol c == True = True : alt symbol clauses model
	| elem (negateSymbol symbol) c == True = False : alt symbol clauses model
	| otherwise = alt symbol clauses model

-- This function finds pure symbol, i.e, a symbol that always appears with the same "sign" in all 
-- clauses.
-- It takes a list of symbols, a list of clauses and a model as inputs. 
-- It returns Just a tuple of a symbol and the truth value to assign to that
-- symbol. If no pure symbol is found, it should return Nothing

-- This function considers each symbol from the given list at a time.
-- If the symbol is not in the given model, it is ignored and the function goes to another one.
-- If the helper function "alt" returnes a list of Bool values which are all True, the function returned a tuple of symbol and its value (True)
-- That means that the the symbol was present in at least one clause and it was always in the same form (therefore all valuses in the list returned by "alt" are True)
-- If the helper function "alt" returnes a list of Bool values which are all False, the function returned a tuple of symbol and its value (False)
-- That means that the the symbol was present in at least one clause and it was always in the same negated form (therefore all valuses in the list returned by "alt" are False)
-- And we have to "adjust" the valuse of the symbol to False to make it true.
-- If the helper function "alt" returnes a list of Bool values which are different from each other, the function igrnores the symbol and goes on to another one in the given list.
-- That means that the symbol was present in at least one clause from the list but it was in a different form.

findPureSymbol :: [Symbol] -> [Clause] -> Model -> Maybe (Symbol, Bool)
findPureSymbol [] clauses model = Nothing
findPureSymbol (s:symbols) clauses model 
	| lookupAssignment s model /= Nothing = findPureSymbol symbols clauses model
	| all (== True) (alt s clauses model) == True = Just (s,True)
	| all (== False) (alt s clauses model) == True = Just (s,False)
	| otherwise = findPureSymbol symbols clauses model 


----------FindUnitClause function:


-- This helper function checks if the given symbol is negated. 
-- If it is it returnes a tuple of the symbol and False value in order to make that single symbol true.
-- This function helps us with reducing the amount of code to write in the later stages.

checkNeg :: Symbol -> Maybe (Symbol, Bool)
checkNeg symbol 
	| isNegated symbol == True = Just (negateSymbol symbol,False)
	| otherwise = Just (symbol,True)

-- This helper function also returnes a tuple but if confronts the clause with the model.
-- It helps us with elimination of some clauses which are not needed to be considered.
-- Variable s is simply a list of all Maybe Bool values of the symbols from the clause.
-- Variable index is an (first to occur) index of an element in s which Maybe Bool value is Nothing.
-- If the clause consists of just one literal and that symbol in not indicated in the model (Nothing) 
-- then the function returnes the appropriate tuple using checkNeg helper function (a clause with just one literal)
-- If the clause consists of literals which Bool values are all False except one which is not indicated in the model then
-- the function returnes the appropriate tuple using checkNeg helper function (a clause in which all literals but one are already assigned false by the model).
-- If the clause is none of the above, it is ignored.

singleClause :: Clause -> Model -> Maybe (Symbol, Bool)
singleClause clause model 
	| length s == 1 && lookupAssignment (clause !! 0) model == Nothing = checkNeg (clause !! 0) 
	| (length (elemIndices (Just False) s) == (length s) - 1) && (length (elemIndices (Nothing) s) == 1) = checkNeg (clause !! index)
	| otherwise = Nothing
		where {s = [lookupAssignment c model | c <- clause];
			index = fromJust (elemIndex (Nothing) s)}

-- This function finds a unit clause from a given list of clauses and a model of assignments.
-- It returns Just a tuple of a symbol and the truth value to assign to that symbol. If no unit  
-- clause is found, it should return Nothing.

-- This function considers one clause from the list at a time.
-- If a singleClause helper function does not return Nothing 
-- (which means that that it is either a clause with just one literal or 
-- a clause in which all literals but one are already assigned false by the model)
-- the function returnes a tuple generated by the singleClause helper function.
-- Otherwise the clause is ignored and the function moves on to the next one.

findUnitClause :: [Clause] -> Model -> Maybe (Symbol, Bool)
findUnitClause [] model = Nothing
findUnitClause (c:clauses) model
	| singleClause c model /= Nothing = singleClause c model
	| otherwise = findUnitClause clauses model


----------DPLL function:


-- This helper function is necessary in order to make dpll function work. It works exactly the same as dpll function
-- but it contains a model which is updated each time after each symbol from the list is considered.
-- If a pure symbol is found, the function continues to search for another pure symbol or unit clause but considering the list of symbols 
-- without the found pure symbol and an updated model (by adding a tuple consisting of the pure symbol and its Bool value).
-- If a unit clause is found, the function continues to search for another pure symbol or unit clause but considering the list of symbols 
-- without the returned symbol by the findUnitClause function and an updated model (by adding a tuple consisting of the returned symbol and its Bool value).
-- If none of the above apply, the function continued with updated model (with tuple containing symbol and either True or False). 
-- If all of the symbols from the list have been considered, early termination occurs considering the latest model

dpll1 :: [Clause] -> [Symbol] -> Model -> Bool
dpll1 clauses [] model = earlyTerminate clauses model
dpll1 clauses (s:symbols) model
	| findPureSymbol (s:symbols) clauses model /= Nothing = dpll1 clauses (delete (fst (fromJust(findPureSymbol (s:symbols) clauses model))) (s:symbols)) ((fromJust (findPureSymbol (s:symbols) clauses model)) : model)
	| findUnitClause clauses model /= Nothing = dpll1 clauses (delete (fst (fromJust(findUnitClause clauses model))) (s:symbols)) ((fromJust (findUnitClause clauses model)) : model)
	| otherwise = (dpll1 clauses symbols ((s,True) : model)) || (dpll1 clauses symbols ((s,False) : model))

-- This function check the satisfability of a sentence in propositional logic. It takes as input a 
-- list of clauses in CNF, a list of symbols for the domain, and model. 
-- It returns true if there is a model which satises the propositional sentence. 
-- Otherwise it returns false.

-- This function calls dpll1 helper function with an empty model.

dpll :: [Clause] -> [Symbol] -> Bool
dpll [] symbols = True
dpll clauses [] = True
dpll clauses symbols = dpll1 clauses symbols []


----------dpllSatisfiable function:


-- This helper function returns a list of all symbols in the clause.
-- This function makes easier to implement the next helper function.

considerClause :: Clause -> [Symbol]
considerClause clause = [getUnsignedSymbol c | c <- clause]

-- This helper function returns a list of all symbols in the list of clauses.
-- This function is necessary for the dpllSatisfiable function since we need to get list of symbols used
-- in the list of clauses in order to use dpll function implemented before (which requires the list of symbols as one of its arguments).

considerClauses :: [Clause] -> [Symbol]
considerClauses [] = []
considerClauses (c:clauses) = considerClause c ++ considerClauses clauses

-- This function serves as the entry point to the dpll function. It takes a list clauses in CNF as 
-- input and returns true or false. 
-- It uses the dpll function above to determine the satisability of its input sentence.

-- This function simply exacutes dpll function with the list of symbol (without repetitions) created using helper functions. 

dpllSatisfiable :: [Clause] -> Bool
dpllSatisfiable clauses = dpll clauses symbols
	where symbols = nub (considerClauses clauses) 

----------TASK 5: EVALUATION (5 marks)--------------------------------------------------------------
-- EVALUATION
-- a knowledge base (i.e. a sentence in propositional 
-- logic), and a query sentence. Both items should have their clauses in CNF representation 
-- and should be assigned to the following respectively:

evalKB :: [Sentence]
evalKB = [[["-A","B"],["-B","C","A"],["-C","B"],["-B"]]]

evalQuery :: Sentence
evalQuery = [["-C"]]


-- RUNTIMES
-- Enter the average runtimes of the ttEntails and dpllSatisable functions respectively
runtimeTtEntails :: Double
runtimeTtEntails = 0.00202

runtimeDpll :: Double
runtimeDpll = 0.001214
