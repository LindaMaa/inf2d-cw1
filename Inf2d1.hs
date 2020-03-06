-- Inf2d Assignment 1 2019-2020
-- Matriculation number: s1801828
-- {-# OPTIONS -Wall #-}


module Inf2d1 where

import Data.List (sortBy, elemIndices, elemIndex)
import ConnectFourWithTwist




{- NOTES:

-- DO NOT CHANGE THE NAMES OR TYPE DEFINITIONS OF THE FUNCTIONS!
You can write new auxillary functions, but don't change the names or type definitions
of the functions which you are asked to implement.

-- Comment your code.

-- You should submit this file when you have finished the assignment.

-- The deadline is the  10th March 2020 at 3pm.

-- See the assignment sheet and document files for more information on the predefined game functions.

-- See the README for description of a user interface to test your code.

-- See www.haskell.org for haskell revision.

-- Useful haskell topics, which you should revise:
-- Recursion
-- The Maybe monad
-- Higher-order functions
-- List processing functions: map, fold, filter, sortBy ...

-- See Russell and Norvig Chapters 3 for search algorithms,
-- and Chapter 5 for game search algorithms.

-}

-- Section 1: Uniform Search

-- 6 x 6 grid search states

-- The Node type defines the position of the robot on the grid.
-- The Branch type synonym defines the branch of search through the grid.
type Node = Int
type Branch = [Node]
type Graph= [Node]

numNodes::Int
numNodes = 10




-- The next function should return all the possible continuations of input search branch through the graph.
-- Your function should return an empty list if the input search branch is empty.
-- This implementation of next function does not backtrace branches.

next::Branch -> Graph ->[Branch]
next [] _ = [] -- branch empty
next _ [] = [] -- graph empty
-- iterate through the row in the adjacency matrix, if path found to node n, expand the search branch with node n
next branch g = [((x `mod` numNodes) : branch) | (x,y) <- zip [0..] g, x>=(head branch)*numNodes && x<(head branch)*numNodes+numNodes && y>0 ]

-- checkArrival returns true iff the node being explored is a goal node
checkArrival::Node -> Node -> Bool
checkArrival n_goal n_current
  | (n_goal == n_current) = True
  | otherwise = False

-- explored checks whether node that is being explored is in the explored list
explored::Node-> [Node] ->Bool
explored n_current [] = False
explored n_current exploredList = or([n_current==x| x<- exploredList])

-- Section 3 Uniformed Search
-- | Breadth-First Search
-- The breadthFirstSearch function should use the next function to expand a node,
-- and the checkArrival function to check whether a node is a destination position.
-- The function should search nodes using a breadth first search order.

breadthFirstSearch::Graph -> Node->(Branch ->Graph -> [Branch])->[Branch]->[Node]->Maybe Branch
breadthFirstSearch g destination next [] exploredList = Nothing -- empty search agenda
breadthFirstSearch g destination next branches exploredList
  |(checkArrival destination (head (head branches))) = Just (head branches) -- goal state reached
  --check whether current node was explored, if not, explore it, add it to the exploredList, otherwise explore other branches
  |(notElem (head (head branches)) exploredList) = breadthFirstSearch g destination next (tail branches ++ next (head branches) g) ((head (head branches)) : exploredList) --explore current node
  | otherwise = breadthFirstSearch g destination next (tail branches) exploredList --ignore current node


-- | Depth-Limited Search
-- The depthLimitedSearch function is similiar to the depthFirstSearch function,
-- except its search is limited to a pre-determined depth, d, in the search tree.
depthLimitedSearch::Graph ->Node->(Branch ->Graph-> [Branch])->[Branch]-> Int->[Node]-> Maybe Branch
depthLimitedSearch g destination next [] d exploredList = Nothing -- empty agenda
depthLimitedSearch g destination next branches d exploredList
  |(d<=0) = Nothing --invalid depth
  |(checkArrival destination (head (head branches))) = Just (head branches) --goal state reached
  -- if node is not explored and the depth limit was not reached, explore the node
  |(notElem (head (head branches)) exploredList) && (length(head branches) <= d) = depthLimitedSearch g destination next (next (head branches) g ++ tail branches) d ((head (head branches)) : exploredList)
  | otherwise = depthLimitedSearch g destination next (tail branches) d exploredList



-- | Section 4: Informed search


-- | AStar Helper Functions

-- | The cost function calculates the current cost of a trace. The cost for a single transition is given in the adjacency matrix.
-- The cost of a whole trace is the sum of all relevant transition costs.
cost :: Graph ->Branch  -> Int
cost gr [] = 0 --empty branch, cost 0
--iterate through transitions in the branch and sum up the costs of individual transitions
cost gr (branch) = sum[ (gr !! ((x*numNodes)+y)) | (x,y) <- zip branch ((tail branch) ++ [0])]

-- | The getHr function reads the heuristic for a node from a given heuristic table.
-- The heuristic table gives the heuristic (in this case straight line distance) and has one entry per node. It is ordered by node (e.g. the heuristic for node 0 can be found at index 0 ..)
getHr:: [Int]->Node->Int
getHr [] node = 0
getHr hrTable node = hrTable!!node -- get heuristic at index node

-- compare2 helper function orders 2 branches relative to each other
compare2:: (Branch, Int) -> (Branch, Int) -> Ordering
compare2 (b1,c1) (b2,c2) = compare c1 c2

-- sort function sorts the branches using compare2 so that the nodes with the lowest total (cost+heuristic value) are first in the list
sort2 :: [Branch] -> ([Int]->Node->Int) -> [Int] -> Graph-> (Graph->Branch->Int) -> [Branch]
sort2 branches getHr hrTable g cost = [x | (x,y) <- sortBy compare2 (zip branches (zipWith (+) (map ((getHr hrTable) . head) branches) (map (cost g) branches)))]


-- | A* Search
-- The aStarSearch function uses the checkArrival function to check whether a node is a destination position,
---- and a combination of the cost and heuristic functions to determine the order in which nodes are searched.
---- Nodes with a lower heuristic value should be searched before nodes with a higher heuristic value.

aStarSearch::Graph->Node->(Branch->Graph -> [Branch])->([Int]->Node->Int)->[Int]->(Graph->Branch->Int)->[Branch]-> [Node]-> Maybe Branch
aStarSearch g destination next getHr hrTable cost [] exploredList = Nothing -- empty search agenda
aStarSearch g destination next getHr hrTable cost branches exploredList
  |(checkArrival destination (head (head branches))) = Just (head branches) --goal state reached
  --if current node not explored, then explore it, otherwise ignore it and explore other nodes on the search agenda
  |(notElem (head (head branches)) exploredList) = aStarSearch g destination next getHr hrTable cost ((next (head (sort2 branches getHr hrTable g cost)) g) ++ tail (sort2 branches getHr hrTable g cost)) ((head (head branches)): exploredList)
  |otherwise = aStarSearch g destination next getHr hrTable cost (tail (sort2 branches getHr hrTable g cost)) exploredList

-- | Section 5: Games
-- See ConnectFourWithTwist.hs for more detail on  functions that might be helpful for your implementation.



-- | Section 5.1 Connect Four with a Twist



-- The function determines the score of a terminal state, assigning it a value of +1, -1 or 0:
eval :: Game -> Int
eval game
  |terminal game && (checkWin game 1)  = 1 --Player wins
  |terminal game && (checkWin game 0)= -1 --minPlayer wins
  |otherwise                   = 0 --no win


-- | The alphabeta function should return the minimax value using alphabeta pruning.
-- The eval function should be used to get the value of a terminal state.

alphabeta:: Role -> Game -> Int
alphabeta player game
 | (terminal game) = eval game --terminal state reached, return score of the game
 | (player == 1) = maxvalue game (-2) 2 -- maxPlayer plays
 | (player == 0) = minvalue game (-2) 2 -- minPlayer plays

-- a loop function that iterates through the results of all possible actions and maximises the utility value v
maxv:: [Game]-> Int-> Int-> Int-> Int
maxv[] a b v = v -- empty list of states of game
maxv (g:games) a b v
   |(max v (minvalue g a b)) >= b = (max v (minvalue g a b)) -- if v>=b
   |otherwise = maxv games (max a v) b (max v (minvalue g a b)) -- a=max(a,v)

-- a loop function that iterates through the results of all possible actions and minimizes the utility value v
minv:: [Game]-> Int-> Int-> Int-> Int
minv [] a b v  = v -- empty list of states of game
minv (g:games) a b v
  | (min v (maxvalue g a b)) <= a = (min v (maxvalue g a b)) -- if v<=a
  | otherwise = minv games a (min b v) (min v (maxvalue g a b)) -- b=min(b,v)

-- minPlayer's turn
minvalue:: Game -> Int -> Int -> Int
minvalue game a b
  |terminal game = eval game --terminal state reached, return result of the game
  |otherwise = minv (moves game 0) a b b -- v=b, enter min value loop

-- maxPlayer's turn
maxvalue:: Game -> Int -> Int -> Int
maxvalue game a b
  | terminal game = eval game --terminal state reached, return result of the game
  | otherwise = maxv (moves game 1) a b a -- v=a, enter max value loop





-- | OPTIONAL!
-- You can try implementing this as a test for yourself or if you find alphabeta pruning too hard.
-- If you implement minimax instead of alphabeta, the maximum points you can get is 10% instead of 15%.
-- Note, we will only grade this function IF YOUR ALPHABETA FUNCTION IS EMPTY.
-- The minimax function should return the minimax value of the state (without alphabeta pruning).
-- The eval function should be used to get the value of a terminal state.
minimax:: Role -> Game -> Int
minimax player game=undefined
{- Auxiliary Functions
-- Include any auxiliary functions you need for your algorithms below.
-- For each function, state its purpose and comment adequately.
-- Functions which increase the complexity of the algorithm will not get additional scores
-}
