{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import System.Environment
import System.IO

--Sources:
--"Efficient Planarity Testing", John Hopcroft and Robert Tarjan
--"The Hopcroft-Trajan Plnarity Algorithm, Presentations and Improvements" David Gries and Jinyun Xue

----Data Structures

data Graph a = Graph [a] [(a, a)]

instance (Eq a) => Eq (Graph a) where
  (Graph v1 e1) == (Graph v2 e2) = v1 == v2 && e1 == e2

instance (Show a) => Show (Graph a) where
  show (Graph vertices edges) = "V: " ++ show vertices ++ " E: " ++ show edges

data Tree a = Tree a [Tree a]

instance (Show a) => Show (Tree a) where
  show (Tree value []) = "L: " ++ show value
  show (Tree value subtrees) = "T: " ++ show value ++ " " ++ show subtrees

------IO operations

myReadFile :: Handle -> IO ()
myReadFile handle =
  do
    eof <- hIsEOF handle
    if eof
      then return ()
      else do
        line <- hGetLine handle
        print line
        myReadFile handle

readV :: Handle -> IO [Int]
readV handle =
  do
    eof <- hIsEOF handle
    if eof
      then return []
      else do
        line <- hGetLine handle
        return (lineOfInts line)

readE :: Handle -> IO [(Int, Int)]
readE handle =
  do
    eof <- hIsEOF handle
    if eof
      then return []
      else do
        line <- hGetLine handle
        rest <- readE handle
        return (firstTwo (lineOfInts line) : rest)

firstTwo :: [Int] -> (Int, Int)
firstTwo (a : b : rs) = (a, b)

lineOfInts :: String -> [Int]
lineOfInts line = map (\x -> read x :: Int) (words line)

checkGraph :: String -> IO ()
checkGraph file =
  do
    fileHandle <- openFile file ReadMode
    ver <- readV fileHandle
    edg <- readE fileHandle
    print (isPlanar (Graph ver edg))
    hClose fileHandle

main :: IO ()
main = do
  print "Podaj nazwe pliku:"
  fileName <- getLine
  if fileName == "."
    then return ()
    else do
      checkGraph fileName
      main

----------Main body

isPlanar :: (Eq a) => Graph a -> Bool
isPlanar graph = all (\(Graph bver bedg) -> length bedg <= 1 || isBiComponentPlanar (Graph bver bedg) (anyCycle (Graph bver bedg)) (Graph [] [])) (concatMap allBiconnectedComponents (allSubgraphs graph))

isBiComponentPlanar :: (Eq a) => Graph a -> Graph a -> Graph a -> Bool
isBiComponentPlanar graph cycle seam = basicPlanarTest graph && checkAllSegments graph cycle (getSegments graph cycle) seam

checkAllSegments :: (Eq a) => Graph a -> Graph a -> [Graph a] -> Graph a -> Bool
checkAllSegments graph cycle segments seam = hasBipartitePartition graph cycle segments seam && all (\segment -> trigerRecurrency segment cycle (makeSeam cycle segment)) segments

trigerRecurrency :: (Eq a) => Graph a -> Graph a -> Graph a -> Bool
trigerRecurrency segment cycle seam = isBiComponentPlanar (graphUnion segment seam) (graphUnion seam (makeSpine cycle segment seam)) seam

makeSegmentGraph :: (Eq a) => Graph a -> Graph a -> [Graph a] -> Graph (Graph a)
makeSegmentGraph graph cycle segments = removeExtraEdges (Graph segments (concatMap (\x -> [(x, y) | y <- segments, interlace graph cycle x y]) segments))

removeExtraEdges :: (Eq a) => Graph a -> Graph a
removeExtraEdges (Graph ver edg) = Graph ver (foldl (\acc (next1, next2) -> if elem (next1, next2) acc || elem (next2, next1) acc then acc else (next1, next2) : acc) [] edg)

makeBipartitePartition :: (Eq a) => Graph a -> a -> ([a], [a]) -> Bool -> ([a], [a])
makeBipartitePartition (Graph ver edg) start (inside, outside) collor = foldl (\(accInside, accOutside) next -> if notElem next accInside && notElem next accOutside then makeBipartitePartition (Graph ver edg) next (accInside, accOutside) (not collor) else (accInside, accOutside)) (if collor then (start : inside, outside) else (inside, start : outside)) (filter (\x -> hasEdge (Graph ver edg) (start, x)) ver)

bipartitePartitionTest1 :: (Eq a) => Graph a -> ([a], [a]) -> Bool
bipartitePartitionTest1 (Graph ver edg) (inside, outside) = null [(x, y) | x <- inside, y <- inside, x /= y, hasEdge (Graph ver edg) (x, y)]

bipartitePartitionTest2 :: (Eq a) => Graph a -> ([a], [a]) -> [a] -> Bool
bipartitePartitionTest2 (Graph ver edg) (inside, outside) specials = null (specials `intersect` outside) || null (specials `intersect` inside)

checkBipartitePartition :: (Eq a) => Graph a -> ([a], [a]) -> [a] -> Bool
checkBipartitePartition graph patrition specials = bipartitePartitionTest1 graph patrition && bipartitePartitionTest2 graph patrition specials

hasBipartitePartition :: (Eq a) => Graph a -> Graph a -> [Graph a] -> Graph a -> Bool
hasBipartitePartition graph cycle segments seam = all (\(Graph (v : vs) edg) -> checkBipartitePartition (Graph (v : vs) edg) (makeBipartitePartition (Graph (v : vs) edg) v ([], []) True) (filter (isSpecial seam) segments)) (allSubgraphs (makeSegmentGraph graph cycle segments))

hasEdge :: (Eq a) => Graph a -> (a, a) -> Bool
hasEdge (Graph vertices []) (v1, v2) = False
hasEdge (Graph vertices ((e1, e2) : es)) (v1, v2) = (e1 == v1 && e2 == v2 || e1 == v2 && e2 == v1) || hasEdge (Graph vertices es) (v1, v2)

hasPath :: (Eq a) => Graph a -> (a, a) -> Bool
hasPath (Graph vertices edges) (v1, v2)
  | notElem v1 vertices || notElem v2 vertices = False
  | v1 == v2 = True
  | otherwise = not (null ([x | x <- vertices, hasEdge (Graph vertices edges) (v1, x), hasPath (Graph (filter (/= v1) vertices) edges) (x, v2)]))

findPaths :: (Eq a) => Graph a -> (a, a) -> [[a]]
findPaths (Graph vertices edges) (v1, v2) =
  if v1 == v2
    then [[v2]]
    else concatMap (map (v1 :)) [findPaths (Graph (filter (/= v1) vertices) edges) (x, v2) | x <- vertices, hasEdge (Graph vertices edges) (v1, x)]

basicPlanarTest :: Graph a -> Bool
basicPlanarTest (Graph vertices edges) = length vertices < 3 || length edges <= 3 * length vertices - 6

findCicles :: (Eq a) => Graph a -> a -> [Graph a]
findCicles (Graph vertices edges) start = map pathToGraph (concatMap (map (start :)) [findPaths (Graph vertices (filter (\z -> z /= (start, x)) edges)) (x, start) | x <- vertices, hasEdge (Graph vertices edges) (start, x)])

pathToGraph :: (Eq a) => [a] -> Graph a
pathToGraph [] = Graph [] []
pathToGraph [x] = Graph [x] []
pathToGraph (x1 : x2 : xs) = graphUnion (Graph [x1] [(x1, x2)]) (pathToGraph (x2 : xs))

--longestCycle::(Eq a) => Graph a ->Graph a
--longestCycle (Graph (v:vertices) edges)=maximumLengthCycle (findCicles (Graph (v:vertices) edges) v)

-- maximumLengthCycle :: (Eq a) => [Graph a] -> Graph a
-- maximumLengthCycle = foldl (\(Graph evertices eedges) (Graph nvertices nedges) -> if length nvertices > length evertices then Graph nvertices nedges else Graph evertices eedges) (Graph [] [])

anyCycle :: Eq a => Graph a -> Graph a
anyCycle (Graph (v : vertices) edges) = head (findCicles (Graph (v : vertices) edges) v)

getSegments :: (Eq a) => Graph a -> Graph a -> [Graph a]
getSegments (Graph vertices edges) (Graph cvertices cycleE) = map (edgesToGraph (Graph vertices edges)) (foldl (\acc next -> if next `elem` concat acc then acc else [x | x <- edges, not (containsEdge cycleE x), x `notElem` concat acc, areEdgesInSameSegment (Graph (difference vertices cvertices) edges) x next] : acc) [] (filter (not . containsEdge cycleE) edges))

containsEdge :: (Eq a) => [(a, a)] -> (a, a) -> Bool
containsEdge xs toCheck =
  foldr (\x -> (||) (sameEdge x toCheck)) False xs

edgesToGraph :: (Eq a) => Graph a -> [(a, a)] -> Graph a
edgesToGraph (Graph vertices edges) myEdges = Graph [x | x <- vertices, elem x (map fst myEdges) || elem x (map snd myEdges)] myEdges

areEdgesInSameSegment :: (Eq a) => Graph a -> (a, a) -> (a, a) -> Bool
areEdgesInSameSegment graph (e11, e12) (e21, e22) = sameEdge (e11, e12) (e21, e22) || hasPath graph (e11, e21) || hasPath graph (e11, e22) || hasPath graph (e12, e21) || hasPath graph (e12, e22)

sameEdge :: (Eq a) => (a, a) -> (a, a) -> Bool
sameEdge (e11, e12) (e21, e22) = e11 == e21 && e12 == e22 || e11 == e22 && e12 == e21

allSubgraphs :: (Eq a) => Graph a -> [Graph a]
allSubgraphs (Graph vertices edges) = map (packVerticles (Graph vertices edges)) (foldl (\acc next -> if next `elem` concat acc then acc else getSubgraph (Graph (difference vertices (concat acc)) edges) next : acc) [] vertices)

getSubgraph :: (Eq a) => Graph a -> a -> [a]
getSubgraph (Graph vertices edges) start = filter (\x -> hasPath (Graph vertices edges) (start, x)) vertices

graphUnion :: (Eq a) => Graph a -> Graph a -> Graph a
graphUnion (Graph vertices1 edges1) (Graph vertices2 edges2) = Graph (vertices1 `union` vertices2) (edges1 `union` edges2)

packVerticles :: (Eq a) => Graph a -> [a] -> Graph a
packVerticles (Graph vertices edges) vertices2 = Graph vertices2 (filter (\(e1, e2) -> elem e1 vertices2 && elem e2 vertices2) edges)

interlaceTestMachine :: (Int, Char) -> Bool -> Bool -> (Int, Char)
interlaceTestMachine (4, c) _ _ = (4, c)
interlaceTestMachine (n, c) False False = (n, c)
interlaceTestMachine (n, 'a') True True = (n + 1, 'a')
interlaceTestMachine (n, 'l') True True = (n + 1, 'r')
interlaceTestMachine (n, 'r') True True = (n + 1, 'l')
interlaceTestMachine (n, 'a') True False = (n + 1, 'r')
interlaceTestMachine (n, 'l') True False = (n + 1, 'r')
interlaceTestMachine (n, 'r') True False = (n, 'r')
interlaceTestMachine (n, 'a') False True = (n + 1, 'l')
interlaceTestMachine (n, 'l') False True = (n, 'l')
interlaceTestMachine (n, 'r') False True = (n + 1, 'l')

interlaceTest1 :: (Eq a) => [a] -> [a] -> Bool
interlaceTest1 a b = length (a `intersect` b) >= 3

interlaceTest2 :: (Eq a) => [a] -> [a] -> [a] -> Bool
interlaceTest2 cycle first second = 4 <= fst (foldl (\acc next -> interlaceTestMachine acc (next `elem` first) (next `elem` second)) (0, 'a') cycle)

interlace :: (Eq a) => Graph a -> Graph a -> Graph a -> Graph a -> Bool
interlace graph (Graph cver cedg) (Graph s1ver s1edg) (Graph s2ver s2edg) = interlaceTest1 (cver `intersect` s1ver) (cver `intersect` s2ver) || interlaceTest2 cver s1ver s2ver

makeSeam :: (Eq a) => Graph a -> Graph a -> Graph a
makeSeam (Graph cycleV cycleE) (Graph segmentV segmentE) = pathToGraph (fst (snd (foldl seamFold (cycleV `intersect` segmentV, ([], False)) cycleV)))

seamFold :: (Eq a) => ([a], ([a], Bool)) -> a -> ([a], ([a], Bool))
seamFold ([], (e, b)) next = ([], (e, b))
seamFold (x : xs, (e, False)) next = if x == next then (xs, (next : e, True)) else (x : xs, (e, False))
seamFold (x : xs, (e, True)) next = if x == next then (xs, (next : e, True)) else (x : xs, (next : e, True))

makeSpine :: (Eq a) => Graph a -> Graph a -> Graph a -> Graph a
makeSpine (Graph cycleV cycleE) (Graph segmentV segmentE) (Graph seamverticles seamedges) = pathToGraph $ head (findPaths (Graph (last seamverticles : head seamverticles : filter (`notElem` seamverticles) segmentV) segmentE) (last seamverticles, head seamverticles))

isSpecial :: (Eq a) => Graph a -> Graph a -> Bool
isSpecial (Graph seamV seamE) (Graph segmentV segmentE) = length seamV >= 2 && not (null (tail (init seamV) `intersect` segmentV))

difference :: (Eq a) => [a] -> [a] -> [a]
difference listA listB = filter (`notElem` listB) listA

union :: (Eq a) => [a] -> [a] -> [a]
union listA listB = listA ++ filter (`notElem` listA) listB

intersect :: (Eq a) => [a] -> [a] -> [a]
intersect listA listB = filter (`elem` listB) listA

----Tree operations

allBiconnectedComponents :: (Eq a) => Graph a -> [Graph a]
allBiconnectedComponents (Graph (v : vertices) edges) = map removeUnesesryEdges (addRemainer (splitGraph (dfs (Graph (v : vertices) edges) 1 v [] v) (Graph (v : vertices) edges, [])))

removeUnesesryEdges :: (Eq a) => Graph a -> Graph a
removeUnesesryEdges (Graph ver edg) = Graph ver (filter (\(a, b) -> a `elem` ver && b `elem` ver) edg)

dfs :: (Eq a) => Graph a -> Int -> a -> [(a, Int)] -> a -> Tree (a, Int, Int)
dfs (Graph vertices edges) depth current visited father = foldl (dfsDecider (Graph vertices edges) depth current visited father) (Tree (current, depth, depth) []) (filter (\x -> hasEdge (Graph vertices edges) (current, x)) vertices)

dfsDecider :: (Eq a) => Graph a -> Int -> a -> [(a, Int)] -> a -> Tree (a, Int, Int) -> a -> Tree (a, Int, Int)
dfsDecider (Graph vertices edges) depth current visited father (Tree (c, d, l) children) next
  | father == next || treeContains (Tree (c, d, l) children) next = Tree (c, d, l) children
  | isInVisited visited next = Tree (c, d, min (visitedLowpoint visited next) l) children
  | otherwise = dfsDeciderFold (Tree (c, d, l) children) (dfs (Graph vertices edges) (depth + 1) next ((current, depth) : visited) current)

dfsDeciderFold :: (Eq a) => Tree (a, Int, Int) -> Tree (a, Int, Int) -> Tree (a, Int, Int)
dfsDeciderFold (Tree (ei, ed, el) echildren) (Tree (ni, nd, nl) nchildren) = Tree (ei, ed, min el nl) (Tree (ni, nd, nl) nchildren : echildren)

isInVisited :: (Eq a) => [(a, Int)] -> a -> Bool
isInVisited [] w = False
isInVisited ((a, b) : xs) w = a == w || isInVisited xs w

visitedLowpoint :: (Eq a) => [(a, Int)] -> a -> Int
visitedLowpoint [] w = 0
visitedLowpoint ((a, b) : xs) w = if a == w then b else visitedLowpoint xs w

treeContains :: (Eq a) => Tree (a, Int, Int) -> a -> Bool
treeContains (Tree (value, _, _) subtrees) x = x == value || or [treeContains y x | y <- subtrees]

traverseTree :: (Eq a) => Tree (a, Int, Int) -> (Graph a, [Graph a]) -> (Graph a, [Graph a])
traverseTree (Tree (i, d, l) children) (Graph vertices edges, taken) = updateNode (Tree (i, d, l) children) (foldl (\acc (Tree (ni, nd, nl) nchildren) -> traverseTree (Tree (ni, nd, nl) nchildren) acc) (Graph vertices edges, taken) children)

updateRoot :: (Eq a) => Tree (a, Int, Int) -> (Graph a, [Graph a]) -> (Graph a, [Graph a])
updateRoot (Tree (i, d, l) children) (Graph vertices edges, taken) = foldl (\acc (Tree (ni, nd, nl) nchildren) -> if length children >= 2 then updateState acc i (subtreeElements (Graph vertices edges) (Tree (ni, nd, nl) nchildren)) else acc) (Graph vertices edges, taken) children

updateNode :: (Eq a) => Tree (a, Int, Int) -> (Graph a, [Graph a]) -> (Graph a, [Graph a])
updateNode (Tree (i, d, l) children) (graph, taken) = foldl (\acc (Tree (ni, nd, nl) nchildren) -> if nl >= d then updateState acc i (subtreeElements graph (Tree (ni, nd, nl) nchildren)) else acc) (graph, taken) children

updateState :: (Eq a) => (Graph a, [Graph a]) -> a -> [a] -> (Graph a, [Graph a])
updateState (Graph vertices edges, removed) patrition toRemove = (Graph (difference vertices toRemove) edges, Graph (patrition : toRemove) edges : removed)

subtreeElements :: (Eq a) => Graph a -> Tree (a, Int, Int) -> [a]
subtreeElements (Graph vertices edges) (Tree (i, d, l) children) = if i `elem` vertices then i : concatMap (subtreeElements (Graph vertices edges)) children else []

splitGraph :: (Eq a) => Tree (a, Int, Int) -> (Graph a, [Graph a]) -> (Graph a, [Graph a])
splitGraph (Tree (i, d, l) children) (graph, taken) = updateRoot (Tree (i, d, l) children) (foldl (\acc (Tree (ni, nd, nl) nchildren) -> traverseTree (Tree (ni, nd, nl) nchildren) acc) (graph, taken) children)

addRemainer :: (Eq a) => (Graph a, [Graph a]) -> [Graph a]
addRemainer (Graph ver edg, rest) = if length ver > 1 then Graph ver edg : rest else rest

-------------------