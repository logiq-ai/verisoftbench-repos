-- import Mathlib
-- #check (deriv : (real → real) → (real → real))

-- namespace List

-- -- Define a boolean variable as a string (variable name).
-- def Var := String

-- -- Define a literal as either a variable or its negation.
-- inductive Literal :=
--   | pos (v : Var)  -- Positive literal (e.g., x)
--   | neg (v : Var)  -- Negative literal (e.g., ¬x)

-- -- Define a clause as a list of literals (disjunction of literals).
-- def Clause := List Literal

-- -- Define a CNF formula as a list of clauses (conjunction of clauses).
-- def Formula := List Clause

-- -- Define a boolean assignment as a function from variables to boolean values.
-- def Assignment := Var → Bool

-- -- Function to evaluate a literal under a given assignment.
-- def evalLiteral (a : Assignment) : Literal → Bool
-- | Literal.pos v => a v
-- | Literal.neg v => not (a v)

-- -- Function to evaluate a clause under a given assignment.
-- def evalClause (a : Assignment) : Clause → Bool
-- | []        => false  -- An empty clause is unsatisfiable.
-- | (l :: ls) => evalLiteral (a) l || evalClause (a) ls

-- -- Function to evaluate a formula under a given assignment.
-- def evalFormula (a : Assignment) : Formula → Bool
-- | []        => true  -- An empty formula is trivially satisfiable.
-- | (c :: cs) => evalClause (a) c && evalFormula (a) cs


-- -- Verifier function

-- -- Example variables
-- def x := "x"
-- def y := "y"
-- def z := "z"

-- -- Example formula: (x ∨ ¬y) ∧ (y ∨ z)
-- def exampleFormula : Formula :=
--   [[Literal.pos x, Literal.neg y],  -- Clause 1: (x ∨ ¬y)
--    [Literal.pos y, Literal.pos z]]  -- Clause 2: (y ∨ z)


-- -- Define a type for nodes (vertices) in the graph.
-- def Node := Nat

-- -- Define a type for the weight (cost) of edges.
-- def Weight := Nat

-- -- Define an adjacency list for the graph, where each node maps to its neighbors with edge weights.
-- def Graph := HashMap Node (List (Node × Weight))

-- -- Define an infinite distance value.
-- def InfDist : Weight := 1000000000 -- A large value to represent infinity

-- -- Initialize distances from source node.
-- def initDist (g : Graph) (src : Node) : HashMap Node Weight :=
--   g.fold (fun dist n _ => dist.insert n InfDist) (HashMap.empty.insert src 0)

-- -- Get the node with the smallest distance that is not yet visited.
-- def getMinDist (dist : HashMap Node Weight) (visited : HashMap Node Bool) : Option Node :=
--   dist.fold (fun acc n d =>
--     if visited.contains n then acc
--     else match acc with
--          | none => some n
--          | some minNode => if d < dist.findD minNode InfDist then some n else acc) none

-- -- Dijkstra's Algorithm implementation.
-- def dijkstra (g : Graph) (src : Node) : HashMap Node Weight :=
--   let rec loop (dist : HashMap Node Weight) (visited : HashMap Node Bool) : HashMap Node Weight :=
--     match getMinDist dist visited with
--     | none => dist
--     | some u =>
--       let neighbors := g.findD u []
--       let dist := neighbors.foldl (fun dist (v, w) =>
--         if visited.contains v then dist
--         else
--           let newDist := dist.findD u InfDist + w
--           if newDist < dist.findD v InfDist then dist.insert v newDist else dist) dist
--       loop dist (visited.insert u true)
--   loop (initDist g src) HashMap.empty

-- -- Verifier function: Check if the distances returned by Dijkstra's algorithm are correct.
-- def verifyDijkstra (g : Graph) (src : Node) (dist : HashMap Node Weight) : Bool :=
--   g.fold (fun isValid u neighbors =>
--     neighbors.foldl (fun isValid (v, w) =>
--       let d_u := dist.findD u InfDist
--       let d_v := dist.findD v InfDist
--       isValid && (d_v ≤ d_u + w)
--     ) isValid
--   ) true
