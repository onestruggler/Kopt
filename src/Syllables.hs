-- | Experiments with 2-qubit Clifford+/T/ circuits.

module Syllables where

import Data.List
import Data.Function
import Text.Printf
import qualified Data.Map as Map
import Data.Map (Map)
import System.Environment
import System.IO

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring hiding (Omega)
import Quantum.Synthesis.MultiQubitSynthesis

-- ----------------------------------------------------------------------
-- * Derivations

-- | An enumeration for some tactics.
data Tactic = ByClifford
  deriving (Show, Eq)

-- | A derivation provides evidence that a certain equational
-- statement is true. The meaning of an equation Γ ⊢ v = w is that v
-- and w desugar to the same sequence of elementary gates, which are
-- W, H0, H1, S0, S1, T0, T1, ZZ.
data Der a =
  Refl [a] [a]              -- ^ Refl w : Γ ⊢ w = w.
  | Symm (Der a)            -- ^ If d : Γ ⊢ w = v, then Symm d : Γ ⊢ v = w.
  | Trans (Der a) (Der a) [a] [a]  -- ^ If d1 : Γ ⊢ w = v and d2 : Γ ⊢ v = u, then Trans d1 d2 w u : Γ ⊢ w = u.
  | Cong [a] (Der a) [a]    -- ^ If d : Γ ⊢ w = v, then Cong a d b : Γ ⊢ awb = avb.
  | Lemma String (Eqn [a])  -- ^ Lemma x A : Γ ⊢ A, where x is the name of the corresponding lemma.
  | Tactic Tactic (Eqn [a]) -- ^ Tactic x A : Γ ⊢ A, where x is the name of the corresponding tactic.
                            -- The difference between a lemma and a tactic is that the lemma knows
                            -- what equation it is proving, whereas for the tactic it is an input.
  deriving (Show, Eq)

-- | If d1 : Γ ⊢ w = w' and d2 : Γ ⊢ v = v', then cong2 d1 d2 : Γ ⊢ wv = w'v'.
cong2 :: (Show a, Eq a, Desugar_Agda a) => Der a -> Der a -> Der a
cong2 d1 d2 = trans (Cong [] d1 v) (Cong w' d2 [])
  where
    Eqn w w' = eqn_of_der d1
    Eqn v v' = eqn_of_der d2

-- ----------------------------------------------------------------------
-- ** Checking derivations

class Desugar_Agda a where
  -- | Desugar generators in the same way our Agda code does.
  desugar_agda :: [a] -> [Gate]
  check_equation :: Eqn [a] -> Bool

instance Desugar_Agda Gate where
  desugar_agda [] = []
  desugar_agda (R pauli : gs) = desugar_agda (rsyll_def pauli) ++ desugar_agda gs
  desugar_agda (T0 : gs) = [T0] ++ desugar_agda gs
  desugar_agda (ZZ : gs) = [ZZ] ++ desugar_agda gs
  desugar_agda (CX0 : gs) = [H0, ZZ, H0] ++ desugar_agda gs
  desugar_agda (CX1 : gs) = [H1, ZZ, H1] ++ desugar_agda gs
  desugar_agda (CH0 : gs) = [S0, H0, T0, H0, ZZ, H0, T0, T0, T0, T0, T0, T0, T0, H0, S0, S0, S0] ++ desugar_agda gs
  desugar_agda (CH1 : gs) = [S1, H1, T1, H1, ZZ, H1, T1, T1, T1, T1, T1, T1, T1, H1, S1, S1, S1] ++ desugar_agda gs
  desugar_agda (CS : gs) = desugar_agda [T0, T1, CX0, T0inv, CX0] ++ desugar_agda gs
  desugar_agda (Swap : gs) = [H0, ZZ, H0, H1, ZZ, H1, H0, ZZ, H0] ++ desugar_agda gs
  desugar_agda (H0 : gs) = [H0] ++ desugar_agda gs
  desugar_agda (H1 : gs) = [H1] ++ desugar_agda gs
  desugar_agda (S0 : gs) = [S0] ++ desugar_agda gs
  desugar_agda (S1 : gs) = [S1] ++ desugar_agda gs
  desugar_agda (S0inv : gs) = [S0, S0, S0] ++ desugar_agda gs
  desugar_agda (S1inv : gs) = [S1, S1, S1] ++ desugar_agda gs
  desugar_agda (T1 : gs) = [T1] ++ desugar_agda gs
  desugar_agda (T0inv : gs) = [T0, T0, T0, T0, T0, T0, T0] ++ desugar_agda gs
  desugar_agda (T1inv : gs) = [T1, T1, T1, T1, T1, T1, T1] ++ desugar_agda gs
  desugar_agda (X0 : gs) = [H0, S0, S0, H0] ++ desugar_agda gs
  desugar_agda (X1 : gs) = [H1, S1, S1, H1] ++ desugar_agda gs
  desugar_agda (Omega k : gs) = replicate k (Omega 1) ++ desugar_agda gs
  check_equation = check_gate_relation

-- | A version of 'Trans' that checks the correctness right away.
trans :: (Show a, Desugar_Agda a, Eq a) => Der a -> Der a -> Der a
trans d1 d2
--  | True = Trans d1 d2 w u -- uncomment this to temporarily disable checking, to enable laziness
  | desugar_agda v == desugar_agda v' = Trans d1 d2 w u
  | otherwise = error ("trans: " ++ show v ++ " /= " ++ show v')
  where
    Eqn w v = eqn_of_der d1
    Eqn v' u = eqn_of_der d2

-- | A version of 'Refl' that checks correctness.
refl :: (Show a, Desugar_Agda a) => [a] -> [a] -> Der a
refl v w
  | desugar_agda v == desugar_agda w = Refl v w
  | otherwise = error ("refl: " ++ show v ++ " /= " ++ show w)

-- | Input a derivation and output the equation that the derivation
-- proves (without checking correctness).
eqn_of_der :: (Show a, Eq a, Desugar_Agda a) => Der a -> Eqn [a]
eqn_of_der (Refl w v) = Eqn w v
eqn_of_der (Symm d) = Eqn v w
  where
    Eqn w v = eqn_of_der d
eqn_of_der (Trans d1 d2 w v) = Eqn w v
eqn_of_der (Cong a d b) = Eqn (a ++ w ++ b) (a ++ v ++ b)
  where
    Eqn w v = eqn_of_der d
eqn_of_der (Lemma x eq) = eq
eqn_of_der (Tactic x eq) = eq

-- | Check that an equation is correct. If it is not correct, throw an error.
check_der :: (Show a, Eq a, Desugar_Agda a) => Der a -> Bool
check_der (Refl w v)
  | desugar_agda w == desugar_agda v = True
  | otherwise = error ("check_der: incorrect use of reflexivity: " ++ show w ++ " /= " ++ show v);
check_der (Symm d) = check_der d
check_der (Trans d1 d2 w' u')
  | desugar_agda v /= desugar_agda v' = error ("check_der: incorrect use of transitivity: " ++ show v ++ " /= " ++ show v')
  | w' /= w = error ("check_der: transitivity left word mismatch: " ++ show w' ++ " /= " ++ show w)
  | u' /= u = error ("check_der: transitivity right word mismatch: " ++ show u' ++ " /= " ++ show u)
  | otherwise = True
  where
    Eqn w v = eqn_of_der d1
    Eqn v' u = eqn_of_der d2
check_der (Cong a d b) = True
check_der (Lemma x eq) =
  case check_equation eq of
    True -> True
    False -> error ("check_der: false Lemma: " ++ show eq)
check_der (Tactic x eq) =
  case check_equation eq of
    True -> True
    False -> error ("check_der: false Tactic: " ++ show eq)

-- ----------------------------------------------------------------------
-- ** Flattening of derivations

-- | Flatten a derivation. A flattened derivation is a sequence of
-- elementary steps, each of which is an optional congruence of an
-- optional symmetry of a lemma, with transitivity only used at the
-- top level.
flatten_der_aux :: (Eq a) => Der a -> ([Der a], [a], [a])
flatten_der_aux (Refl v w)
  | v == w = ([], v, w)
  | otherwise = ([Refl v w], v, w)
flatten_der_aux (Symm d) = (map symm (reverse steps), w, v)
  where
    (steps, v, w) = flatten_der_aux d
    symm (Symm d) = d
    symm (Cong a d b) = Cong a (symm d) b
    symm (Tactic ByClifford (Eqn u v)) = Tactic ByClifford (Eqn v u)
    symm x = Symm x
flatten_der_aux (Trans d1 d2 _ _) = (steps1 ++ steps2, v, u)
  where
    (steps1, v, w) = flatten_der_aux d1
    (steps2, w', u) = flatten_der_aux d2
flatten_der_aux (Cong [] d []) = flatten_der_aux d
flatten_der_aux (Cong a d b) = (map cong steps, a++v++b, a++w++b)
  where
    (steps, v, w) = flatten_der_aux d
    cong (Cong a1 d b1) = Cong (a++a1) d (b1++b)
    cong x = Cong a x b
flatten_der_aux (Lemma name eq) = ([Lemma name eq], v, w)
  where
    Eqn v w = eq
flatten_der_aux (Tactic name eq) = ([Tactic name eq], v, w)
  where
    Eqn v w = eq

-- | Simplify a derivation. This gets rid of most instances of
-- reflexivity, and uses transitivity only at the top level.
flatten_der :: (Show a, Eq a, Desugar_Agda a) => Der a -> Der a
flatten_der d =
  case steps of
    [] -> refl v w
    otherwise -> aux steps'
  where
    (steps0, v, w) = flatten_der_aux d
    steps = straighten_der steps0
    steps' = add_reflexivities v steps w
    d0 = head steps
    dn = last steps
    Eqn v' _ = eqn_of_der d0
    Eqn _ w' = eqn_of_der dn
    aux [d] = d
    aux (h:t) = trans h (aux t)

-- | Take a sequence of steps, and add explicit reflexivity steps
-- wherever the conclusion of one step is not literally the premise of
-- the next one.
add_reflexivities :: (Eq a, Show a, Desugar_Agda a) => [a] -> [Der a] -> [a] -> [Der a]
add_reflexivities v [] w
  | v == w = []
  | otherwise = Refl v w : []
add_reflexivities v (d:ds) w
  | v == d1 = d : add_reflexivities d2 ds w
  | otherwise = Refl v d1 : d : add_reflexivities d2 ds w
  where
    Eqn d1 d2 = eqn_of_der d
    

-- ----------------------------------------------------------------------
-- ** Remove loops in derivations

data Graph e v = Vertex v | Edge (Graph e v) e v
  deriving (Show)

-- | For testing.
graph_of_list :: [a] -> Graph Integer a
graph_of_list [] = error "graph_of_list"
graph_of_list [x] = Vertex x
graph_of_list (h:t) = Edge (graph_of_list t) 0 h

-- | Remove loops (repeated vertices) from a directed linear graph,
-- finding the shortest path. Linear time.
remove_loops :: (Ord v) => Graph e v -> Graph e v
remove_loops g = graph
  where
    -- | Find the shortest path to any vertex. For efficiency, also
    -- return the rightmost vertex of the graph.
    aux :: (Ord v) => Graph e v -> (v, Map v (Integer, Graph e v))
    aux (Vertex v) = (v, Map.singleton v (0, Vertex v))
    aux (Edge g e v) =
      case Map.lookup v m of
        Nothing -> (v, Map.insert v (n+1, Edge g' e v) m)
        Just (k, g'') ->
          if k >= n+1 then
            (v, Map.insert v (n+1, Edge g' e v) m)
          else
            (v, m)
      where
        (w, m) = aux g
        Just (n, g') = Map.lookup w m

    (v, map) = aux g
    Just (n, graph) = Map.lookup v map

-- | Remove loops from a flattened derivation.
straighten_der :: (Show a, Desugar_Agda a, Eq a) => [Der a] -> [Der a]
straighten_der [] = []
straighten_der ders = ders_of_graph (remove_loops (graph_of_ders ders))

graph_of_ders :: (Show a, Desugar_Agda a, Eq a) => [Der a] -> Graph (Der a) [Gate]
graph_of_ders [] = error "graph_of_ders"
graph_of_ders [der] = Edge (Vertex w') der v'
  where
    Eqn v w = eqn_of_der der
    v' = desugar_agda v
    w' = desugar_agda w
graph_of_ders (der:ders) = Edge g der v'
  where
    g = graph_of_ders ders
    Eqn v w = eqn_of_der der
    v' = desugar_agda v

ders_of_graph :: Graph (Der a) v -> [Der a]
ders_of_graph (Vertex r) = []
ders_of_graph (Edge g der v) = der : ders_of_graph g

-- ----------------------------------------------------------------------
-- ** Agda output

class ToAgda a where
  to_agda :: a -> String

instance ToAgda Pauli2 where
  to_agda (Pauli2 s p q) = "(" ++ to_agda s ++ " , " ++ to_agda p ++ "⊗" ++ to_agda q ++ ")"

instance ToAgda Gate where
  to_agda (R pauli) = "R " ++ to_agda pauli
  to_agda S0inv = "S0⁻¹"
  to_agda S1inv = "S1⁻¹"
  to_agda T0inv = "T0⁻¹"
  to_agda T1inv = "T1⁻¹"
  to_agda (Omega 1) = "W"
  to_agda (Omega 7) = "W⁻¹"
  to_agda (Omega n) = "W ^ " ++ show n
  to_agda Swap = "Swap"
  to_agda g = show g

instance (ToAgda a) => ToAgda [a] where
  to_agda [] = "ε"
  to_agda (g:gs) = to_agda g ++ " • " ++ to_agda gs

instance (ToAgda a, ToAgda b) => ToAgda (a,b) where
  to_agda (a,b) = "(" ++ to_agda a ++ " , " ++ to_agda b ++ ")"

instance (ToAgda a, ToAgda b, ToAgda c) => ToAgda (a,b,c) where
  to_agda (a,b,c) = "(" ++ to_agda a ++ " , " ++ to_agda b ++ " , " ++ to_agda c ++ ")"

instance ToAgda Sign where
  to_agda Plus = "plus"
  to_agda Minus = "minus"

instance ToAgda Pauli where
  to_agda = show

to_agda_clifford_gate :: Gate -> String
to_agda_clifford_gate g = "C." ++ to_agda g

to_agda_clifford :: [Gate] -> String
to_agda_clifford [] = "ε"
to_agda_clifford [g] = to_agda_clifford_gate g
to_agda_clifford (g:gs) = to_agda_clifford_gate g ++ " • " ++ to_agda_clifford gs

to_agda_pauli :: Pauli2 -> String
to_agda_pauli (Pauli2 s p q) = "(" ++ to_agda s ++ " , " ++ to_agda p ++ "⊗" ++ to_agda q ++ ")"

-- | Input a derivation and convert it to an Agda proof of itself. Try
-- to be readable.
to_agda_der :: (Show a, Eq a, Desugar_Agda a, ToAgda a) => Der a -> String -> String
to_agda_der der name = dec ++ def
  where
    Eqn v w = if check_der der then eqn_of_der der else error "to_agda_der"
    dec = name ++ " : " ++ typ ++ "\n"
    def = name ++ " = " ++ "\n" ++ proof ++ "\n"
    typ = "Δ ⊢ " ++ lhs ++ " === " ++ rhs
    lhs = to_agda v
    rhs = to_agda w
    comment v = " -- " ++ to_agda v ++ "\n"
    proof = "  equational " ++ to_agda v ++ "\n" ++ aux_top der

    aux_top (Trans d1 d2 v w) = step d1 ++ aux_top d2
    aux_top der = step der

    step der = 
         "          by " ++ aux der ++ "\n"
      ++ "      equals " ++ to_agda u ++ "\n"
      where
        Eqn _ u = eqn_of_der der

    aux (Refl v w) = "general-assoc auto"
    aux (Symm d) = "symm (" ++ aux d ++ ")"
    aux (Trans d1 d2 v w) = "trans (" ++ aux d1 ++ ") (" ++ aux d2 ++ ")"
    aux (Cong a (Tactic ByClifford eqn) b) = "clifford-tactic " ++ show n ++ " " ++ show m ++ " " ++ show 10000 ++ " auto"
      where
        n = length a
        m = length d1
        Eqn d1 d2 = eqn
    aux (Cong a (Lemma name eqn) b) = "in-context " ++ show n ++ " " ++ show m ++ " auto " ++ paren (elem ' ' name) name
      where
        n = length a
        m = length d1
        Eqn d1 d2 = eqn
        paren True s = "(" ++ s ++ ")"
        paren False s = s
    aux (Cong a (Symm (Lemma name eqn)) b) = "in-context " ++ show n ++ " " ++ show m ++ " auto (symm " ++ paren (elem ' ' name) name ++ ")"
      where
        n = length a
        m = length d2
        Eqn d1 d2 = eqn
        paren True s = "(" ++ s ++ ")"
        paren False s = s
    aux (Cong a d b) = "general-context " ++ show n ++ " " ++ show m ++ " auto (" ++ aux d ++ ")"
      where
        n = length a
        m = length d1
        Eqn d1 d2 = eqn_of_der d
    aux (Lemma name eq) = aux (Cong [] (Lemma name eq) [])
      where
        paren True s = "(" ++ s ++ ")"
        paren False s = s
    aux (Tactic ByClifford eq) = aux (Cong [] (Tactic ByClifford eq) [])

print_der :: (Show a, Eq a, Desugar_Agda a, ToAgda a) => Der a -> String -> IO ()
print_der der name = do
  putStrLn (to_agda_der (flatten_der der) name)

-- | Print a derivation by breaking it up into lemmas, one for each step.
print_der_stepwise :: (Show a, Eq a, Desugar_Agda a, ToAgda a) => Der a -> String -> IO ()
print_der_stepwise der name = do
  let (ds, _, _) = flatten_der_aux der
  sequence_ [ aux d n | (d,n) <- zip ds [1..] ]
  where
    aux d n = do
      putStrLn (to_agda_der d (name ++ "-" ++ show n))

-- | Output prototypes for all of the lemmas used by a proof.
get_lemmas_aux :: Der a -> Map String (Eqn [a])
get_lemmas_aux (Refl u v) = Map.empty
get_lemmas_aux (Symm d) = get_lemmas_aux d
get_lemmas_aux (Trans d1 d2 v w) = Map.union (get_lemmas_aux d1) (get_lemmas_aux d2)
get_lemmas_aux (Cong a d b) = get_lemmas_aux d
get_lemmas_aux (Lemma name eq) = Map.singleton name eq
get_lemmas_aux (Tactic name eq) = Map.empty

get_lemmas :: (ToAgda a) => Der a -> String
get_lemmas d = unlines (concat [ format_lemma name eq | (name, eq) <- Map.toList lems ])
  where
    lems = get_lemmas_aux d
    format_lemma name (Eqn lhs rhs) = [
      name ++ " : Δ ⊢ " ++ to_agda lhs ++ " === " ++ to_agda rhs,
      name ++ " = ?",
      ""
      ]

-- | Output prototypes for all of the lemmas used by a proof.
print_lemmas :: (ToAgda a) => Der a -> IO ()
print_lemmas der = do
  putStrLn (get_lemmas der)

-- ----------------------------------------------------------------------
-- * Useful general-purpose functions

-- | Repeatedly apply a one-step reduction until it's done.
repeatedly :: (a -> Maybe a) -> (a -> a)
repeatedly f a = case f a of
  Nothing -> a
  Just b -> repeatedly f b

-- | Like 'repeatedly', but with evidence.
repeatedly_der :: (Show a, Desugar_Agda a, Eq a) => ([a] -> Maybe ([a], Der a)) -> ([a] -> ([a], Der a))
repeatedly_der f a = case f a of
  Nothing -> (a, refl a a)
  Just (b, der1) ->
    let (c, der2) = repeatedly_der f b
    in
      (c, trans der1 der2)

-- | Apply one or more one-step reductions until it's done. If no
-- one-step reduction applies, return Nothing.
maybe_repeatedly :: (a -> Maybe a) -> (a -> Maybe a)
maybe_repeatedly f a = case f a of
  Nothing -> Nothing
  Just b -> Just (repeatedly f b)

-- | Like 'maybe_repeatedly', but with evidence.
maybe_repeatedly_der :: (Show a, Desugar_Agda a, Eq a) => ([a] -> Maybe ([a], Der a)) -> ([a] -> Maybe ([a], Der a))
maybe_repeatedly_der f a = case f a of
  Nothing -> Nothing
  Just (b, der1) ->
    let (c, der2) = repeatedly_der f b
    in
      Just (c, trans der1 der2)

-- | Return the longest common prefix of two lists, as well as the remainders.
common_prefix :: (Eq a) => [a] -> [a] -> ([a], [a], [a])
common_prefix (h:t) (h':t')
  | h == h' = (h : pre, lhs, rhs)
  where
    (pre, lhs, rhs) = common_prefix t t'
common_prefix l1 l2 = ([], l1, l2)

-- | Return the longest common postfix of two lists, as well as the remainders.
common_postfix :: (Eq a) => [a] -> [a] -> ([a], [a], [a])
common_postfix l1 l2 = (reverse lhs, reverse rhs, reverse pre)
  where
    (pre, lhs, rhs) = common_prefix (reverse l1) (reverse l2)

-- | Given two lists l1 and l2, find (pre, lhs, rhs, post) such that
-- l1 == pre ++ lhs ++ post and
-- l2 == pre ++ rhs ++ post,
-- and such that lhs and rhs are as short as possible.
find_context :: (Eq a) => [a] -> [a] -> ([a], [a], [a], [a])
find_context l1 l2 = (pre, lhs, rhs, post)
  where
    (pre, t1, t2) = common_prefix l1 l2
    (lhs, rhs, post) = common_postfix t1 t2

-- | A general list-to-string function. Example:
--
-- > string_of_list "{" ", " "}" "{}" show [1,2,3] = "{1, 2, 3}"
string_of_list :: String -> String -> String -> String -> (t -> String) -> [t] -> String
string_of_list lpar comma rpar nil string_of_elt lst =
  let string_of_tail lst =
        case lst of
          [] -> ""
          h:t -> comma ++ string_of_elt h ++ string_of_tail t
  in
   case lst of
     [] -> nil
     h:t -> lpar ++ string_of_elt h ++ string_of_tail t ++ rpar

-- | Print a list, one element per line.
print_list :: (Show a) => [a] -> IO ()
print_list as = sequence_ [ putStrLn (show a) | a <- as ]

-- ----------------------------------------------------------------------
-- * Pauli operators

-- | Pauli operators.
data Pauli = I | X | Y | Z
           deriving (Eq, Show, Ord)

-- | Signs for Pauli operators.
data Sign = Plus | Minus
           deriving (Eq, Show, Ord)

-- | Negation.
neg :: Sign -> Sign
neg Plus = Minus
neg Minus = Plus

-- | Multiplication of signs.
sign_mult :: Sign -> Sign -> Sign
sign_mult Plus s = s
sign_mult Minus s = neg s

-- | Check whether two Pauli operators commute. Return +1 if they do
-- and -1 if they don't.
commute_pauli :: Pauli -> Pauli -> Sign
commute_pauli I _ = Plus
commute_pauli _ I = Plus
commute_pauli p q = if p == q then Plus else Minus

-- | 2-qubit signed Pauli operators.
data Pauli2 = Pauli2 Sign Pauli Pauli
  deriving (Show, Eq)

instance Ord Pauli2 where
  Pauli2 s p q <= Pauli2 s' p' q' = (p,q,s) <= (p',q',s')

-- ----------------------------------------------------------------------
-- * Representation of 2-qubit Clifford+/T/ circuits by syllables

-- | Basic gates. Note: circuits are represented as lists of 'Gate's, and
-- for this project, they are to be read in /matrix order/, i.e.,
-- right-to-left is past-to-future.
data Gate =
  R Pauli2    -- ^ /B/_{±/P/ x /Q/}.
  | ZZ          -- ^ Controlled /Z/.
  | CX0         -- ^ Controlled /X0/.
  | CX1         -- ^ Controlled /X1/.
  | CH0         -- ^ Controlled /H0/.
  | CH1         -- ^ Controlled /H1/.
  | CS          -- ^ Controlled /S/.
  | Swap        -- ^ Swap gate.
  | H0          -- ^ /H/ x /I/.
  | H1          -- ^ /I/ x /H/.
  | S0          -- ^ /S/ x /I/.
  | S1          -- ^ /I/ x /S/.
  | S0inv       -- ^ /S/ x /I/ inverse.
  | S1inv       -- ^ /I/ x /S/ inverse.
  | T0          -- ^ /T/ x /I/.
  | T1          -- ^ /I/ x /T/.
  | T0inv       -- ^ /T/ x /I/ inverse.
  | T1inv       -- ^ /I/ x /T/ inverse.
  | X0          -- ^ /X/ x /I/.
  | X1          -- ^ /I/ x /X/.
  | Omega Int   -- ^ omega^/k/.
  deriving (Show, Eq, Ord)

-- | A convenient abbreviation for the omega gate.
w :: Gate
w = Omega 1

-- | A convenient abbreviation for the inverse of the omega gate.
winv :: Gate
winv = Omega 7

-- | Check whether a gate is Clifford.
isClifford :: Gate -> Bool
isClifford (R pauli) = False
isClifford T0 = False
isClifford T1 = False
isClifford T0inv = False
isClifford T1inv = False
isClifford CH0 = False
isClifford CH1 = False
isClifford CS = False
isClifford g = True

-- | Return the definition of R pauli.
rsyll_def :: Pauli2 -> [Gate]
rsyll_def pauli = c ++ [T0] ++ invert c
  where
    c = desugar_agda $ conjugator pauli

-- | Like 'rsyll_def', but with witness. Should be reflexivity.
rsyll_def_der :: Pauli2 -> ([Gate], Der Gate)
rsyll_def_der pauli = (g, refl [R pauli] g)
  where
    g = rsyll_def pauli

-- | The inverse of a Clifford+/T/ gate.
invert_gate :: Gate -> [Gate]
invert_gate (R pauli) = invert (rsyll_def pauli)
invert_gate ZZ = [ZZ]
invert_gate CX0 = [CX0]
invert_gate CX1 = [CX1]
invert_gate CH0 = [CH0]
invert_gate CH1 = [CH1]
invert_gate CS = [CS, CS, CS]
invert_gate Swap = [Swap]
invert_gate H0 = [H0]
invert_gate H1 = [H1]
invert_gate S0 = [S0inv]
invert_gate S1 = [S1inv]
invert_gate S0inv = [S0]
invert_gate S1inv = [S1]
invert_gate T0 = [T0inv]
invert_gate T1 = [T1inv]
invert_gate T0inv = [T0]
invert_gate T1inv = [T1]
invert_gate X0 = [X0]
invert_gate X1 = [X1]
invert_gate (Omega k) = [Omega (8-k)]

-- | The inverse of a Clifford+/T/ gate, with witness.
-- 'invert_gate_der' a returns (b,d1,d2), b is the inverse of a, d1 is
-- a derivation of ab=1, and d2 is a derivation of ba=1. This is only
-- needed for non-Clifford gates.
invert_gate_der :: Gate -> ([Gate], Der Gate, Der Gate)
invert_gate_der CH0 = ([CH0], Lemma "order-CH0" (Eqn [CH0,CH0] []), Lemma "order-CH0" (Eqn [CH0,CH0] []))
invert_gate_der CH1 = ([CH1], Lemma "order-CH1" (Eqn [CH1,CH1] []), Lemma "order-CH1" (Eqn [CH1,CH1] []))
invert_gate_der CS = ([CS], Lemma "order-CS" (Eqn [CS,CS] []), Lemma "order-CS" (Eqn [CS,CS] []))
invert_gate_der T0 = ([T0inv], Lemma "order-T0" (Eqn (replicate 8 T0) []), Lemma "order-T0" (Eqn (replicate 8 T0) []))
invert_gate_der T1 = ([T1inv], Lemma "order-T1" (Eqn (replicate 8 T1) []), Lemma "order-T1" (Eqn (replicate 8 T1) []))
invert_gate_der T0inv = ([T0], Lemma "order-T0" (Eqn (replicate 8 T0) []), Lemma "order-T0" (Eqn (replicate 8 T0) []))
invert_gate_der T1inv = ([T1], Lemma "order-T1" (Eqn (replicate 8 T1) []), Lemma "order-T1" (Eqn (replicate 8 T1) []))
invert_gate_der (R pauli) = (circ, d4, d5)
  where
    (g, d1) = rsyll_def_der pauli
    (circ, d2, d3) = invert_der g
    d4 = trans (Cong [] d1 circ) d2
    d5 = trans (Cong circ d1 []) d3
invert_gate_der g = error "invert_gate_der applied to a Clifford gate"

-- | The inverse of a circuit.
invert :: [Gate] -> [Gate]
invert circ = concat $ reverse $ map invert_gate circ

-- | Like 'invert', but with witness. If (xinv, d, e) = invert_der x, then
--
-- > d : x • xinv === ε
-- > e : xinv • x === ε
invert_der :: [Gate] -> ([Gate], Der Gate, Der Gate)
invert_der [] = ([], refl [] [], refl [] [])
invert_der (g:gs)
  | isClifford g = (g2inv ++ g1inv, f1, f2)
  where
    (g1, g2) = span isClifford (g:gs)
    g1inv = invert g1
    d1 = by_clifford (g1 ++ g1inv) []
    -- d1 : g1 • g1inv === ε
    d2 = by_clifford (g1inv ++ g1) []
    -- d2 : g1inv • g1 === ε
    (g2inv, e1, e2) = invert_der g2
    -- e1 : g2 • g2inv === ε
    -- e2 : g2inv • g2 === ε
    f1 = trans (Cong g1 e1 g1inv) d1
    -- f1 : g1 • g2 • g2inv • g1inv === g1 • g1inv === ε
    f2 = trans (Cong g2inv d2 g2) e2
    -- f1 : g2inv • g1inv • g1 • g2 === g2inv • g2 === ε

invert_der (g:gs) = (gs' ++ g', f1, f2)
  where
    (g', d1, d2) = invert_gate_der g
    -- d1 : g • g' === ε
    -- d2 : g' • g === ε
    (gs', e1, e2) = invert_der gs
    -- e1 : gs • gs' === ε
    -- e2 : gs' • gs === ε
    f1 = trans (Cong [g] e1 g') d1
    -- f1 : g • gs • gs' • g' === g • g' === ε
    f2 = trans (Cong gs' d2 gs) e2
    -- f1 : gs' • g' • g • gs === gs' • gs === ε


-- | Conjugate a gate with Swap on both sides.
swap_gate :: Gate -> Gate
swap_gate (R (Pauli2 sign p q)) = R (Pauli2 sign q p)
swap_gate T0 = T1
swap_gate ZZ = ZZ
swap_gate CX0 = CX1
swap_gate CX1 = CX0
swap_gate CH0 = CH1
swap_gate CH1 = CH0
swap_gate CS = CS
swap_gate Swap = Swap
swap_gate H0 = H1
swap_gate H1 = H0
swap_gate S0 = S1
swap_gate S1 = S0
swap_gate S0inv = S1inv
swap_gate S1inv = S0inv
swap_gate T1 = T0
swap_gate T0inv = T1inv
swap_gate T1inv = T0inv
swap_gate X0 = X1
swap_gate X1 = X0
swap_gate (Omega n) = Omega n

-- | Given a signed 2-qubit Pauli operator /P/, return a (fixed but
-- arbitrary choice of a) Clifford operator /C/ such that
--
-- /C/(/Z/ x /I/)/C/^{-1} = /P/
conjugator :: Pauli2 -> [Gate]
conjugator (Pauli2 Plus I I) = error "conjugator"
conjugator (Pauli2 Plus Z I) = []
conjugator (Pauli2 Plus X I) = [H0]
conjugator (Pauli2 Plus Y I) = [S0, H0]
conjugator (Pauli2 Plus I Z) = [Swap]
conjugator (Pauli2 Plus Z Z) = [H0, ZZ, H0]
conjugator (Pauli2 Plus X Z) = [ZZ, H0]
conjugator (Pauli2 Plus Y Z) = [S0, ZZ, H0]
conjugator (Pauli2 Plus I X) = [H1, Swap]
conjugator (Pauli2 Plus Z X) = [H1, H0, ZZ, H0]
conjugator (Pauli2 Plus X X) = [H1, ZZ, H0]
conjugator (Pauli2 Plus Y X) = [H1, S0, ZZ, H0]
conjugator (Pauli2 Plus I Y) = [S1, H1, Swap]
conjugator (Pauli2 Plus Z Y) = [S1, H1, H0, ZZ, H0]
conjugator (Pauli2 Plus X Y) = [S1, H1, ZZ, H0]
conjugator (Pauli2 Plus Y Y) = [S1, H1, S0, ZZ, H0]
conjugator (Pauli2 Minus p q) = conjugator (Pauli2 Plus p q) ++ [X0]

-- | Translate to a minimal set of generators: {ZZ, Swap, H0, S0, T0,
-- omega^k}.  This is not intended to be used in formal proofs (say
-- Agda output), but is convenient for certain other purposes, like
-- converting gates to matrices, and computing actions.
desugar :: Gate -> [Gate]
desugar (R pauli) = desugar_gates (c ++ [T0] ++ invert c)
  where
    c = conjugator pauli
desugar CX0 = desugar_gates [H0, ZZ, H0]
desugar CX1 = desugar_gates [H1, ZZ, H1]
desugar CH0 = desugar_gates [S0, H0, T0, CX0, T0inv, H0, S0inv]
desugar CH1 = desugar_gates [S1, H1, T1, CX1, T1inv, H1, S1inv]
desugar CS = desugar_gates [T0, T1, CX0, T0inv, CX0]
desugar H1 = desugar_gates [Swap, H0, Swap]
desugar S1 = desugar_gates [Swap, S0, Swap]
desugar T1 = desugar_gates [Swap, T0, Swap]
desugar X0 = desugar_gates [H0, S0, S0, H0]
desugar X1 = desugar_gates [H1, S1, S1, H1]
desugar S0inv = desugar_gates [S0, S0, S0]
desugar S1inv = desugar_gates [S1, S1, S1]
desugar T0inv = desugar_gates [T0, S0inv]
desugar T1inv = desugar_gates [T1, S1inv]
desugar x = [x]

-- | Translate a circuit to a minimal set of generators: {ZZ, Swap,
-- H0, S0, T0, omega}.
desugar_gates :: [Gate] -> [Gate]
desugar_gates circ = concat [ desugar x | x <- circ ]

-- | Calculate a power of 'T1', using no more than one actual 'T'-gate.
powerT1 :: Int -> [Gate]
powerT1 m | m < 0 || m > 7 = powerT1 (m `mod` 8)
powerT1 0 = []
powerT1 1 = [T1]
powerT1 2 = [S1]
powerT1 3 = [S1, T1]
powerT1 4 = [S1, S1]
powerT1 5 = [S1, S1, T1]
powerT1 6 = [S1inv]
powerT1 7 = [T1inv]

-- | Calculate a power of 'T0', using no more than one actual 'T'-gate.
powerT0 :: Int -> [Gate]
powerT0 m = [Swap] ++ powerT1 m ++ [Swap]

-- ----------------------------------------------------------------------
-- * Convert syllable representation to matrix

-- | Turn a gate into a matrix.
matrix_of_gate :: Gate -> Matrix Four Four DOmega
matrix_of_gate ZZ = matrix4x4 (1, 0, 0,  0)
                              (0, 1, 0,  0)
                              (0, 0, 1,  0)
                              (0, 0, 0, -1)
matrix_of_gate Swap = matrix4x4 (1, 0, 0, 0)
                                (0, 0, 1, 0)
                                (0, 1, 0, 0)
                                (0, 0, 0, 1)
matrix_of_gate H0 = h `tensor` id
  where
    h = roothalf * matrix2x2 (1,  1)
                             (1, -1)
    id = 1 :: Matrix Two Two DOmega
matrix_of_gate S0 = s `tensor` id
  where
    s = matrix2x2 (1, 0)
                  (0, i)
    id = 1 :: Matrix Two Two DOmega
matrix_of_gate T0 = t `tensor` id
  where
    t = matrix2x2 (1, 0)
                  (0, omega)
    id = 1 :: Matrix Two Two DOmega
matrix_of_gate (Omega k) = omega^k
matrix_of_gate x = matrix_of_gates (desugar x)

-- | Turn a circuit into a matrix. Note: a circuit is a list of gates
-- and is read from right to left for this project.
matrix_of_gates :: [Gate] -> Matrix Four Four DOmega
matrix_of_gates [] = 1
matrix_of_gates (h:t) = (matrix_of_gate h) * (matrix_of_gates t)

-- ----------------------------------------------------------------------
-- * Convert matrix to symbolic representation

-- | Input a 2-qubit circuit that performs a 2-level operation on
-- levels 2 and 3 (i.e., an operation on the second qubit controlled
-- by the first qubit). Also input two levels /j/ and /k/. Output a
-- modified circuit that applies the given operation to levels /j/ and
-- /k/ instead of 2 and 3. We don't really use a \"Gray code\", but
-- this is a Gray-code-like operation.
graycode2 :: [Gate] -> Int -> Int -> [Gate]
graycode2 circ 0 1 = [X0] ++ circ ++ [X0]
graycode2 circ 0 2 = [Swap, X0] ++ circ ++ [X0, Swap]
graycode2 circ 0 3 = [CX0, X0] ++ circ ++ [X0, CX0]
graycode2 circ 1 2 = [CX0, X1] ++ circ ++ [X1, CX0]
graycode2 circ 1 3 = [Swap] ++ circ ++ [Swap]
graycode2 circ 2 3 = circ
graycode2 circ j k | k < j = graycode2 ([X1] ++ circ ++ [X1]) k j

-- | Input a 2-qubit circuit that performs a 1-level operation on
-- level 3. Also input a level /j/. Output a new circuit that applies
-- the same operation to level /j/ instead of 3.
graycode1 :: [Gate] -> Int -> [Gate]
graycode1 circ 0 = [X0, X1] ++ circ ++ [X0, X1]
graycode1 circ 1 = [X0] ++ circ ++ [X0]
graycode1 circ 2 = [X1] ++ circ ++ [X1]
graycode1 circ 3 = circ

-- | Convert a 'TwoLevelAlt' operation to a circuit.
gates_from_twolevelalt :: TwoLevelAlt -> [Gate]
gates_from_twolevelalt (TL_iX j k) = graycode2 [S0, CX1] j k
gates_from_twolevelalt (TL_TiHT m j k) = graycode2 circ j k
  where
    circ = powerT1 (-m) ++ ciH ++ powerT1 m
    ciH = [S1inv, H1, T1inv, S0, CX1, T1, H1, S1]
gates_from_twolevelalt (TL_W m j k) = graycode2 circ j k
  where
    circ = [CX1] ++ powerT1 m ++ [CX1] ++ powerT1 (-m)
gates_from_twolevelalt (TL_omega_alt m j) = graycode1 circ j
  where
    circ = if m `mod` 2 == 1 then
             error "gates_from_twolevelalt: determinant"
           else
             let k = m `div` 2 in
             powerT0 k ++ powerT1 k ++ [CX1] ++ powerT1 (-k) ++ [CX1]


-- | Convert a list of 'TwoLevelAlt' operations to a circuit. Note:
-- both 'TwoLevelAlt' operations and 'Gate' operations are written in
-- matrix multiplication order.
gates_from_twolevelalts :: [TwoLevelAlt] -> [Gate]
gates_from_twolevelalts ops = concat [ gates_from_twolevelalt x | x <- ops ]

-- | Convert a 4x4-matrix to a symbolic circuit.
gates_of_matrix :: Matrix Four Four DOmega -> [Gate]
gates_of_matrix = gates_from_twolevelalts . synthesis_nqubit_alt

-- ----------------------------------------------------------------------
-- * Pauli actions

-- | Action of Clifford gates on the Pauli operators.
-- Given C and P, compute CPC^{-1}.
action :: Gate -> Pauli2 -> Pauli2
action T0 _ = error "action: not a Clifford gate"
action H0 (Pauli2 sign I p) = (Pauli2 sign I p)
action H0 (Pauli2 sign X p) = (Pauli2 sign Z p)
action H0 (Pauli2 sign Y p) = (Pauli2 (neg sign) Y p)
action H0 (Pauli2 sign Z p) = (Pauli2 sign X p)
action S0 (Pauli2 sign I p) = (Pauli2 sign I p)
action S0 (Pauli2 sign X p) = (Pauli2 sign Y p)
action S0 (Pauli2 sign Y p) = (Pauli2 (neg sign) X p)
action S0 (Pauli2 sign Z p) = (Pauli2 sign Z p)
action Swap (Pauli2 sign p q) = (Pauli2 sign q p)
action ZZ (Pauli2 sign I I) = (Pauli2 sign I I)
action ZZ (Pauli2 sign X I) = (Pauli2 sign X Z)
action ZZ (Pauli2 sign Y I) = (Pauli2 sign Y Z)
action ZZ (Pauli2 sign Z I) = (Pauli2 sign Z I)
action ZZ (Pauli2 sign I X) = (Pauli2 sign Z X)
action ZZ (Pauli2 sign X X) = (Pauli2 sign Y Y)
action ZZ (Pauli2 sign Y X) = (Pauli2 (neg sign) X Y)
action ZZ (Pauli2 sign Z X) = (Pauli2 sign I X)
action ZZ (Pauli2 sign I Y) = (Pauli2 sign Z Y)
action ZZ (Pauli2 sign X Y) = (Pauli2 (neg sign) Y X)
action ZZ (Pauli2 sign Y Y) = (Pauli2 sign X X)
action ZZ (Pauli2 sign Z Y) = (Pauli2 sign I Y)
action ZZ (Pauli2 sign I Z) = (Pauli2 sign I Z)
action ZZ (Pauli2 sign X Z) = (Pauli2 sign X I)
action ZZ (Pauli2 sign Y Z) = (Pauli2 sign Y I)
action ZZ (Pauli2 sign Z Z) = (Pauli2 sign Z Z)
action (Omega k) op = op
action gate op = actions (desugar gate) op

-- | Action of Clifford circuits on the Pauli operators.
-- Given C and P, compute CPC^{-1}.
actions :: [Gate] -> Pauli2 -> Pauli2
actions [] = id
actions (h:t) = action h . actions t

-- | Like actions, but also return a derivation of C • R_{P} = R_{P'} • C,
-- where C P = P' C.  Leave the actual work of the proof to Agda.
actions_der :: [Gate] -> Pauli2 -> (Pauli2, Der Gate)
actions_der c p = (p', der)
  where
    p' = actions c p
    der = Lemma ("lemma-R (" ++ to_agda_clifford c ++ ") " ++ to_agda_pauli p) (Eqn (c ++ [R p]) ([R p'] ++ c))

-- | Given p and q, output g such that R(Pauli2 Minus p q) === R(Pauli2 Plus p q) • g.
r_correction :: Pauli -> Pauli -> [Gate]
r_correction p q = g
  where
    c = conjugator (Pauli2 Plus p q)
    g = c ++ [S0inv, w] ++ invert c

-- | Like 'r_correction', but with witness.
r_correction_der :: Pauli -> Pauli -> ([Gate], Der Gate)
r_correction_der p q = (g, der)
  where
    g = r_correction p q
    der = Lemma ("lemma-correction " ++ to_agda p ++ "⊗" ++ to_agda q) (Eqn [R (Pauli2 Minus p q)] ([R (Pauli2 Plus p q)] ++ g))

-- | Convert a Pauli operator to channel representation, using only
-- positive channels.
rsyll_pos :: Pauli2 -> [Gate]
rsyll_pos (Pauli2 Plus p q) = [R (Pauli2 Plus p q)]
rsyll_pos (Pauli2 Minus p q) = [R (Pauli2 Plus p q)] ++ r_correction p q

-- | Like 'rsyll_pos', but with witness, i.e., a proof that R pauli === rsyll_pos pauli
rsyll_pos_der :: Pauli2 -> ([Gate], Der Gate)
rsyll_pos_der (Pauli2 Plus p q) = ([R (Pauli2 Plus p q)], refl [R (Pauli2 Plus p q)] [R (Pauli2 Plus p q)])
rsyll_pos_der (Pauli2 Minus p q) = ([R (Pauli2 Plus p q)] ++ corr, der)
  where
    (corr, der) = r_correction_der p q

-- ----------------------------------------------------------------------
-- * Simplify Clifford operators

-- | Apply one of a finite number of rewrite rules to simplify the
-- Clifford part of a circuit. Return 'Nothing' if the circuit is
-- already normal. We use 'ZZ', 'H0', 'S0', 'H1', 'S1', and 'Omega' as
-- the generators; other Clifford gates must already be desugared or
-- they will not be simplified.  The rules below implement a confluent
-- and terminating rewrite system.
peephole_clifford :: [Gate] -> Maybe [Gate]

-- Rules for Omega.
peephole_clifford (Omega 0:t) = Just t
peephole_clifford (Omega k:Omega l:t) = Just (Omega (k+l):t)
peephole_clifford (Omega k:t) | k < 0 || k >= 8 = Just (Omega (k `mod` 8):t)
peephole_clifford (Omega k:h:t) = Just (h:Omega k:t)

-- Commuting rules for unary gates.
peephole_clifford (H1:H0:t) = Just (H0:H1:t)
peephole_clifford (H1:S0:t) = Just (S0:H1:t)
peephole_clifford (S1:H0:t) = Just (H0:S1:t)
peephole_clifford (S1:S0:t) = Just (S0:S1:t)

-- Rules for unary gates.
peephole_clifford (H0:H0:t) = Just t
peephole_clifford (S0:S0:S0:S0:t) = Just t
peephole_clifford (S0:H0:S0:H0:t) = Just (H0:S0:S0:S0:Omega 1:t)
peephole_clifford (H0:S0:H0:S0:t) = Just (S0:S0:S0:H0:Omega 1:t)
peephole_clifford (H0:S0:S0:S0:H0:t) = Just (S0:H0:S0:Omega (-1):t)
peephole_clifford (S0:H0:S0:S0:H0:S0:t) = Just (H0:S0:S0:H0:Omega 2:t)
peephole_clifford (H0:S0:S0:H0:S0:S0:t) = Just (S0:S0:H0:S0:S0:H0:Omega 4:t)
peephole_clifford (S0:S0:S0:H0:S0:S0:H0:t) = Just (H0:S0:S0:H0:S0:Omega (-2):t)
peephole_clifford (S0:S0:S0:H0:S0:S0:S0:t) = Just (H0:S0:H0:Omega (-1):t)

peephole_clifford (H1:H1:t) = Just t
peephole_clifford (S1:S1:S1:S1:t) = Just t
peephole_clifford (S1:H1:S1:H1:t) = Just (H1:S1:S1:S1:Omega 1:t)
peephole_clifford (H1:S1:H1:S1:t) = Just (S1:S1:S1:H1:Omega 1:t)
peephole_clifford (H1:S1:S1:S1:H1:t) = Just (S1:H1:S1:Omega (-1):t)
peephole_clifford (S1:H1:S1:S1:H1:S1:t) = Just (H1:S1:S1:H1:Omega 2:t)
peephole_clifford (H1:S1:S1:H1:S1:S1:t) = Just (S1:S1:H1:S1:S1:H1:Omega 4:t)
peephole_clifford (S1:S1:S1:H1:S1:S1:H1:t) = Just (H1:S1:S1:H1:S1:Omega (-2):t)
peephole_clifford (S1:S1:S1:H1:S1:S1:S1:t) = Just (H1:S1:H1:Omega (-1):t)

-- Rules for ZZ.
peephole_clifford (ZZ:ZZ:t) = Just t

peephole_clifford (S1:ZZ:t) = Just (ZZ:S1:t)
peephole_clifford (S0:ZZ:t) = Just (ZZ:S0:t)
peephole_clifford (S0:H1:ZZ:t) = Just (H1:ZZ:S0:t)
peephole_clifford (S0:S1:H1:ZZ:t) = Just (S1:H1:ZZ:S0:t)

peephole_clifford (S1:S1:H1:ZZ:t) = Just (H1:ZZ:S0:S0:H1:S1:S1:H1:t)
peephole_clifford (S0:S0:H0:ZZ:t) = Just (H0:ZZ:H0:S0:S0:H0:S1:S1:t)
peephole_clifford (S0:S0:H0:H1:ZZ:t) = Just (H0:H1:ZZ:H0:S0:S0:H0:S1:S1:t)
peephole_clifford (S0:S0:H0:S1:H1:ZZ:t) = Just (H0:S1:H1:ZZ:H0:S0:S0:H0:S1:S1:t)

peephole_clifford (H1:S1:H1:ZZ:t) = Just (S1:H1:ZZ:S0:S0:S1:H1:S1:S1:H1:Omega (-1):t)
peephole_clifford (H0:S0:H0:ZZ:t) = Just (S0:H0:ZZ:S0:H0:S0:S0:H0:S1:S1:Omega (-1):t)
peephole_clifford (H0:S0:H0:H1:ZZ:t) = Just (S0:H0:H1:ZZ:S0:H0:S0:S0:H0:S1:S1:Omega (-1):t)
peephole_clifford (H0:S0:H0:S1:H1:ZZ:t) = Just (S0:H0:S1:H1:ZZ:S0:H0:S0:S0:H0:S1:S1:Omega (-1):t)

peephole_clifford (S1:H1:ZZ:H0:H1:ZZ:t) = Just (H1:ZZ:H0:H1:ZZ:H0:S0:H0:t)
peephole_clifford (S1:H1:ZZ:S0:H0:H1:ZZ:t) = Just (H1:ZZ:S0:H0:H1:ZZ:H0:S0:H0:t)
peephole_clifford (S0:H0:ZZ:H0:H1:ZZ:t) = Just (H0:ZZ:H0:H1:ZZ:H1:S1:H1:t)
peephole_clifford (S0:H0:H1:ZZ:H0:H1:ZZ:t) = Just (H0:H1:ZZ:H0:H1:ZZ:H1:S1:H1:t)
peephole_clifford (S0:H0:ZZ:H0:S1:H1:ZZ:t) = Just (H0:ZZ:H0:S1:H1:ZZ:H1:S1:H1:t)

peephole_clifford (H1:ZZ:H0:S1:H1:ZZ:t) = Just (ZZ:H0:S1:H1:ZZ:S0:S0:S0:H0:S0:H1:S1:S1:H1:t)
peephole_clifford (H1:ZZ:S0:H0:S1:H1:ZZ:t) = Just (ZZ:S0:H0:S1:H1:ZZ:S0:S0:S0:H0:S0:H1:S1:S1:H1:t)
peephole_clifford (H0:ZZ:S0:H0:H1:ZZ:t) = Just (ZZ:S0:H0:H1:ZZ:H0:S0:S0:H0:S1:S1:S1:H1:S1:t)
peephole_clifford (H0:H1:ZZ:S0:H0:H1:ZZ:t) = Just (H1:ZZ:S0:H0:H1:ZZ:H0:S0:S0:H0:S1:S1:S1:H1:S1:t)
peephole_clifford (H0:ZZ:S0:H0:S1:H1:ZZ:t) = Just (ZZ:S0:H0:S1:H1:ZZ:H0:S0:S0:H0:S1:S1:S1:H1:S1:t)

peephole_clifford (ZZ:H0:ZZ:t) = Just (S0:H0:ZZ:S0:H0:S0:S1:Omega (-1):t)
peephole_clifford (ZZ:S0:H0:ZZ:t) = Just (S0:S0:H0:ZZ:S0:H0:S0:S1:Omega (-1):t)
peephole_clifford (ZZ:H1:ZZ:t) = Just (S1:H1:ZZ:S0:S1:H1:S1:Omega (-1):t)
peephole_clifford (ZZ:S1:H1:ZZ:t) = Just (S1:S1:H1:ZZ:S0:S1:H1:S1:Omega (-1):t)

peephole_clifford (H1:ZZ:H0:H1:ZZ:H0:H1:ZZ:t) = Just (ZZ:H0:H1:ZZ:H0:H1:ZZ:H0:t)
peephole_clifford (H0:ZZ:H0:H1:ZZ:H0:H1:ZZ:t) = Just (ZZ:H0:H1:ZZ:H0:H1:ZZ:H1:t)

-- Recursive cases.
peephole_clifford (h:t) = do
  t' <- peephole_clifford t
  return (h:t')
peephole_clifford [] = Nothing

-- | Auxiliary function to simplify cases.
peephole_simple :: [Gate] -> [Gate] -> [Gate] -> Maybe ([Gate], Der Gate)
peephole_simple lhs rhs t = Just (rhs ++ t, Cong [] der t)
  where
    der = Lemma (lname ++ "=" ++ rname) (lhs === rhs)
    lname = name lhs
    rname = name rhs
    name xs = case xs of { [] -> "ε" ; _ -> concat [ nospace (to_agda x) | x <- xs ] }
    nospace s = [ x | x <- s, x /= ' ' ]

-- | Like 'peephole_clifford', but with evidence.
peephole_clifford_der :: [Gate] -> Maybe ([Gate], Der Gate)

-- Rules for Omega.
peephole_clifford_der (Omega 0:t) = Just (t, refl (Omega 0:t) t)
peephole_clifford_der (Omega k:Omega l:t) = Just (Omega (k+l):t, refl (Omega k:Omega l:t) (Omega (k+l):t))
peephole_clifford_der (Omega k:t) | k >= 8 = Just (Omega (k - 8):t, der)
  where
    lemma = Lemma "order-W" ([Omega 8] === [])
    der = Cong [] lemma (Omega (k-8):t)
peephole_clifford_der (Omega k:t) | k < 0 = Just (Omega (k + 8):t, error "peephole_clifford_der") -- hopefully we don't need this?
peephole_clifford_der (Omega k:h:t) = Just (h:Omega k:t, Cong [] (Lemma ("commute-omega " ++ show k ++ " " ++ show h) ([Omega k,h] === [h,Omega k])) t)

-- Commuting rules for unary gates.
peephole_clifford_der (H1:H0:t) = peephole_simple [H1,H0] [H0,H1] t
peephole_clifford_der (H1:S0:t) = peephole_simple [H1,S0] [S0,H1] t
peephole_clifford_der (S1:H0:t) = peephole_simple [S1,H0] [H0,S1] t
peephole_clifford_der (S1:S0:t) = peephole_simple [S1,S0] [S0,S1] t

-- Rules for unary gates.
peephole_clifford_der (H0:H0:t) = peephole_simple [H0,H0] [] t
peephole_clifford_der (S0:S0:S0:S0:t) = peephole_simple [S0,S0,S0,S0] [] t
peephole_clifford_der (S0:H0:S0:H0:t) = peephole_simple [S0,H0,S0,H0] [H0,S0,S0,S0,Omega 1] t
peephole_clifford_der (H0:S0:H0:S0:t) = peephole_simple [H0,S0,H0,S0] [S0,S0,S0,H0,Omega 1] t
peephole_clifford_der (H0:S0:S0:S0:H0:t) = peephole_simple [H0,S0,S0,S0,H0] [S0,H0,S0,Omega 7] t
peephole_clifford_der (S0:H0:S0:S0:H0:S0:t) = peephole_simple [S0,H0,S0,S0,H0,S0] [H0,S0,S0,H0,Omega 2] t
peephole_clifford_der (H0:S0:S0:H0:S0:S0:t) = peephole_simple [H0,S0,S0,H0,S0,S0] [S0,S0,H0,S0,S0,H0,Omega 4] t
peephole_clifford_der (S0:S0:S0:H0:S0:S0:H0:t) = peephole_simple [S0,S0,S0,H0,S0,S0,H0] [H0,S0,S0,H0,S0,Omega 6] t
peephole_clifford_der (S0:S0:S0:H0:S0:S0:S0:t) = peephole_simple [S0,S0,S0,H0,S0,S0,S0] [H0,S0,H0,Omega 7] t

peephole_clifford_der (H1:H1:t) = peephole_simple [H1,H1] [] t
peephole_clifford_der (S1:S1:S1:S1:t) = peephole_simple [S1,S1,S1,S1] [] t
peephole_clifford_der (S1:H1:S1:H1:t) = peephole_simple [S1,H1,S1,H1] [H1,S1,S1,S1,Omega 1] t
peephole_clifford_der (H1:S1:H1:S1:t) = peephole_simple [H1,S1,H1,S1] [S1,S1,S1,H1,Omega 1] t
peephole_clifford_der (H1:S1:S1:S1:H1:t) = peephole_simple [H1,S1,S1,S1,H1] [S1,H1,S1,Omega 7] t
peephole_clifford_der (S1:H1:S1:S1:H1:S1:t) = peephole_simple [S1,H1,S1,S1,H1,S1] [H1,S1,S1,H1,Omega 2] t
peephole_clifford_der (H1:S1:S1:H1:S1:S1:t) = peephole_simple [H1,S1,S1,H1,S1,S1] [S1,S1,H1,S1,S1,H1,Omega 4] t
peephole_clifford_der (S1:S1:S1:H1:S1:S1:H1:t) = peephole_simple [S1,S1,S1,H1,S1,S1,H1] [H1,S1,S1,H1,S1,Omega 6] t
peephole_clifford_der (S1:S1:S1:H1:S1:S1:S1:t) = peephole_simple [S1,S1,S1,H1,S1,S1,S1] [H1,S1,H1,Omega 7] t

-- Rules for ZZ.
peephole_clifford_der (ZZ:ZZ:t) = peephole_simple [ZZ,ZZ] [] t
peephole_clifford_der (S1:ZZ:t) = peephole_simple [S1,ZZ] [ZZ,S1] t
peephole_clifford_der (S0:ZZ:t) = peephole_simple [S0,ZZ] [ZZ,S0] t
peephole_clifford_der (S0:H1:ZZ:t) = peephole_simple [S0,H1,ZZ] [H1,ZZ,S0] t
peephole_clifford_der (S0:S1:H1:ZZ:t) = peephole_simple [S0,S1,H1,ZZ] [S1,H1,ZZ,S0] t

peephole_clifford_der (S1:S1:H1:ZZ:t) = peephole_simple [S1,S1,H1,ZZ] [H1,ZZ,S0,S0,H1,S1,S1,H1] t

peephole_clifford_der (S0:S0:H0:ZZ:t) = peephole_simple [S0,S0,H0,ZZ] [H0,ZZ,H0,S0,S0,H0,S1,S1] t
peephole_clifford_der (S0:S0:H0:H1:ZZ:t) = peephole_simple [S0,S0,H0,H1,ZZ] [H0,H1,ZZ,H0,S0,S0,H0,S1,S1] t
peephole_clifford_der (S0:S0:H0:S1:H1:ZZ:t) = peephole_simple [S0,S0,H0,S1,H1,ZZ] [H0,S1,H1,ZZ,H0,S0,S0,H0,S1,S1] t

peephole_clifford_der (H1:S1:H1:ZZ:t) = peephole_simple [H1,S1,H1,ZZ] [S1,H1,ZZ,S0,S0,S1,H1,S1,S1,H1,Omega 7] t
peephole_clifford_der (H0:S0:H0:ZZ:t) = peephole_simple [H0,S0,H0,ZZ] [S0,H0,ZZ,S0,H0,S0,S0,H0,S1,S1,Omega 7] t
peephole_clifford_der (H0:S0:H0:H1:ZZ:t) = peephole_simple [H0,S0,H0,H1,ZZ] [S0,H0,H1,ZZ,S0,H0,S0,S0,H0,S1,S1,Omega 7] t
peephole_clifford_der (H0:S0:H0:S1:H1:ZZ:t) = peephole_simple [H0,S0,H0,S1,H1,ZZ] [S0,H0,S1,H1,ZZ,S0,H0,S0,S0,H0,S1,S1,Omega 7] t

peephole_clifford_der (S1:H1:ZZ:H0:H1:ZZ:t) = peephole_simple [S1,H1,ZZ,H0,H1,ZZ] [H1,ZZ,H0,H1,ZZ,H0,S0,H0] t
peephole_clifford_der (S1:H1:ZZ:S0:H0:H1:ZZ:t) = peephole_simple [S1,H1,ZZ,S0,H0,H1,ZZ] [H1,ZZ,S0,H0,H1,ZZ,H0,S0,H0] t
peephole_clifford_der (S0:H0:ZZ:H0:H1:ZZ:t) = peephole_simple [S0,H0,ZZ,H0,H1,ZZ] [H0,ZZ,H0,H1,ZZ,H1,S1,H1] t
peephole_clifford_der (S0:H0:H1:ZZ:H0:H1:ZZ:t) = peephole_simple [S0,H0,H1,ZZ,H0,H1,ZZ] [H0,H1,ZZ,H0,H1,ZZ,H1,S1,H1] t
peephole_clifford_der (S0:H0:ZZ:H0:S1:H1:ZZ:t) = peephole_simple [S0,H0,ZZ,H0,S1,H1,ZZ] [H0,ZZ,H0,S1,H1,ZZ,H1,S1,H1] t

peephole_clifford_der (H1:ZZ:H0:S1:H1:ZZ:t) = peephole_simple [H1,ZZ,H0,S1,H1,ZZ] [ZZ,H0,S1,H1,ZZ,S0,S0,S0,H0,S0,H1,S1,S1,H1] t
peephole_clifford_der (H1:ZZ:S0:H0:S1:H1:ZZ:t) = peephole_simple [H1,ZZ,S0,H0,S1,H1,ZZ] [ZZ,S0,H0,S1,H1,ZZ,S0,S0,S0,H0,S0,H1,S1,S1,H1] t
peephole_clifford_der (H0:ZZ:S0:H0:H1:ZZ:t) = peephole_simple [H0,ZZ,S0,H0,H1,ZZ] [ZZ,S0,H0,H1,ZZ,H0,S0,S0,H0,S1,S1,S1,H1,S1] t
peephole_clifford_der (H0:H1:ZZ:S0:H0:H1:ZZ:t) = peephole_simple [H0,H1,ZZ,S0,H0,H1,ZZ] [H1,ZZ,S0,H0,H1,ZZ,H0,S0,S0,H0,S1,S1,S1,H1,S1] t
peephole_clifford_der (H0:ZZ:S0:H0:S1:H1:ZZ:t) = peephole_simple [H0,ZZ,S0,H0,S1,H1,ZZ] [ZZ,S0,H0,S1,H1,ZZ,H0,S0,S0,H0,S1,S1,S1,H1,S1] t

peephole_clifford_der (ZZ:H0:ZZ:t) = peephole_simple [ZZ,H0,ZZ] [S0,H0,ZZ,S0,H0,S0,S1,Omega 7] t
peephole_clifford_der (ZZ:S0:H0:ZZ:t) = peephole_simple [ZZ,S0,H0,ZZ] [S0,S0,H0,ZZ,S0,H0,S0,S1,Omega 7] t
peephole_clifford_der (ZZ:H1:ZZ:t) = peephole_simple [ZZ,H1,ZZ] [S1,H1,ZZ,S0,S1,H1,S1,Omega 7] t
peephole_clifford_der (ZZ:S1:H1:ZZ:t) = peephole_simple [ZZ,S1,H1,ZZ] [S1,S1,H1,ZZ,S0,S1,H1,S1,Omega 7] t

peephole_clifford_der (H1:ZZ:H0:H1:ZZ:H0:H1:ZZ:t) = peephole_simple [H1,ZZ,H0,H1,ZZ,H0,H1,ZZ] [ZZ,H0,H1,ZZ,H0,H1,ZZ,H0] t
peephole_clifford_der (H0:ZZ:H0:H1:ZZ:H0:H1:ZZ:t) = peephole_simple [H0,ZZ,H0,H1,ZZ,H0,H1,ZZ] [ZZ,H0,H1,ZZ,H0,H1,ZZ,H1] t

-- Recursive cases.
peephole_clifford_der (h:t) = do
  (t', der) <- peephole_clifford_der t
  return (h:t', Cong [h] der [])
peephole_clifford_der [] = Nothing

-- | Desugar all Clifford gates in a circuit to the {'ZZ', 'H0', 'S0',
-- 'H1', 'S1', 'Omega'} gate set. Non-Clifford gates are untouched.
desugar_to_ZZHS :: [Gate] -> [Gate]
desugar_to_ZZHS circ = concat [ desugar_gate x | x <- circ ]
  where
    desugar_gate ZZ = [ZZ]
    desugar_gate H0 = [H0]
    desugar_gate H1 = [H1]
    desugar_gate S0 = [S0]
    desugar_gate S1 = [S1]
    desugar_gate (Omega k) = [Omega k]
    desugar_gate Swap = [ZZ, H0, H1, ZZ, H0, H1, ZZ, H0, H1]
    desugar_gate g | isClifford g = desugar_to_ZZHS (desugar g)
    desugar_gate g = [g]

-- | Efficiently simplify swap gates. Desugaring them to ZZHS
-- introduces unreasonable overhead!
simplify_swaps :: [Gate] -> Maybe [Gate]
simplify_swaps (Swap : Swap : t) = Just t
simplify_swaps (Swap : g : t) = Just (g' : Swap : t)
  where
    g' = swap_gate g
simplify_swaps (h : t) = do
  t' <- simplify_swaps t
  return (h : t')
simplify_swaps [] = Nothing

-- | Like 'simplify_swaps', but with witness.
simplify_swaps_der :: [Gate] -> Maybe ([Gate], Der Gate)
simplify_swaps_der (Swap : Swap : t) = peephole_simple [Swap, Swap] [] t
simplify_swaps_der (Swap : g : t) = peephole_simple [Swap, g] [g', Swap] t
  where
    g' = swap_gate g
-- Recursive cases.
simplify_swaps_der (h:t) = do
  (t', der) <- simplify_swaps_der t
  return (h:t', Cong [h] der [])
simplify_swaps_der [] = Nothing

-- | Simplify the Clifford parts of a circuit.
simplify_clifford :: [Gate] -> [Gate]
simplify_clifford c = repeatedly peephole_clifford (desugar_to_ZZHS (repeatedly simplify_swaps c))

-- ----------------------------------------------------------------------
-- ** More sophisticated simpification of Clifford circuits

-- | Simplify a Clifford circuit using a single Swap gate at the end.
simplify_clifford_with_swap :: [Gate] -> [Gate]
simplify_clifford_with_swap gates = gates' ++ [Swap]
  where
    gates' = simplify_clifford (gates ++ [Swap])

-- | Simplify a Clifford circuit, but only if the "simplified" circuit
-- is shorter than the original.
shorten_clifford :: [Gate] -> [Gate]
shorten_clifford gates
  | length gates <= length gates' && length gates <= length gates'' = gates
  | length gates' <= length gates'' = gates'
  | otherwise = gates''
  where
    gates' = simplify_clifford gates
    gates'' = simplify_clifford_with_swap gates

-- | Produce a proof of the equality of two Clifford gates.
by_clifford :: [Gate] -> [Gate] -> Der Gate
by_clifford lhs rhs
  | lhs == rhs = Refl lhs rhs
  | lhs' == rhs' = Tactic ByClifford (Eqn lhs rhs)
  | otherwise = error ("by_clifford: " ++ show (lhs, rhs, lhs', rhs'))
  where
    lhs' = simplify_clifford lhs
    rhs' = simplify_clifford rhs

-- | Like 'shorten_clifford', but with witness.
shorten_clifford_der :: [Gate] -> ([Gate], Der Gate)
shorten_clifford_der gates
  | length gates' < length gates = (gates', der)
  | otherwise = (gates, refl gates gates)
  where
    gates' = shorten_clifford gates
    (pre, lhs, rhs, post) = find_context gates gates'
    der1 = by_clifford lhs rhs
    der = Cong pre der1 post

-- | Like 'simplify_clifford', but with witness.
simplify_clifford_der :: [Gate] -> ([Gate], Der Gate)
simplify_clifford_der gates
  | gates' /= gates = (gates', der)
  | otherwise = (gates, refl gates gates)
  where
    gates' = simplify_clifford gates
    (pre, lhs, rhs, post) = find_context gates gates'
    der1 = by_clifford lhs rhs
    der = Cong pre der1 post

-- | Shorten all Clifford subcircuits.
shorten_cliffords :: [Gate] -> [Gate]
shorten_cliffords gates = clif' ++ rest'
  where
    (clif, rest) = span isClifford gates
    clif' = shorten_clifford clif
    rest' = case rest of
      [] -> []
      h : t -> h : shorten_cliffords t

-- | Like 'shorten_cliffords', but with witness.
shorten_cliffords_der :: [Gate] -> ([Gate], Der Gate)
shorten_cliffords_der gates = (clif' ++ rest', cong2 der1 der2)
  where
    (clif, rest) = span isClifford gates
    (clif', der1) = shorten_clifford_der clif
    (rest', der2) = case rest of
      [] -> ([], refl [] [])
      h : t ->
        let (t', der3) = shorten_cliffords_der t
        in
          (h : t', Cong [h] der3 [])

-- | Simplify (normalize) all Clifford subcircuits.
simplify_cliffords :: [Gate] -> [Gate]
simplify_cliffords gates = clif' ++ rest'
  where
    (clif, rest) = span isClifford gates
    clif' = simplify_clifford clif
    rest' = case rest of
      [] -> []
      h : t -> h : simplify_cliffords t

-- | Like 'simplify_cliffords', but with witness.
simplify_cliffords_der :: [Gate] -> ([Gate], Der Gate)
simplify_cliffords_der gates = (clif' ++ rest', cong2 der1 der2)
  where
    (clif, rest) = span isClifford gates
    (clif', der1) = simplify_clifford_der clif
    (rest', der2) = case rest of
      [] -> ([], refl [] [])
      h : t ->
        let (t', der3) = simplify_cliffords_der t
        in
          (h : t', Cong [h] der3 [])

-- ----------------------------------------------------------------------
-- * Channel representation

-- ----------------------------------------------------------------------
-- ** Conversion to syllable format

-- | Convert a Clifford+/T/ circuit to channel representation, but do
-- not eliminate intermediate Clifford gates. This function uses
-- 'R'-syllables (channel generators with positive or negative Pauli
-- operators).
to_channel :: [Gate] -> [Gate]
to_channel [] = []
to_channel (T0 : xs) = R (Pauli2 Plus Z I) : to_channel xs
to_channel (T1 : xs) = R (Pauli2 Plus I Z) : to_channel xs
to_channel (T0inv : xs) = R (Pauli2 Plus Z I) : S0inv : to_channel xs
to_channel (T1inv : xs) = R (Pauli2 Plus I Z) : S1inv : to_channel xs
to_channel (CH0 : xs) = to_channel ([S0, H0, T0, CX0, T0inv, H0, S0inv] ++ xs)
to_channel (CH1 : xs) = to_channel ([S1, H1, T1, CX1, T1inv, H1, S1inv] ++ xs)
to_channel (CS : xs) = to_channel ([T0, T1, CX0, T0inv, CX0] ++ xs)
to_channel (x : xs) = x : to_channel xs

-- | Like 'to_channel', but with a witness.
to_channel_der :: [Gate] -> ([Gate], Der Gate)
to_channel_der [] = ([], Refl [] [])
to_channel_der (T0 : xs) = (R (Pauli2 Plus Z I) : xs', der)
  where
    (xs', der1) = to_channel_der xs
    -- der1 : xs === xs'
    der2 = refl [T0] [R (Pauli2 Plus Z I)]
    -- der2 : T0 === R (Pauli2 Plus Z I)
    der = trans (Cong [] der2 xs) (Cong [R (Pauli2 Plus Z I)] der1 [])
to_channel_der (T1 : xs) = (R (Pauli2 Plus I Z) : xs', der)
  where
    (xs', der1) = to_channel_der xs
    -- der1 : xs === xs'
    der2 = Lemma "lemma-channel-T1" (Eqn [T1] [R (Pauli2 Plus I Z)])
    -- der2 : T1 === R (Plus, I, Z)
    der = trans (Cong [] der2 xs) (Cong [R (Pauli2 Plus I Z)] der1 [])
to_channel_der (T0inv : xs) = (R (Pauli2 Plus Z I) : S0inv : xs', der)
  where
    (xs', der1) = to_channel_der xs
    -- der1 : xs === xs'
    der2 = Lemma "lemma-channel-T0⁻¹" (Eqn [T0inv] [R (Pauli2 Plus Z I), S0inv])
    -- der2 : T0⁻¹ === R (Plus, Z, I) • S0⁻¹
    der = trans (Cong [] der2 xs) (Cong [R (Pauli2 Plus Z I), S0inv] der1 [])
to_channel_der (T1inv : xs) = (R (Pauli2 Plus I Z) : S1inv : xs', der)
  where
    (xs', der1) = to_channel_der xs
    -- der1 : xs === xs'
    der2 = Lemma "lemma-channel-T1⁻¹" (Eqn [T1inv] [R (Pauli2 Plus I Z), S1inv])
    -- der2 : T1⁻¹ === R (Pauli2 Plus I Z) • S1⁻¹
    der = trans (Cong [] der2 xs) (Cong [R (Pauli2 Plus I Z), S1inv] der1 [])
to_channel_der (CH0 : xs) = to_channel_der ([S0, H0, T0, CX0, T0inv, H0, S0inv] ++ xs)
to_channel_der (CH1 : xs) = to_channel_der ([S1, H1, T1, CX1, T1inv, H1, S1inv] ++ xs)
to_channel_der (CS : xs) = to_channel_der ([T0, T1, CX0, T0inv, CX0] ++ xs)
to_channel_der (x : xs) = (x : xs', der)
  where
    (xs', der1) = to_channel_der xs
    -- der1 : xs === xs'
    der = Cong [x] der1 []

-- ----------------------------------------------------------------------
-- ** Commute Clifford operators to the right

-- | Clean up a channel representation so that there are no Clifford
-- operators to the left of R-syllables. Avoid excessive desugaring.
clean_channel_step :: [Gate] -> Maybe [Gate]
clean_channel_step gates =
  case rest of
    R pauli : other -> do
      let pauli' = actions c pauli
      return (g1 ++ [R pauli'] ++ c ++ other)
    other -> Nothing
  where
    (g1, gs) = span (not . isClifford) gates
    (c, rest) = span (isClifford) gs

-- | Like 'clean_channel_step', but with witness.
clean_channel_step_der :: [Gate] -> Maybe ([Gate], Der Gate)
clean_channel_step_der gates =
  case rest of
    R pauli : other -> do
      -- refl : rest === R pauli : other
      let (pauli',d) = actions_der c pauli
      -- d : C • R pauli = R pauli' • C
      let der = Cong g1 d other
      -- der : gates === g1 • c • R pauli • other === g1 • R pauli' • c • other
      return (g1 ++ [R pauli'] ++ c ++ other, der)
    other -> Nothing
  where
    (g1, gs) = span (not . isClifford) gates
    (c, rest) = span (isClifford) gs
    -- refl : gates === g1 • c • rest

-- | Clean up a channel representation so that there are no Clifford
-- operators to the left of R-syllables. Avoid excessive
-- desugaring. Simplify Clifford operators where useful.
clean_channel :: [Gate] -> [Gate]
clean_channel gates =
  case clean_channel_step gates' of
    Nothing -> gates'
    Just g -> clean_channel g
  where
    gates' = shorten_cliffords gates

-- | Like 'clean_channel', but with witness.
clean_channel_der :: [Gate] -> ([Gate], Der Gate)
clean_channel_der gates =
  case clean_channel_step_der gates' of
    Nothing -> (gates', der1)
    Just (g, der2) ->
      -- der2 : gates' === g
      let (a, der3) = clean_channel_der g
      -- der3 : g === a
      in
        (a, der1 `trans` der2 `trans` der3)
  where
    (gates',der1) = shorten_cliffords_der gates
    -- der1 : gates === gates'

-- ----------------------------------------------------------------------
-- ** Convert to positive channels

-- | Clean up a channel representation so that there are no Clifford
-- operators to the left of R-syllables, and so that all R-syllables
-- are positive.
clean_channel_pos_step :: [Gate] -> Maybe [Gate]
clean_channel_pos_step (g@(R (Pauli2 Plus p q)) : t) = do
  t' <- clean_channel_pos_step t
  return (g : t')
clean_channel_pos_step gates =
  case rest of
    R pauli : other -> do
      let pauli' = actions c pauli
      let r = rsyll_pos pauli'
      return (r ++ c ++ other)
    other -> Nothing
  where
    (c, rest) = span (isClifford) gates

-- | Like 'clean_channel_pos_step', but with witness.
clean_channel_pos_step_der :: [Gate] -> Maybe ([Gate], Der Gate)
clean_channel_pos_step_der (g@(R (Pauli2 Plus p q)) : t) = do
  (t', der) <- clean_channel_pos_step_der t
  return (g : t', Cong [g] der [])
clean_channel_pos_step_der gates =
  case rest of
    R pauli : other -> do
      let (pauli', der1) = actions_der c pauli
      -- der1 : c • R pauli === R pauli' • c
      let (r, der2) = rsyll_pos_der pauli'
      -- der2 : R pauli' === r
      let der = trans (Cong [] der1 other) (Cong [] der2 (c ++ other))
      -- der : gates == c • rest == c • R pauli • other === R pauli' • c • other === r • c • other
      return (r ++ c ++ other, der)
    other -> Nothing
  where
    (c, rest) = span (isClifford) gates

-- | Clean up a channel representation so that there are no Clifford
-- operators to the left of R-syllables, and so that all R-syllables
-- are positive.
clean_channel_pos :: [Gate] -> [Gate]
clean_channel_pos gates =
  case clean_channel_pos_step gates' of
    Nothing -> gates'
    Just g -> clean_channel_pos g
  where
    gates' = shorten_cliffords gates

-- | Like 'clean_channel_pos', but with witness.
clean_channel_pos_der :: [Gate] -> ([Gate], Der Gate)
clean_channel_pos_der gates =
  case clean_channel_pos_step_der gates' of
    Nothing -> (gates', der1)
    Just (g, der2) ->
      -- der2 : gates' === g
      let (a, der3) = clean_channel_pos_der g
      -- der3 : g === a
      in
        (a, der1 `trans` der2 `trans` der3)
  where
    (gates',der1) = shorten_cliffords_der gates
    -- der1 : gates === gates'

-- ----------------------------------------------------------------------
-- ** Standardize commuting operators

-- | Return all possible ways to split a list into a prefix, a single
-- element, and a postfix. Example:
--
-- > splits [1,2,3,4] = [ ([],1,[2,3,4]),
-- >                      ([1],2,[3,4]),
-- >                      ([1,2],3,[4]),
-- >                      ([1,2,3],4,[])
-- >                    ].
splits :: [a] -> [([a],a,[a])]
splits [] = []
splits (h:t) = ([],h,t) : [(h:pre,x,post) | (pre,x,post) <- splits t]

-- | Input a word, and a function to determine whether two letters
-- commute. Output the alphabetically first representative of the
-- equivalence class of the given word modulo commutations.
sort_word :: (Ord a, Eq a) => (a -> a -> Bool) -> [a] -> [a]
sort_word com w = case best of
  [] -> []
  (pre,x,post):_ -> x : sort_word com (pre ++ post)
  where
    candidates = [ (pre,x,post) | (pre,x,post) <- splits w, all (com x) pre ]
    best = sortBy (compare `on` (\(p,x,q) -> x)) candidates

-- | Input y, a comparision function p, and a list [x1, ..., xn]. If
-- for each i, p y xi is a proof that y commutes with xi, then output
-- a proof that y commutes with [x1, ..., xn].
all_der :: (Show a, Desugar_Agda a, Eq a) => a -> (a -> a -> Maybe (Der a)) -> [a] -> Maybe (Der a)
all_der y p [] = Just (refl [y] [y])
all_der y p (x : xs) =
  case (p y x, all_der y p xs) of
    (Nothing, _) -> Nothing
    (_, Nothing) -> Nothing
    (Just d1, Just d2) ->
      -- d1 : [y] ++ [x] == [x] ++ [y]
      -- d2 : [y] ++ xs == xs ++ [y]
      let d = trans (Cong [] d1 xs) (Cong [x] d2 [])
        -- d : [y] ++ [x] ++ xs == [x] ++ xs ++ [y]
      in
        Just d

-- | Like 'sort_word', but also produce a witness of w == w'
sort_word_der :: (Ord a, Eq a, Show a, Desugar_Agda a) => (a -> a -> Maybe (Der a)) -> [a] -> ([a], Der a)
sort_word_der com w = case best of
  [] -> ([], refl [] [])
  (pre,x,post,d):_ ->
    let
      -- d : [x] ++ pre == pre ++ [x]
      (rest, ih) = sort_word_der com (pre ++ post)
      -- ih : pre ++ post == rest
      der = trans (Cong [] (Symm d) post) (Cong [x] ih [])
      -- der : pre ++ [x] ++ post == [x] ++ rest
    in
      (x : rest, der)
  where
    candidates = [ (pre,x,post,d) | (pre,x,post) <- splits w, Just d <- [all_der x com pre] ]
    best = sortBy (compare `on` (\(p,x,q,d) -> x)) candidates

-- | Consider the equivalence relation on circuits generated by
-- pairwise permutation of commuting gates. This function picks out
-- the alphabetically first representative in each equivalence class.
constrained_sort :: [Gate] -> [Gate]
constrained_sort = sort_word commute

-- | Like 'constrained_sort', but produce a witness.
constrained_sort_der :: [Gate] -> ([Gate], Der Gate)
constrained_sort_der = sort_word_der commute_der

-- | Check whether two elementary gates commute. We really only care
-- in case of B-gates - all other gates are made non-commuting.
commute :: Gate -> Gate -> Bool
commute (R pauli) (R pauli') = commute_pauli p p' `sign_mult` commute_pauli q q' == Plus
  where
    (Pauli2 s p q) = pauli
    (Pauli2 s' p' q') = pauli'
commute _ _ = False

-- | Like 'commute', but also output a proof when the gates
-- commute. (The proof is always a lemma).
commute_der :: Gate -> Gate -> Maybe (Der Gate)
commute_der g h
  | g == h = Just (refl [g, h] [h, g])
commute_der g@(R pauli) h@(R pauli') =
  case commute_pauli p p' `sign_mult` commute_pauli q q' of
    Plus -> Just (Lemma ("lemma-commute " ++ to_agda pauli ++ " " ++ to_agda pauli' ++ " auto") ([g, h] === [h, g]))
    Minus -> Nothing
  where
    (Pauli2 s p q) = pauli
    (Pauli2 s' p' q') = pauli'
commute_der _ _ = Nothing

-- ----------------------------------------------------------------------
-- ** Combine mergable syllables

-- | Combine adjacent /R/-syllables if they can be merged into a
-- single syllable. Return 'Nothing' if no such combining was possible.
r_combine_step :: [Gate] -> Maybe [Gate]
r_combine_step [] = Nothing
r_combine_step [a] = Nothing
r_combine_step (R (Pauli2 s p q) : R (Pauli2 s' p' q') : t)
  | p==p' && q==q' = Just (gates ++ t)
  where
    gates = c ++ corr ++ invert c
    c = conjugator (Pauli2 Plus p q)
    corr = case (s,s') of
      (Plus,Plus) -> [S0]
      (Plus,Minus) -> [Omega 1]
      (Minus,Plus) -> [Omega 1]
      (Minus,Minus) -> [S0inv,Omega 2]
r_combine_step (h:t) = do
  t' <- r_combine_step t
  return (h:t')

-- | Like 'r_combine_step', but with witness.
r_combine_step_der :: [Gate] -> Maybe ([Gate], Der Gate)
r_combine_step_der [] = Nothing
r_combine_step_der [a] = Nothing
r_combine_step_der (R (Pauli2 s p q) : R (Pauli2 s' p' q') : t)
  | p==p' && q==q' = Just (gates ++ t, der)
  where
    gates = c ++ corr ++ invert c
    c = conjugator (Pauli2 Plus p q)
    corr = case (s,s') of
      (Plus,Plus) -> [S0]
      (Plus,Minus) -> [Omega 1]
      (Minus,Plus) -> [Omega 1]
      (Minus,Minus) -> [S0inv,Omega 2]
    der1 = Lemma ("lemma-combine " ++ to_agda s ++ " " ++ to_agda s' ++ " " ++ to_agda p ++ "⊗" ++ to_agda q) ([R (Pauli2 s p q), R (Pauli2 s' p q)] === gates)
    der = Cong [] der1 t
r_combine_step_der (h:t) = do
  (t', ih) <- r_combine_step_der t
  return (h:t', Cong [h] ih [])

-- | Keep combining until there's nothing to combine. Return 'Nothing'
-- if no progress is possible.
r_combine :: [Gate] -> Maybe [Gate]
r_combine = maybe_repeatedly r_combine_step

-- | Like 'r_combine', but with evidence.
r_combine_der :: [Gate] -> Maybe ([Gate], Der Gate)
r_combine_der = maybe_repeatedly_der r_combine_step_der

-- ----------------------------------------------------------------------
-- ** Combine adjacent T-gates

-- | Opportunistically reduce T0 • T0 to S0 and T1 • T1 to S1, as this
-- is a common case arising from T0⁻¹ and T1⁻¹ gates. This can be a
-- useful pre-processing step.
peephole_tsquared :: [Gate] -> Maybe [Gate]
peephole_tsquared (T0 : T0 : t) = Just (S0 : t)
peephole_tsquared (T1 : T1 : t) = Just (S1 : t)
peephole_tsquared (h:t) = do
  t' <- peephole_tsquared t
  return (h:t')
peephole_tsquared [] = Nothing

-- | Like 'peephole_tsquared', but with witness.
peephole_tsquared_der :: [Gate] -> Maybe ([Gate], Der Gate)
peephole_tsquared_der (T0 : T0 : t) = peephole_simple [T0,T0] [S0] t
peephole_tsquared_der (T1 : T1 : t) = peephole_simple [T1,T1] [S1] t
peephole_tsquared_der (h:t) = do
  (t', der) <- peephole_tsquared_der t
  return (h:t', Cong [h] der [])
peephole_tsquared_der [] = Nothing

-- | Opportunistically reduce T0 • T0 to S0 and T1 • T1 to S1, as this
-- is a common case arising from T0⁻¹ and T1⁻¹ gates. This is a useful
-- pre-processing step.
simplify_tsquared :: [Gate] -> [Gate]
simplify_tsquared c = repeatedly peephole_tsquared c

-- | Like 'simplify_tsquared', but with witness.
simplify_tsquared_der :: [Gate] -> ([Gate], Der Gate)
simplify_tsquared_der c = repeatedly_der peephole_tsquared_der c

-- ----------------------------------------------------------------------
-- ** Apply all of the above to normalize channel representation

-- | Input an arbitrary circuit, convert to channel representation,
-- and then simplify as much as possible using commutativity, combine
-- steps, and commutation of Clifford operators.
normalize :: [Gate] -> [Gate]
normalize gates = simplify_cliffords (constrained_sort (clean_channel_pos (repeatedly step chan3)))
  where
    gates' = simplify_tsquared gates
    chan1 = to_channel gates'
    chan3 = constrained_sort (clean_channel chan1)

    step :: [Gate] -> Maybe [Gate]
    step chan = do
      chan6 <- r_combine chan
      return (constrained_sort (clean_channel chan6))

-- | Like 'normalize', but with witness.
normalize_der :: [Gate] -> ([Gate], Der Gate)
normalize_der gates = (chan7, der0 `trans` der1 `trans` der2 `trans` der3 `trans` der4 `trans` der5 `trans` der6 `trans` der7)
  where
    (gates', der0) = simplify_tsquared_der gates
    (chan1, der1) = to_channel_der gates'
    -- der1 : gates === chan1
    (chan2, der2) = clean_channel_der chan1
    -- der2 : chan1 === chan2
    (chan3, der3) = constrained_sort_der chan2
    -- der3 : chan2 === chan3
    (chan4, der4) = repeatedly_der step chan3
    -- der4 : chan3 === chan4
    (chan5, der5) = clean_channel_pos_der chan4
    -- der5 : chan4 === chan5
    (chan6, der6) = constrained_sort_der chan5
    -- der6 : chan5 === chan6
    (chan7, der7) = simplify_cliffords_der chan6
    -- der6 : chan5 === chan6

    step :: [Gate] -> Maybe ([Gate], Der Gate)
    step chan = do
      (chan6, der6) <- r_combine_der chan
      -- der6 : chan === chan6
      let (chan7, der7) = clean_channel_der chan6
      -- der7 : chan6 === chan7
      let (chan8, der8) = constrained_sort_der chan7
      -- der8 : chan7 === chan8
      return (chan8, der6 `trans` der7 `trans` der8)

-- | Prove an equation, if possible outright, by normalizing the left-
-- and right-hand sides. Otherwise, output a lemma.
prove_equation :: Eqn [Gate] -> String -> Der Gate
prove_equation eqn lemma_name
  | lhs' == rhs' = der1 `trans` (Symm der2)
  | otherwise = der1 `trans` lemma `trans` (Symm der2)
  where
    (lhs', der1) = normalize_der (lhs eqn)
    (rhs', der2) = normalize_der (rhs eqn)
    lemma = Lemma lemma_name (Eqn lhs' rhs')

-- | Prove an equation by normalizing both sides. The user must supply
-- a lemma showing that the normalized lhs and rhs are equal.
prove_equation_from_lemma :: Eqn [Gate] -> Der Gate -> Der Gate
prove_equation_from_lemma eqn proof_lemma
  | lhs' == lhs lemma && rhs' == rhs lemma = der1 `trans` proof_lemma `trans` Symm der2
  | otherwise = error "prove_equation_from_lemma: wrong lemma"
  where
    (lhs', der1) = normalize_der (lhs eqn)
    (rhs', der2) = normalize_der (rhs eqn)
    lemma = eqn_of_der proof_lemma



-- ----------------------------------------------------------------------
-- * One-sided equations and conjugation

-- | Turn an equation into an equivalent one-sided equation. In the
-- special case where the equation is already one-sided of the form a
-- === ε, this is a no-op.
one_sided :: Eqn [Gate] -> [Gate]
one_sided (Eqn a b) = a ++ invert b

-- | Like 'one_sided', but with witnesses f and g. If (x, f, g) =
-- one_sided_der eqn, then
--
-- > f : x === ε -> eqn
-- > g : eqn -> x === ε
one_sided_der :: Eqn [Gate] -> ([Gate], Der Gate -> Der Gate, Der Gate -> Der Gate)
one_sided_der (Eqn a b) = (a ++ binv, f, g)
  where
    (binv, i1, i2) = invert_der b
    -- i1 : b • binv === ε
    -- i2 : binv • b === ε
    f der = der'
      where
        -- der : a • binv === ε
        der1 = Cong [] der b
        -- der1 : a • binv • b === b
        der2 = Cong a i2 []
        -- der2 : a • binv • b === a
        der' = Symm der2 `trans` der1
        -- der' : a === b

    g der' = der
      where
        -- der' : a === b
        der1 = Cong [] der' binv
        -- der1 : a • binv === b • binv
        der = der1 `trans` i1
        -- der : a • binv === ε

-- | Conjugate the given circuit by the given operator.
conjugate :: [Gate] -> [Gate] -> [Gate]
conjugate op circ = op ++ circ ++ invert op

-- | Like 'conjugate', but with witnesses f and g. If (x, f, g) =
-- conjugate_der op y, then
--
-- > f : x === ε -> y === ε
-- > g : y === ε -> x === ε
conjugate_der :: [Gate] -> [Gate] -> ([Gate], Der Gate -> Der Gate, Der Gate -> Der Gate)
conjugate_der op circ = (op ++ circ ++ opinv, f, g)
  where
    (opinv, i1, i2) = invert_der op
    -- i1 : op • opinv === ε
    -- i2 : opinv • op === ε
    f der = der'
      where
        -- der : op • circ • opinv === ε
        der1 = Cong opinv der op
        -- der1 : opinv • op • circ • opinv • op === opinv • op
        der2 = Cong [] i2 (circ ++ opinv ++ op)
        -- der2 : opinv • op • circ • opinv • op === circ • opinv • op
        der3 = Symm der2 `trans` der1
        -- der3 : circ • opinv • op === opinv • op
        der5 = Cong circ i2 []
        -- der5 : circ • opinv • op === circ
        der6 = Symm der5 `trans` der3
        -- der6 : circ === opinv • op
        der' = der6 `trans` i2
        -- der' : circ === ε
    g der' = der
      where
        -- der' : circ === ε
        der1 = Cong op der' opinv
        -- der1 : op • circ • opinv === op • opinv
        der = der1 `trans` i1
        -- der : op • circ • opinv === ε

-- ----------------------------------------------------------------------
-- * Translation between row operations and circuit generators

-- ----------------------------------------------------------------------
-- ** Translate from circuits to row operations

-- | Turn a gate into a list of elemenary row operations. Note: both
-- circuits and row operations are written in matrix multiplication
-- order, i.e., right-to-left.
twolevels_of_gate :: Gate -> [TwoLevel]
twolevels_of_gate ZZ = [TL_omega 4 3]
twolevels_of_gate CX0 = [TL_X 1 3]
twolevels_of_gate CX1 = [TL_X 2 3]
twolevels_of_gate CH0 = [TL_H 1 3]
twolevels_of_gate CH1 = [TL_H 2 3]
twolevels_of_gate CS = [TL_omega 2 3]
twolevels_of_gate Swap = [TL_X 1 2]
twolevels_of_gate H0 = [TL_H 1 3, TL_H 0 2]
twolevels_of_gate H1 = [TL_H 2 3, TL_H 0 1]
twolevels_of_gate S0 = [TL_omega 2 3, TL_omega 2 2]
twolevels_of_gate S1 = [TL_omega 2 3, TL_omega 2 1]
twolevels_of_gate S0inv = [TL_omega 6 3, TL_omega 6 2]
twolevels_of_gate S1inv = [TL_omega 6 3, TL_omega 6 1]
twolevels_of_gate T0 = [TL_omega 1 3, TL_omega 1 2]
twolevels_of_gate T1 = [TL_omega 1 3, TL_omega 1 1]
twolevels_of_gate T0inv = [TL_omega 7 3, TL_omega 7 2]
twolevels_of_gate T1inv = [TL_omega 7 3, TL_omega 7 1]
twolevels_of_gate X0 = [TL_X 1 3, TL_X 0 2]
twolevels_of_gate X1 = [TL_X 2 3, TL_X 0 1]
twolevels_of_gate (Omega k) = [TL_omega k 0, TL_omega k 1, TL_omega k 2, TL_omega k 3]
twolevels_of_gate (R pauli) = twolevels_of_gates (desugar (R pauli))

-- | Turn a circuit into a list of elementary row operations. Note:
-- both circuits and row operations are written in matrix
-- multiplication order, i.e., right-to-left.
twolevels_of_gates :: [Gate] -> [TwoLevel]
twolevels_of_gates gs = concat [ twolevels_of_gate g | g <- gs ]

-- ----------------------------------------------------------------------
-- ** Translate from row operations to circuits

-- | Operators expressible by Clifford+/T/ circuits have determinants
-- that are powers of /i/. Operators expressible by elementary row
-- operations have determinants that are powers of ω. Therefore, there
-- are 2 cosets. We use 1 and ω_[3] as the canonical coset
-- representatives.
data Coset = C1 | Cw
       deriving (Eq, Show)

-- | Convert a coset to a 'TwoLevel' operation.
twolevels_of_coset :: Coset -> [TwoLevel]
twolevels_of_coset C1 = []
twolevels_of_coset Cw = [TL_omega 1 3]

-- | The set of cosets.
cosets :: [Coset]
cosets = [C1, Cw]

-- | Map a coset representative and an elementary row operation into a
-- circuit and a coset representative. Keeping in mind that all
-- multiplication is right-to-left, like matrices.
gates_of_twolevel :: (Coset, TwoLevel) -> ([Gate], Coset)
gates_of_twolevel (C1, TL_X j k) = (graycode2 [CX1] j k, C1)
gates_of_twolevel (Cw, TL_X j k)
  | k == 3 = (graycode2 [T1, CX1, T1inv] j k, Cw)
  | j == 3 = (graycode2 [T1, CX1, T1inv] k j, Cw)
  | otherwise = (graycode2 [CX1] j k, Cw)
gates_of_twolevel (C1, TL_H j k) = (graycode2 [S1inv, H1, T1inv, CX1, T1, H1, S1] j k, C1)
gates_of_twolevel (Cw, TL_H j k)
  | k == 3 = (graycode2 [T1, S1inv, H1, T1inv, CX1, T1, H1, S1, T1inv] j k, Cw)
  | j == 3 = (graycode2 [T1inv, S1inv, H1, T1inv, CX1, T1, H1, S1, T1] j k, Cw)
  | otherwise = (graycode2 [S1inv, H1, T1inv, CX1, T1, H1, S1] j k, Cw)
gates_of_twolevel (c, TL_T n j k) = gates_of_twolevel (c, TL_omega n k)
gates_of_twolevel (C1, TL_omega 1 3) = ([], Cw)
gates_of_twolevel (Cw, TL_omega 1 3) = ([T1, T0, CX1, T1inv, CX1], C1)
gates_of_twolevel (C1, TL_omega 1 k) = (graycode2 [T1inv, CX1, T1, CX1] k 3, Cw)
gates_of_twolevel (Cw, TL_omega 1 k) = (graycode2 [T0] k 3, C1)
gates_of_twolevel (c, TL_omega n k)
  | n < 0 || n > 7 = gates_of_twolevel (c, TL_omega (n `mod` 8) k)
  | n == 0 = ([], c)
  | otherwise = (g1 ++ g2, c2) where
      (g1, c1) = gates_of_twolevel (c, TL_omega 1 k)
      (g2, c2) = gates_of_twolevel (c1, TL_omega (n-1) k)

-- | Map a coset representative and a sequence of elementary row
-- operations into a circuit and a coset representative. Keeping in
-- mind that all multiplication is right-to-left, like matrices.
gates_of_twolevels :: (Coset, [TwoLevel]) -> ([Gate], Coset)
gates_of_twolevels (c, []) = ([], c)
gates_of_twolevels (c, t:ts) = (g ++ gs, c'') where
  (g, c') = gates_of_twolevel (c, t)
  (gs, c'') = gates_of_twolevels (c', ts)

-- | Map an even sequence of elementary row operations to a
-- Clifford+/T/ circuit.  It is an error if the sequence of elementary
-- row operations is not even.
--
-- Here, we call a sequence of elementary row operations \"even\" if
-- it is in the Clifford+/T/ subgroup, i.e., its determinant is a
-- power of /i/.
gates_of_even_twolevels :: [TwoLevel] -> [Gate]
gates_of_even_twolevels ts
  | c == C1 = gs
  | otherwise = error "gates_of_even_twolevels: not even"
  where
    (gs, c) = gates_of_twolevels (C1, ts)

-- ----------------------------------------------------------------------
-- ** Generators and relations for row operations

-- | A type of relations.
data Eqn a = Eqn a a
   deriving (Eq)

-- | Convenient syntax for equations.
(===) :: a -> a -> Eqn a
(===) = Eqn
infix 4 ===

-- | Return the left-hand side of an equation.
lhs :: Eqn a -> a
lhs (Eqn l r) = l

-- | Return the right-hand side of an equation.
rhs :: Eqn a -> a
rhs (Eqn l r) = r

-- | Opposite equation.
symm :: Eqn a -> Eqn a
symm (Eqn l r) = Eqn r l

instance (Show a) => Show (Eqn a) where
  show (Eqn x y) = (show x) ++ " === " ++ (show y)

-- | Output gate relations in latex format.
latex_of_gr_nosimp :: [Eqn [Gate]] -> String
latex_of_gr_nosimp a = concat [r | (Eqn c d) <- a, let e = d++invert c, let r= (tikz_of_clifford 2 e)++"}}\\\\&\\scalebox{0.4}{\\m{"]

-- ----------------------------------------------------------------------
-- * Checking the validity of certain relations

check_twolevel_relation :: Eqn [TwoLevel] -> Bool
check_twolevel_relation (Eqn a b) = matrix_of_twolevels a == (matrix_of_twolevels b :: Matrix Four Four DOmega)

-- | Check the validity of a set of relations.
check_twolevel_relations :: [Eqn [TwoLevel]] -> Bool
check_twolevel_relations eqs = and [ check_twolevel_relation eq | eq <- eqs ]

-- | Check whether a relation is true.
check_gate_relation :: Eqn [Gate] -> Bool
check_gate_relation (Eqn a b) = matrix_of_gates a == (matrix_of_gates b :: Matrix Four Four DOmega)

-- | Check the validity of a set of relations.
check_gate_relations :: [Eqn [Gate]] -> Bool
check_gate_relations eqs = and [ check_gate_relation eq | eq <- eqs ]

-- ----------------------------------------------------------------------
-- * Some automation

-- | Enumerate all 2-qubit Clifford operators.
all_clifford2 :: [[Gate]]
all_clifford2 =
  [ l2 ++ m2 ++ l1 ++ m1 | l2 <- all_l2, m2 <- all_m2, l1 <- all_l1, m1 <- all_m1 ]
  where
    all_m1 = [[], [S0], [S0,S0], [S0,S0,S0]]
    all_l1 = [ a ++ c | a <- all_a1, c <- all_c1 ]
    all_c1 = [[], [H0,S0,S0,H0]]
    all_m2 = [ d ++ e | d <- all_d2, e <- all_e2 ]
    all_e2 = [[], [S1], [S1,S1], [S1,S1,S1]]
    all_d2 = [[ZZ,H0,H1,ZZ,H0,H1,ZZ,H1], [H0,ZZ,H0,H1,ZZ,H1], [H0,H1,S1,ZZ,H0,H1,ZZ,H1], [H0,H1,ZZ,H0,H1,ZZ,H1]]
    all_l2 = all_l1 ++ [ a ++ b ++ c | a <- all_a2, b <- all_b2, c <- all_c1 ]
    all_a1 = [ [], [H0], [H0,S0,H0] ]
    all_a2 = [ [], [H1], [H1,S1,H1] ]
    all_b2 = [ [H1,ZZ,H0,H1,ZZ,H0,H1,ZZ], [ZZ,H0,H1,ZZ], [H0,S0,ZZ,H0,H1,ZZ], [H0,ZZ,H0,H1,ZZ] ]

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Print a matrix in readable format.
print_mat :: (Nat a) => Matrix a b DOmega -> IO ()
print_mat m = print m' where
  m' = matrix_map f m
  f x = fromDOmega x :: DRComplex

-- | output a 1-qubit Pauli operator in Latex format
-- | for exmaple, X -> "X"
latex_of_pauli :: Pauli -> String
latex_of_pauli I = "I"
latex_of_pauli X = "X"
latex_of_pauli Y = "Y"
latex_of_pauli Z = "Z"

latex_of_pauli2 :: Pauli2 -> String
latex_of_pauli2 (Pauli2 Plus p q) = latex_of_pauli p ++ "\\otimes " ++ latex_of_pauli q
latex_of_pauli2 (Pauli2 Minus p q) = "-" ++ latex_of_pauli p ++ "\\otimes " ++ latex_of_pauli q

-- | output a Gate in Latex format
-- | for exmaple, S0 -> "S_0"
latex_of_gate :: Gate -> String
latex_of_gate ZZ = "Z_c"
latex_of_gate CX0 = "CX_0"
latex_of_gate CX1 = "CX_1"
latex_of_gate CH0 = "CH_0"
latex_of_gate CH1 = "CH_1"
latex_of_gate CS = "CS"
latex_of_gate Swap = "Swap"
latex_of_gate H0 = "H_0"
latex_of_gate H1 = "H_1"
latex_of_gate S0 = "S_0"
latex_of_gate S1 = "S_1"
latex_of_gate S0inv = "S_0^{-1}"
latex_of_gate S1inv = "S_1^{-1}"
latex_of_gate T0 = "T_0"
latex_of_gate T1 = "T_1"
latex_of_gate T0inv = "T_0^{-1}"
latex_of_gate T1inv = "T_1^{-1}"
latex_of_gate X0 = "X_0"
latex_of_gate X1 = "X_1"
latex_of_gate (Omega i) = "\\omega^{" ++ show i ++"}"
latex_of_gate (R pauli) = "R_{" ++ latex_of_pauli2 pauli ++ "}"

-- | output a circuit in Latex format
-- | for example, [S0,H0] -> "S_0H_0"
latex_of_gates :: [Gate] -> String
latex_of_gates [] = ""
latex_of_gates (h:t)= (latex_of_gate h)++(latex_of_gates t)

-- | output 40 relations in rels1 in Latex format
latex_of_rels1 :: [[Gate]] -> String
latex_of_rels1 [] = ""
latex_of_rels1 (h:t)= "&"++(latex_of_gates h)++"\\\\\n"++(latex_of_rels1 t)


-- | output ([Gate], Coset) in latex format
latex_of_GcrossC :: ([Gate], Coset) -> String
latex_of_GcrossC (a,C1) = "(" ++ (latex_of_gates a) ++ ", 1)"
latex_of_GcrossC (a,Cw) = "(" ++ (latex_of_gates a) ++ ", \\omega)"

-- | Output a two-level gate in Latex format
-- | for exmaple, TL_H j k -> "H_{[j,k]}"
latex_of_twolevel :: TwoLevel -> String
latex_of_twolevel (TL_H j k) = "H_{["++ (show j)++","++(show k)++"]}"
latex_of_twolevel (TL_X j k) = "X_{["++ (show j)++","++(show k)++"]}"
latex_of_twolevel (TL_omega n k) = "\\omega_{"++(show k)++"}^{"++(show n)++"}"

-- | Output an equation in Latex format.
latex_of_eqn :: Eqn [Gate] -> String
latex_of_eqn (Eqn lhs rhs) = latex_of_gates lhs ++ " = " ++ latex_of_gates rhs

-- ----------------------------------------------------------------------
-- * TikZ output

-- | A type synonym for /x/-coordinates.
type X = Double

-- | A type synonym for /y/-coordinates.
type Y = Double

-- | Convert one gate to TikZ format. This returns a pair consisting
-- of: the width of the gate, and a function from an /X/-coordinate to
-- the code for the gate.
tikz_of_gate :: Int -> Gate -> (X, X -> [String])
tikz_of_gate n (R pauli) = (1.5, code) where
  code x = undefined
tikz_of_gate n (ZZ) = (1, code) where
  code x = [printf "\\controlled{\\dotgate}{%0.2f,%d}{%d};" x (n-1) (n-2)]
tikz_of_gate n (CX0) = (1, code) where
  code x = [printf "\\controlled{\\notgate}{%0.2f,%d}{%d};" x (n-1) (n-2)]
tikz_of_gate n (CX1) = (1, code) where
  code x = [printf "\\controlled{\\notgate}{%0.2f,%d}{%d};" x (n-2) (n-1)]
tikz_of_gate n (CH0) = (1, code) where
  code x = [printf "\\controlled{\\gate{$H$}}{%0.2f,%d}{%d};" x (n-1) (n-2)]
tikz_of_gate n (CH1) = (1, code) where
  code x = [printf "\\controlled{\\gate{$H$}}{%0.2f,%d}{%d};" x (n-2) (n-1)]
tikz_of_gate n (CS) = (1, code) where
  code x = [printf "\\controlled{\\gate{$S$}}{%0.2f,%d}{%d};" x (n-2) (n-1)]
tikz_of_gate n (Swap) = (1, code) where
  code x = [printf "\\swapgate{%0.2f}{%d}{%d};" x (n-2) (n-1)]
tikz_of_gate n (H0) = (1.5, code) where
  code x = [printf "\\gate{$H$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (H1) = (1.5, code) where
  code x = [printf "\\gate{$H$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (S0) = (1.5, code) where
  code x = [printf "\\gate{$S$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (S1) = (1.5, code) where
  code x = [printf "\\gate{$S$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (S0inv) = (1.5, code) where
  code x = [printf "\\gate{$S^\\dagger$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (S1inv) = (1.5, code) where
  code x = [printf "\\gate{$S^\\dagger$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (T0) = (1.5, code) where
  code x = [printf "\\gate{$T$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (T1) = (1.5, code) where
  code x = [printf "\\gate{$T$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (T0inv) = (1.5, code) where
  code x = [printf "\\gate{$T^\\dagger$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (T1inv) = (1.5, code) where
  code x = [printf "\\gate{$T^\\dagger$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (X0) = (1.5, code) where
  code x = [printf "\\gate{$X$}{%0.2f,%d};" x (n-1)]
tikz_of_gate n (X1) = (1.5, code) where
  code x = [printf "\\gate{$X$}{%0.2f,%d};" x (n-2)]
tikz_of_gate n (Omega k) = (1.5, code) where
  code x = [printf "\\gate{$\\omega^{%d}$}{%0.2f,%d};" k x (n-1)]

-- | Return the set of wires of a gate.
wires_of_gate :: Gate -> [Int]
wires_of_gate (R pauli) = [0,1]
wires_of_gate (ZZ) = [0,1]
wires_of_gate (CX0) = [0,1]
wires_of_gate (CX1) = [0,1]
wires_of_gate (CH0) = [0,1]
wires_of_gate (CH1) = [0,1]
wires_of_gate (CS) = [0,1]
wires_of_gate (Swap) = [0,1]
wires_of_gate (H0) = [0]
wires_of_gate (H1) = [1]
wires_of_gate (S0) = [0]
wires_of_gate (S1) = [1]
wires_of_gate (S0inv) = [0]
wires_of_gate (S1inv) = [1]
wires_of_gate (T0) = [0]
wires_of_gate (T1) = [1]
wires_of_gate (T0inv) = [0]
wires_of_gate (T1inv) = [1]
wires_of_gate (X0) = [0]
wires_of_gate (X1) = [1]
wires_of_gate (Omega k) = [0]

-- | Take a convex closure of a set of integers (represented as a
-- list).
convex :: (Enum a, Ord a) => [a] -> [a]
convex [] = []
convex l = [min..max] where
  min = minimum l
  max = maximum l

-- | Assign columns to gates. The columns are numbered from 0. Gates
-- are sorted into columns in such a way that overlapping gates never
-- share the same column.
assign_columns :: [Gate] -> ([(Int, Gate)], Int)
assign_columns = aux Map.empty (-1) where
  aux :: Map Int Int -> Int -> [Gate] -> ([(Int, Gate)], Int)
  aux m c0 [] = ([], 1 + Map.foldr' max 0 m)
  aux m c0 (h:t) = (h':t', n) where
    (t', n) = aux m' c1 t
    h' = (c, h)
    wires = convex (wires_of_gate h)
    c = 1 + foldl' (\x w -> max x (Map.findWithDefault (-1) w m)) c0 wires
    c1 = c0
    m' = foldr (\w m -> Map.insert w c m) m wires

-- | Print a Clifford circuit in TikZ format, with labels. The gates
-- are sorted into columns.
tikz_of_clifford_with_labels :: Int -> [Gate] -> [String] -> [String] -> String
tikz_of_clifford_with_labels n gates l1s l2s = str where
  (colgates, ncols) = assign_columns gates
  gatemap = foldr (\(c,g) m -> Map.insertWith (++) c [g] m) Map.empty colgates
  widthmap = Map.map (\gs -> maximum (map (fst . tikz_of_gate n) gs)) gatemap
  (width', centermap) = Map.mapAccum (\p w -> (p+w, p+0.5*w)) 0.5 widthmap
  render = do
    (c,g) <- colgates
    let ctr = centermap Map.! c
    let (_,f) = tikz_of_gate n g
    return (f ctr)
  width = width' + 0.5
  str = "\\begin{qcircuit}[scale=0.5]\n" ++
        printf "    \\grid{%0.2f}{%s}\n" width (string_of_list "" "," "" "" show [0..n-1]) ++
        concat [ "    " ++ r ++ "\n" | r <- leftlabels 0 n l1s ++
                                            concat render ++
                                            rightlabels width n l2s ] ++
        "\\end{qcircuit}\n"
  leftlabels :: Double -> Int -> [String] -> [String]
  leftlabels x n [] = []
  leftlabels x n (h:t) = (printf "\\leftlabel{%s}{%0.2f,%d}" h x (n-1)) : leftlabels x (n-1) t
  rightlabels :: Double -> Int -> [String] -> [String]
  rightlabels x n [] = []
  rightlabels x n (h:t) = (printf "\\rightlabel{%s}{%0.2f,%d}" h x (n-1)) : rightlabels x (n-1) t

-- | Print a Clifford circuit in TikZ format.
tikz_of_clifford :: Int -> [Gate] -> String
tikz_of_clifford n circ = tikz_of_clifford_with_labels n circ [] []

-- ----------------------------------------------------------------------
-- * Generate Agda proofs for specific propositions.

-- ----------------------------------------------------------------------
-- ** Proof obligations:

eqn1 = Eqn [w] [T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn2 = Eqn [H0] [CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap, X0, CH1, X0, Swap]

eqn3 = Eqn [H1] [Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap, X0, CH1, X0]

eqn4 = Eqn [S0] [Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn5 = Eqn [S1] [X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, CX1, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn6 = Eqn [T0] [Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn7 = Eqn [T1] [X1, CX1, T0inv, T1inv, w, X1, CX1, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn8 = Eqn [ZZ] [CX1, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1, CX1, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, T1, CX1, T1inv, T1, CX1, T1inv, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, CX1]

eqn9 = Eqn [T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0] []

eqn10 = Eqn [X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w] []

eqn11 = Eqn [X0, CH1, X0, X0, CH1, X0] []

eqn12 = Eqn [X0, CH1, X0, X0, CH1, X0] []

eqn13 = Eqn [X1, CX1, X1, CX1] []

eqn14 = Eqn [X1, CX1, X1, CX1] []

eqn15 = Eqn [Swap, Swap] []

eqn16 = Eqn [Swap, Swap] []

eqn17 = Eqn [CX1, CX1] []

eqn18 = Eqn [T1, CX1, T1inv, T1, CX1, T1inv] []

eqn19 = Eqn [T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1] [X1, CX1, T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0]

eqn20 = Eqn [X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1] [X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w]

eqn21 = Eqn [Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap, X0, CH1, X0] [X0, CH1, X0, Swap, X1, CX1, T0inv, T1inv, w, X1, CX1, Swap]

eqn22 = Eqn [Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap, X0, CH1, X0] [X0, CH1, X0, Swap, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, Swap]

eqn23 = Eqn [T0inv, T1inv, w, Swap] [Swap, T0inv, T1inv, w]

eqn24 = Eqn [X0, CX0, T0, CX0, X0, Swap] [Swap, X0, CX0, T0, CX0, X0]

eqn25 = Eqn [T0inv, T1inv, w, T1, CX1, T1inv] [CX1, T0inv, T1inv, w]

eqn26 = Eqn [X0, CX0, T0, CX0, X0, CX1] [T1, CX1, T1inv, X0, CX0, T0, CX0, X0]

eqn27 = Eqn [X0, CH1, X0, Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap] [Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap, X0, CH1, X0]

eqn28 = Eqn [X0, CH1, X0, Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv, Swap] [Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv, Swap, X0, CH1, X0]

eqn29 = Eqn [X0, CH1, X0, CX1] [CX1, X0, CH1, X0]

eqn30 = Eqn [X0, CH1, X0, T1, CX1, T1inv] [T1, CX1, T1inv, X0, CH1, X0]

eqn31 = Eqn [X1, CX1, CX1] [CX1, X1, CX1]

eqn32 = Eqn [X1, CX1, T1, CX1, T1inv] [T1, CX1, T1inv, X1, CX1]

eqn33 = Eqn [X1, CX1, Swap, X1, CX1] [Swap, X1, CX1, Swap]

eqn34 = Eqn [X1, CX1, Swap, X1, CX1] [Swap, X1, CX1, Swap]

eqn35 = Eqn [Swap, CX1, Swap] [CX1, Swap, CX1]

eqn36 = Eqn [Swap, T1, CX1, T1inv, Swap] [T1, CX1, T1inv, Swap, T1, CX1, T1inv]

eqn37 = Eqn [T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1] [X1, CX1, T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1]

eqn38 = Eqn [X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1] [X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1]

eqn39 = Eqn [T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X0, CH1, X0] [X0, CH1, X0, T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1]

eqn40 = Eqn [X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1, X0, CH1, X0] [X0, CH1, X0, X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1]

eqn41 = Eqn [X0, CH1, X0, X1, CX1] [X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X0, CH1, X0]

eqn42 = Eqn [X0, CH1, X0, X1, CX1] [X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X0, CH1, X0]

eqn43 = Eqn [X0, CH1, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, X0, CH1, X0] [T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, X0, CH1, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1]

eqn44 = Eqn [X0, CH1, X0, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CH1, X0] [X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CH1, X0, X0, CX0, T0, CX0, X0, T0inv, T1inv, w, X0, CX0, T0, CX0, X0, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1, X1, CX1, X0, CX0, T0, CX0, X0, X1, CX1, X1, CX1, T0inv, T1inv, w, X1, CX1]

eqn45 = Eqn [X0, CH1, X0, Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap, Swap, X0, CH1, X0, Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1] [Swap, X0, CH1, X0, Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, X0, CH1, X0, Swap, CX1, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, CX1, Swap]

eqn46 = Eqn [X0, CH1, X0, Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv, Swap, Swap, X0, CH1, X0, Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv] [ Swap, X0, CH1, X0, Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv, X0, CH1, X0, Swap, T1, CX1, T1inv, X1, CX1, Swap, X0, CH1, X0, Swap, X1, CX1, T1, CX1, T1inv, Swap]

-- ----------------------------------------------------------------------
-- ** Axioms:

rel_A = Eqn [T1, H1, T1inv, CX1, X1, T1, H1, T1inv, CX1, T1, H1, T1inv, CX1, X1, T1, H1, T1inv, CX1] []

rel_B = Eqn [CX1, T1, H1, T1, H1, T1inv, CX1, X1, T1, H1, T1inv, H1, T1inv, CX1, T1, H1, T1, H1, T1inv, CX1, X1, T1, H1, T1inv, H1, T1inv] []

rel_C = Eqn [CH1, H1, T1, CH1, CH0, H0, T0, CH0] [CH0, H0, T0, CH0, CH1, H1, T1, CH1]

proof_rel_A :: Der Gate
proof_rel_A = Lemma "axiom rel-A" rel_A

proof_rel_B :: Der Gate
proof_rel_B = Lemma "axiom rel-B" rel_B

proof_rel_C :: Der Gate
proof_rel_C = Lemma "axiom rel-C" rel_C

-- ----------------------------------------------------------------------
-- ** Explicit proofs of lemmas

-- | Prove an equation that is a conjugate of another.
proof_by_conjugation_from_axiom :: Eqn [Gate] -> [Gate] -> Der Gate -> Der Gate
proof_by_conjugation_from_axiom claim op proof_axiom
  | d == a = der7
  | otherwise = error "proof_by_conjugation_from_axiom"
  where
    axiom = eqn_of_der proof_axiom
    (rel, f0, g0) = one_sided_der axiom
    -- f0 :: rel === ε -> axiom
    -- g0 :: axiom -> rel === ε
    (a, der1) = normalize_der rel
    -- der1 : rel === a
    -- proof_axiom : axiom
    der2a = g0 proof_axiom
    -- der2a : rel === ε
    der3 = Symm der1 `trans` der2a
    -- der3 : a === ε
    (b, f1, g1) = one_sided_der claim
    (c, f2, g2) = conjugate_der op b
    (d, der4) = normalize_der c
    -- der4 : c === d == a
    der5 = der4 `trans` der3
    -- der5 : c === ε
    der6 = f2 der5
    -- der6 : b === ε
    der7 = f1 der6
    -- der7 : lemma_eqn1

-- This is an appealing and useful statement of rel_A, since there are
-- no Cliffords and the relation is easy to memorize.
lemma_relA = Eqn [R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), R (Pauli2 Plus I X), R (Pauli2 Plus Z X)] [R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z)]

proof_lemma_relA :: Der Gate
proof_lemma_relA = proof_by_conjugation_from_axiom lemma_relA ([ZZ,S1] ++ [R (Pauli2 Plus Z Z)]) proof_rel_A

-- Note that this is a relatively appealing statement of rel_A, since the Clifford operators are equal.
lemma_eqn21 = Eqn [R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), R (Pauli2 Plus I X), R (Pauli2 Plus Z X), ZZ, S1, Omega 7] [R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), ZZ, S1, Omega 7]

-- Note: normalize (one_sided rel_A)
-- == normalize (conjugate ([CX1] ++ invert [R (Pauli2 Plus I Z)]) (one_sided lemma_eqn1))

proof_lemma_eqn21 :: Der Gate
proof_lemma_eqn21 = Cong [] proof_lemma_relA [ZZ, S1, Omega 7]

lemma_eqn28 = Eqn [R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus Z Z), R (Pauli2 Plus I X), R (Pauli2 Plus Z X), R (Pauli2 Plus Z Y), S1, H1, ZZ, S0, S0, S0, S1, S1, Omega 6] [R (Pauli2 Plus Z Z), R (Pauli2 Plus I X), R (Pauli2 Plus Z X), R (Pauli2 Plus Z Y), R (Pauli2 Plus I X), R (Pauli2 Plus Z X), S1, H1, ZZ, S0, S0, S0, S1, S1, Omega 6]

-- normalize (one_sided lemma_eqn28)
-- ==
-- [R (Pauli2 Plus I Z),R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus Z X),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),S0,S0,Omega 5]

-- normalize (conjugate ([ZZ,H1,S1,S1,X0] ++ invert [R (Pauli2 Plus I X)] ++ invert [R (Pauli2 Plus I Z)]) (one_sided lemma_eqn28))
-- ==
-- normalize (lhs rel_B)

-- H1,H0,ZZ,H0,H1,ZZ,ZZ,H0,H1,ZZ,H0,H1,ZZ,H1,S1,S1,H0,S0,S0,H0

proof_lemma_eqn28 :: Der Gate
proof_lemma_eqn28 = proof_by_conjugation_from_axiom lemma_eqn28 ([ZZ,X0,H1,S1] ++ invert [R (Pauli2 Plus I Y)]) proof_rel_B

lemma_eqn30 = Eqn [R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), S1, H1, ZZ, S0, S0, S0, H1, Omega 7] [R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), R (Pauli2 Plus I X), R (Pauli2 Plus Z X), S1, H1, ZZ, S0, S0, S0, H1, Omega 7]

proof_lemma_eqn30 :: Der Gate
proof_lemma_eqn30 = Cong [] (Symm proof_lemma_relA) [S1, H1, ZZ, S0, S0, S0, H1, Omega 7]

lemma_eqn43 = Eqn [R (Pauli2 Plus I Y), R (Pauli2 Plus Z I), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), ZZ, S0, S0, S1, S1] [R (Pauli2 Plus I Z), R (Pauli2 Plus Z I), R (Pauli2 Plus Z Z), R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), ZZ, S0, S0, S1, S1]

-- normalize (lhs rel_A)
-- [R (Pauli2 Plus I Z),R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus Z Z),ZZ,S0,S0,S0,S1,S1,Omega 6]

-- normalize (conjugate ([S1,H1,R (Pauli2 Plus Z Z)]) (one_sided rel_A))
-- [R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I X),R (Pauli2 Plus Z X),S1,H1,ZZ,S0,S0,S0,S1,S1,H1,S1,S1,S1,Omega 6]

-- normalize $ one_sided lemma_eqn43
-- [R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),S0,S0,Omega 6]

-- normalize (invert (conjugate ([S1,H1,R (Pauli2 Plus Z Z)]) (one_sided rel_A)) ++ one_sided lemma_eqn43)
-- [R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),ZZ,S0,S0,S0,S1,S1,Omega 6]
-- == normalize (conjugate ([X0,H1,S1, R (Pauli2 Plus Z Z)]) (one_sided rel_A))

proof_lemma_eqn43 :: Der Gate
proof_lemma_eqn43 = der
  where
    (a, f1, g1) = one_sided_der lemma_eqn43
    -- f1 : a === ε -> lemma_eqn43
    -- g1 : lemma_eqn43 -> a === ε
    rela = Lemma "axiom rel-A" rel_A
    -- rela : rel_A
    (b, f2, g2) = one_sided_der rel_A
    -- f2 : b === ε -> rel_A
    -- g2 : rel_A -> b === ε
    (c, f3, g3) = conjugate_der [S1,H1,R (Pauli2 Plus Z Z)] b
    -- f3 : c === ε -> b === ε
    -- g3 : b === ε -> c === ε
    (cinv, i1, i2) = invert_der c
    -- i1 : c • cinv === ε
    -- i2 : cinv • c === ε
    (e, der1) = normalize_der (cinv ++ a)
    -- der1 : cinv • a === e
    (f, f5, g5) = conjugate_der [X0,H1,S1, R (Pauli2 Plus Z Z)] b
    -- f5 : f === ε -> b === ε
    -- g5 : b === ε -> f === ε
    (g, der2) = normalize_der f
    -- der2 : f === g == e
    der3 = g2 rela
    -- der3 : b === ε
    der4 = g3 der3
    -- der4 : c === ε
    der5 = g5 der3
    -- der5 : f === ε
    der6 = Symm der2 `trans` der5
    -- der6 : e === ε
    der7 = der1 `trans` der6
    -- der7 : cinv • a === ε
    der8 = Cong c der7 []
    -- der8 : c • cinv • a === c
    der9 = Cong [] i1 a
    -- der9 : c • cinv • a === a
    der10 = Symm der8 `trans` der9
    -- der10 : c === a
    der11 = Symm der10 `trans` der4
    -- der9 : a === ε
    der = f1 der11
    -- der : lemma_eqn43

lemma_eqn44 = Eqn [R (Pauli2 Plus I Y), R (Pauli2 Plus Z I), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), ZZ, S0, S0, S1, S1] [R (Pauli2 Plus I Z), R (Pauli2 Plus Z I), R (Pauli2 Plus Z Z), R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Z Z), ZZ, S0, S0, S1, S1]

proof_lemma_eqn44 :: Der Gate
proof_lemma_eqn44 = proof_lemma_eqn43
    
-- Graphs of relations:
--
--
--         IY       :      ZY  XY      YZ  YX       YY  ZI       XZ  |  XY
-- rel_C:        IZ :              ZI           XI           YZ      |      ZY ...
--         ZY       :      IY  YZ      XY  ZY        ZX IY       YX  |  XI
--
--                : IZ      IZ      IZ      IX |
-- rel_B:  ZZ  IX :     ZX      IY      IY     |     ZZ ...
--                : ZZ      ZZ      ZZ         | ZX
--
--            IX :   IZ   IY   ZZ |       IX
-- rel_A:  IZ    : *    *    *    |    *      * ...
--            ZX :   ZZ   ZY      | IZ    ZX

-- How do we translate the equation [TL_H 0 1,TL_H 2 3,TL_H 0 2,TL_H 1
-- 3] === [TL_H 0 2,TL_H 1 3,TL_H 0 1,TL_H 2 3]?

-- Haskell translation:
--
-- gates_of_twolevels (Cw, [TL_H 0 1]) == ([X0,S1inv,H1,T1inv,CX1,T1,H1,S1,X0],Cw)
-- gates_of_twolevels (Cw, [TL_H 2 3]) == ([T1,S1inv,H1,T1inv,CX1,T1,H1,S1,T1inv],Cw)
-- gates_of_twolevels (Cw, [TL_H 0 2]) == ([Swap,X0,S1inv,H1,T1inv,CX1,T1,H1,S1,X0,Swap],Cw)
-- gates_of_twolevels (Cw, [TL_H 1 3]) == ([Swap,T1,S1inv,H1,T1inv,CX1,T1,H1,S1,T1inv,Swap],Cw)
--
-- Note the use of Gray codes: each gate H01, H02, requires a T-count
-- of 2, arising from the controlled Hadamard gate, and each of H23,
-- H13 requires a T-count of 4, arising from the coset correction. So
-- the average T-count per twolevel-H is 3. The same is true for the RHS.

-- Agda translation:
--
-- (h **) Ω H₀₁ = ([X0, S1,H1,T1,H1,ZZ,H1,T1inv,H1,S1inv, X0], Ω)
-- (h **) Ω H₂₃ = ([Swap,T1,CX1,T1inv,X1,CX1,Swap,X0,S1,H1,T1,CX1,T1inv,H1,S1inv,X0,Swap,X1,CX1,T1,CX1,T1inv,Swap] , Ω)
-- (h **) Ω H₀₂ = ([Swap,X0,S1,H1,T1,CX1,T1inv,H1,S1inv,X0,Swap ] , Ω)
-- (h **) Ω H₁₃ = ([     T1,CX1,T1inv,X1,CX1,Swap,X0,S1,H1,T1,CX1,T1inv,H1,S1inv,X0,Swap,X1,CX1,T1,CX1,T1inv     ] , Ω)

-- The translations of H₂₃ and H₁₃ have T-count 6 instead of 4. Why?
-- Because H₂₃ is desugared to X₁₂ • X₂₃ • X₀₁ • X₁₂ • H₀₁ • X₁₂ • X₀₁
-- • X₂₃ • X₁₂, which requires *two* X₂₃ gates, each of which
-- generates T-count 2 in the Ω-coset. Unfortunately, these extra
-- T-gates do not immediately cancel out. We need to use rel_A to
-- cancel them.
--
-- So what if we first have a lemma showing that Swap,T1,CX1,T1inv,X1,CX1,Swap, X0,S1,H1,T1,CX1,T1inv,H1,S1inv,X0, Swap,X1,CX1,T1,CX1,T1inv,Swap === T1,S1inv,H1,T1inv,CX1,T1,H1,S1,T1inv?

lemma_46a :: Eqn [Gate]
lemma_46a = Eqn [T1,CX1,T1inv,X1,CX1,Swap,X0,CH1,X0,Swap,X1,CX1,T1,CX1,T1inv] [T0,CH0,T0inv]

proof_lemma_46a :: Der Gate
proof_lemma_46a = proof_by_conjugation_from_axiom lemma_46a [X0,CX0,CX1] proof_rel_A

lemma_eqn46 = Eqn [R (Pauli2 Plus I Y), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus I Y), R (Pauli2 Plus Y Z), R (Pauli2 Plus Z Y), R (Pauli2 Plus X Y), R (Pauli2 Plus Z I), R (Pauli2 Plus X Y), R (Pauli2 Plus Y Z), R (Pauli2 Plus X Z), R (Pauli2 Plus Z X), ZZ, H0, H1, ZZ, H0, S0, S0, H0, H1, S1, S1, H1, Omega 6] [R (Pauli2 Plus Y I), R (Pauli2 Plus Y Z), R (Pauli2 Plus Z I), R (Pauli2 Plus Y I), R (Pauli2 Plus Y Z), R (Pauli2 Plus X Z), R (Pauli2 Plus Y X), R (Pauli2 Plus Z Y), R (Pauli2 Plus I Z), R (Pauli2 Plus Y X), R (Pauli2 Plus Z Y), R (Pauli2 Plus Z X), ZZ, H0, H1, ZZ, H0, S0, S0, H0, H1, S1, S1, H1, Omega 6]

-- Note: (normalize $ one_sided lemma_eqn46) == (normalize $ one_sided rel_C)
proof_lemma_eqn46 :: Der Gate
proof_lemma_eqn46 = der
  where
    (a, f1, g1) = one_sided_der lemma_eqn46
    -- f1 :: a === ε -> lemma_eqn46
    -- g1 :: lemma_eqn46 -> a === ε
    (b, der1) = normalize_der a
    -- der1 :: a === b
    (c, f2, g2) = one_sided_der rel_C
    -- f2 :: c === ε -> rel_C
    -- g2 :: rel_C -> c === ε
    (d, der2) = normalize_der c
    -- der2 :: c === d == b
    relc = Lemma "axiom rel-C" rel_C
    -- relc : rel_C
    der3 = g2 relc
    -- der3 : c === ε
    der4 = der1 `trans` Symm der2 `trans` der3
    -- der4 : a === ε
    der = f1 der4
    -- der : lemma_eqn46
    
proof_eqn46 :: Der Gate
proof_eqn46 = der1 `trans` der2 `trans` der5 `trans` Symm der4 `trans` Symm der3
  where
    d = Lemma "lemma-eqn46a" lemma_46a
    der1 = Cong [X0,CH1,X0,Swap] d [Swap,Swap,X0,CH1,X0,Swap,T1,CX1,T1inv,X1,CX1,Swap,X0,CH1,X0,Swap,X1,CX1,T1,CX1,T1inv]
    -- der1 : lhs46 === [X0,CH1,X0,Swap,T0,CH0,T0inv,Swap,Swap,X0,CH1,X0,Swap,T1,CX1,T1inv,X1,CX1,Swap,X0,CH1,X0,Swap,X1,CX1,T1,CX1,T1inv]
    der2 = Cong [X0,CH1,X0,Swap,T0,CH0,T0inv,Swap,Swap,X0,CH1,X0,Swap] d []
    -- der2 : rhs (eqn_of_der der1) === [X0,CH1,X0,Swap,T0,CH0,T0inv,Swap,Swap,X0,CH1,X0,Swap,T0,CH0,T0inv]
    der3 = Cong [Swap,X0,CH1,X0,Swap] d [X0,CH1,X0,Swap,T1,CX1,T1inv,X1,CX1,Swap,X0,CH1,X0,Swap,X1,CX1,T1,CX1,T1inv,Swap]
    -- der3 : rhs46 === [Swap,X0,CH1,X0,Swap,T0,CH0,T0inv,X0,CH1,X0,Swap,T1,CX1,T1inv,X1,CX1,Swap,X0,CH1,X0,Swap,X1,CX1,T1,CX1,T1inv,Swap]
    der4 = Cong [Swap,X0,CH1,X0,Swap,T0,CH0,T0inv,X0,CH1,X0,Swap] d [Swap]
    -- der4 : rhs (eqn_of_der der3) === [Swap,X0,CH1,X0,Swap,T0,CH0,T0inv,X0,CH1,X0,Swap,T0,CH0,T0inv,Swap]
    der5 = prove_equation_from_lemma (Eqn (rhs (eqn_of_der der2)) (rhs (eqn_of_der der4)))  proof_lemma_eqn46
    -- der5 : rhs (eqn_of_der der2) === rhs (eqn_of_der der4)

-- ----------------------------------------------------------------------
-- * Output

-- | Top-level function: output a proof of the given equation.
prove :: Eqn [Gate] -> String -> IO ()
prove eqn name = do
  let d = prove_equation eqn ("lemma-" ++ name)
  print_der d name

-- | Output a proof of the given equation, using normalization and a lemma.
prove_from_lemma :: Der Gate -> Eqn [Gate] -> String -> IO ()
prove_from_lemma lemma eqn name = do
  let d = prove_equation_from_lemma eqn lemma
  print_der d name

main7 :: IO ()
main7 = do
  args <- getArgs
  case args of
    ["--help"] -> usage stdout
    [n] -> process_eqn (read n)
    _ -> usage stderr
  where
    process_eqn :: Int -> IO ()
    process_eqn 1 = prove eqn1 "eqn1"
    process_eqn 2 = prove eqn2 "eqn2"
    process_eqn 3 = prove eqn3 "eqn3"
    process_eqn 4 = prove eqn4 "eqn4"
    process_eqn 5 = prove eqn5 "eqn5"
    process_eqn 6 = prove eqn6 "eqn6"
    process_eqn 7 = prove eqn7 "eqn7"
    process_eqn 8 = prove eqn8 "eqn8"
    process_eqn 9 = prove eqn9 "eqn9"
    process_eqn 10 = prove eqn10 "eqn10"
    process_eqn 11 = prove eqn11 "eqn11"
    process_eqn 12 = prove eqn12 "eqn12"
    process_eqn 13 = prove eqn13 "eqn13"
    process_eqn 14 = prove eqn14 "eqn14"
    process_eqn 15 = prove eqn15 "eqn15"
    process_eqn 16 = prove eqn16 "eqn16"
    process_eqn 17 = prove eqn17 "eqn17"
    process_eqn 18 = prove eqn18 "eqn18"
    process_eqn 19 = prove eqn19 "eqn19"
    process_eqn 20 = prove eqn20 "eqn20"
    process_eqn 21 = prove_from_lemma proof_lemma_eqn21 eqn21 "eqn21"
    process_eqn 22 = prove eqn22 "eqn22"
    process_eqn 23 = prove eqn23 "eqn23"
    process_eqn 24 = prove eqn24 "eqn24"
    process_eqn 25 = prove eqn25 "eqn25"
    process_eqn 26 = prove eqn26 "eqn26"
    process_eqn 27 = prove eqn27 "eqn27"
    process_eqn 28 = prove_from_lemma proof_lemma_eqn28 eqn28 "eqn28"
    process_eqn 29 = prove eqn29 "eqn29"
    process_eqn 30 = prove_from_lemma proof_lemma_eqn30 eqn30 "eqn30"
    process_eqn 31 = prove eqn31 "eqn31"
    process_eqn 32 = prove eqn32 "eqn32"
    process_eqn 33 = prove eqn33 "eqn33"
    process_eqn 34 = prove eqn34 "eqn34"
    process_eqn 35 = prove eqn35 "eqn35"
    process_eqn 36 = prove eqn36 "eqn36"
    process_eqn 37 = prove eqn37 "eqn37"
    process_eqn 38 = prove eqn38 "eqn38"
    process_eqn 39 = prove eqn39 "eqn39"
    process_eqn 40 = prove eqn40 "eqn40"
    process_eqn 41 = prove eqn41 "eqn41"
    process_eqn 42 = prove eqn42 "eqn42"
    process_eqn 43 = prove_from_lemma proof_lemma_eqn43 eqn43 "eqn43"
    process_eqn 44 = prove_from_lemma proof_lemma_eqn44 eqn44 "eqn44"
    process_eqn 45 = prove eqn45 "eqn45"
    process_eqn 46 = do
      print_der proof_lemma_46a "lemma-eqn46a"
      print_der proof_eqn46 "eqn46"
    process_eqn n = hPutStrLn stderr ("Unknown: " ++ show n)

    usage fout = hPutStrLn fout "Usage: Syllables <n>"

-- ----------------------------------------------------------------------
-- * Some automation

-- | The following function can be adapted to search through all
-- conjugates of a given circuit /a/, to see if it is equal (modulo
-- normalization) to another given circuit /b/. The main function
-- takes two arguments (main8 n m) to search the Clifford operators
-- numbered from n to m. This can be used to parallelize the search on
-- multiple processors.

main8 = do
  [x,y] <- getArgs
  let i0 = read x :: Int
  let i1 = read y :: Int
  let clifs = drop i0 (take i1 all_clifford2)
  let a = [R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I Y),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),ZZ,S0,S0,S0,S1,S1,Omega 6]
  let b = normalize (conjugate ([R (Pauli2 Plus Z Z)]) (one_sided rel_A))
  let list = [ (g,n,yes) | (g,n) <- zip clifs [0..], let yes = normalize (conjugate g a) `good_enough` b, yes ]
  sequence_ [ print x | x <- list ]
  where
    good_enough xs ys = take 11 xs == take 11 ys

-- ----------------------------------------------------------------------

main = main7

-- ----------------------------------------------------------------------
-- * Generate all 2-qubit Clifford operators (up to scalars)

clifford_A0s = [[],[H0],[H0,S0,H0]]
clifford_A1s = [[],[H1],[H1,S1,H1]]
clifford_Bs = [
  [H1,ZZ,H0,H1,ZZ,H0,H1,ZZ],
  [ZZ,H0,H1,ZZ],
  [H0,S0,ZZ,H0,H1,ZZ],
  [H0,ZZ,H0,H1,ZZ]
  ]
clifford_C0s = [[],[H0,S0,S0,H0]]
clifford_C1s = [[],[H1,S1,S1,H1]]
clifford_Ds = [
  [ZZ,H0,H1,ZZ,H0,H1,ZZ,H1],
  [H0,ZZ,H0,H1,ZZ,H1],
  [H0,H1,S1,ZZ,H0,H1,ZZ,H1],
  [H0,H1,ZZ,H0,H1,ZZ,H1]
  ]
clifford_E0s = [[],[S0],[S0,S0],[S0,S0,S0]]
clifford_E1s = [[],[S1],[S1,S1],[S1,S1,S1]]

clifford_L2s =
  [ a ++ b ++ c | a <- clifford_A1s, b <- clifford_Bs, c <- clifford_C0s ]
  ++ [ a ++ c | a <- clifford_A0s, c <- clifford_C0s ]

clifford_L1s = 
  [ a ++ c | a <- clifford_A0s, c <- clifford_C0s ]

clifford_M2s =
  [ d ++ e | d <- clifford_Ds, e <- clifford_E1s ]

clifford_M1s =
  [ e | e <- clifford_E0s ]

-- | A list of all 11520 2-qubit Clifford operators (up to scalars).
clifford_2s =
  [ l2 ++ m2 ++ l1 ++ m1 | l2 <- clifford_L2s, m2 <- clifford_M2s, l1 <- clifford_L1s, m1 <- clifford_M1s ]

-- | A list of 2-qubit Clifford operators (up to scalars) that commute
-- with I⊗Z.
clifford_2s_IZ =
  [ [H1,ZZ,H0,H1,ZZ,H0,H1,ZZ] ++ m2 ++ l1 ++ m1 | m2 <- clifford_M2s, l1 <- clifford_L1s, m1 <- clifford_M1s ]

-- Double-check that they do indeed commute with I⊗Z, or equivalently S1:
-- length [ c | c <- clifford_2s_IZ, let c1 = simplify_clifford c, check_gate_relation (Eqn (c1 ++ [S1]) ([S1] ++ c1))]
-- 384

-- | A list of 2-qubit Clifford operators (up to scalars) that commute
-- with Z⊗I.
clifford_2s_ZI =
  [ [Swap] ++ c ++ [Swap] | c <- clifford_2s_IZ ]

-- To generate a list of all Clifford conjugates of rel_B by Clifford
-- operators that commute with ZI:
-- 
-- > sequence_ [ print $ normalize (conjugate c (one_sided rel_B)) | c <- clifford_2s_ZI ]
--
-- None of them have empty Clifford tail (not even up to scalars).
--
-- We could try two-sided presentations, which give an additional
-- degree of freedom.

-- > x = normalize (one_sided rel_B)
-- > x1 = take 6 x
-- > x2 = invert (drop 6 x)
-- > isr x = case x of { R _ -> True; _ -> False }
-- > cpart xs = dropWhile isr xs
-- > cconj x c = cpart (normalize (conjugate c x))
-- > works c = cconj x1 c == cconj x2 c
-- > works2 c = check_equation (Eqn (cconj x1 c) (cconj x2 c))
-- > sequence_ [ print c | c <- clifford_2s_ZI, works2 c ]
-- [Swap,H1,ZZ,H0,H1,ZZ,H0,H1,ZZ,ZZ,H0,H1,ZZ,H0,H1,ZZ,H1,Swap]
-- [Swap,H1,ZZ,H0,H1,ZZ,H0,H1,ZZ,ZZ,H0,H1,ZZ,H0,H1,ZZ,H1,S0,Swap]
-- [Swap,H1,ZZ,H0,H1,ZZ,H0,H1,ZZ,ZZ,H0,H1,ZZ,H0,H1,ZZ,H1,H0,Swap]
-- ... and many others.
-- > sequence_ [ print (normalize (conjugate c x1), normalize (conjugate c x2)) | c <- clifford_2s_ZI, works2 c ]
-- ([R (Pauli2 Plus Z Z),R (Pauli2 Plus I X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus Z X),R (Pauli2 Plus I Z)],[R (Pauli2 Plus I Z),R (Pauli2 Plus I X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus Z X),R (Pauli2 Plus Z Z)])
-- ... and many others

--
-- > xx = drop 1 x ++ take 1 x
-- > x1 = take 6 xx
-- > x2 = invert (drop 6 xx)
-- > works2 c = check_equation (Eqn (cconj x1 c) (cconj x2 c))
-- > sequence_ [ print c | c <- clifford_2s_ZI, works2 c ]
-- ([R (Pauli2 Plus I Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus Z Y),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z)],[R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus Z X),R (Pauli2 Plus I Z),R (Pauli2 Plus Z Z),R (Pauli2 Plus I X)])
-- ([R (Pauli2 Plus I Z),R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus Z Z),R (Pauli2 Plus I X),R (Pauli2 Plus Z X)],[R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus Z Y),R (Pauli2 Plus I X),R (Pauli2 Plus Z X),R (Pauli2 Plus I Y)])
-- ... and many others

-- Compile with:
--
-- ghc Syllables.hs -main-is show_relAs -o show_relAs
show_relAs :: IO ()
show_relAs = sequence_ [ process i | i <- [0..3] ]
  where
    process i = do
      let xx = drop i x ++ take i x
      let x1 = take 4 xx
      let x2 = invert (drop 4 xx)
      sequence_ [ output x1 x2 c | c <- clifford_2s_ZI, works2 x1 x2 c ]

    output x1 x2 c = do
      let lhs = rpart (normalize (conjugate c x1))
      let rhs = rpart (normalize (conjugate c x2))
      putStrLn ("  " ++ latex_of_eqn (Eqn lhs rhs))
      hFlush stdout
      

    x = normalize (one_sided rel_A)
    isr x = case x of { R _ -> True; _ -> False }
    rpart xs = takeWhile isr xs
    cpart xs = dropWhile isr xs
    cconj x c = normalize (conjugate c x)
    works2 x1 x2 c = check_equation (Eqn (cpart (cconj x1 c)) (cpart (cconj x2 c)))

-- One-sided relation A.
-- Compile with:
--
-- ghc Syllables.hs -main-is show_relAs1 -o show_relAs1
--
-- Note: there's no output (no one-sided presentations found).
show_relAs1 :: IO ()
show_relAs1 = sequence_ [ process i | i <- [0..7] ]
  where
    process i = do
      let xx = drop i x ++ take i x
      let x1 = xx
      let x2 = []
      sequence_ [ output x1 x2 c | c <- clifford_2s_ZI, works2 x1 x2 c ]

    output x1 x2 c = do
      let lhs = rpart (normalize (conjugate c x1))
      let rhs = rpart (normalize (conjugate c x2))
      putStrLn ("  " ++ latex_of_eqn (Eqn lhs rhs))
      hFlush stdout
      

    x = normalize (one_sided rel_A)
    isr x = case x of { R _ -> True; _ -> False }
    rpart xs = takeWhile isr xs
    cpart xs = dropWhile isr xs
    cconj x c = normalize (conjugate c x)
    works2 x1 x2 c = check_equation (Eqn (cpart (cconj x1 c)) (cpart (cconj x2 c)))

show_relBs :: IO ()
show_relBs = sequence_ [ process i | i <- [0..5] ]
  where
    process i = do
      let xx = drop i x ++ take i x
      let x1 = take 6 xx
      let x2 = invert (drop 6 xx)
      sequence_ [ output x1 x2 c | c <- clifford_2s_ZI, works2 x1 x2 c ]

    output x1 x2 c = do
      let lhs = rpart (normalize (conjugate c x1))
      let rhs = rpart (normalize (conjugate c x2))
      putStrLn ("  " ++ latex_of_eqn (Eqn lhs rhs))
      hFlush stdout
      

    x = normalize (one_sided rel_B)
    isr x = case x of { R _ -> True; _ -> False }
    rpart xs = takeWhile isr xs
    cpart xs = dropWhile isr xs
    cconj x c = normalize (conjugate c x)
    works2 x1 x2 c = check_equation (Eqn (cpart (cconj x1 c)) (cpart (cconj x2 c)))

relCs :: [Eqn [Gate]]
relCs = concat [ process i | i <- [0..9] ]
  where
    x = normalize (one_sided rel_C)
    isr x = case x of { R _ -> True; _ -> False }
    rpart xs = takeWhile isr xs
    cpart xs = dropWhile isr xs
    cconj x c = normalize (conjugate c x)
    works2 x1 x2 c = check_equation (Eqn (cpart (cconj x1 c)) (cpart (cconj x2 c)))

    process i = res
      where
        xx = drop i x ++ take i x
        x1 = take 10 xx
        x2 = invert (drop 10 xx)
        res = [ output x1 x2 c | c <- clifford_2s, works2 x1 x2 c ]

    output x1 x2 c = res
      where
        lhs = rpart (normalize (conjugate c x1))
        rhs = rpart (normalize (conjugate c x2))
        res = Eqn lhs rhs

relCs_special :: [Eqn [Gate]]
relCs_special = [ eqn | eqn <- relCs, is_special eqn ]
  where
    is_special (Eqn lhs rhs) = lhs1 == rhs2 && lhs2 == rhs1
      where
        (lhs1, lhs2) = splitAt 5 lhs
        (rhs1, rhs2) = splitAt 5 rhs

-- Compile with:
--
-- ghc Syllables.hs -main-is show_relCs
show_relCs :: IO ()
show_relCs = sequence_ [ output eqn | eqn <- relCs_special ]
  where
    output (Eqn lhs rhs) = do
      putStrLn ("  " ++ latex_of_eqn (Eqn lhs rhs))
      hFlush stdout

-- ----------------------------------------------------------------------
-- * What is we work with H-syllables instead of T-syllables?

-- $ Idea: the 2-qubit Clifford+T circuits are generated by two finite
-- subgroups:
--
-- * Clifford: e.g. CX0, CX1, H0, S0
--
-- * Diagonals + Permutations: T0, X0, CX0, CX1, Swap, S0, etc.
--
-- Instead of considering conjugates of T0 by Clifford operators, we
-- can also consider conjugates of H0 by Diagonal+Permutation
-- operators. This gives a different kind of syllable. Bian was very
-- successful with this for 3-qubit Clifford+CS.

-- | Permutations: there are 4! = 24 permutations for a 2-qubit
-- (4-level) system.  They are generated by CX0 = (13), CX1 = (23),
-- and X0 = (02)(13). They are:
-- perms :: [[Gate]]
-- perms = [
--   [], -- 0123
--   ...
  
