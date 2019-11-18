module Term where

import Control.Monad
import Data.Char
import Data.Foldable
import Data.Functor.Identity
import Data.List
import Data.Maybe
import Prelude hiding ((<>))
import Text.Parsec.Prim
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.PrettyPrint.HughesPJ as P

type VarName = String
type ConName = String
type FuncName = String
type DeBruijnIndex = Int

data Term = Free VarName                           -- free variable
          | Bound DeBruijnIndex                    -- bound variable with de Bruijn index
          | Lambda VarName Term                    -- lambda abstraction
          | Con ConName [Term]                     -- constructor application
          | Fun FuncName                           -- function call
          | Apply Term [Term]                      -- application
          | Case Term [(ConName, [VarName], Term)] -- case expression
          | Let VarName Term Term                  -- temporary let expression
          | Letrec FuncName [String] Term Term     -- local function
          -- Q: what is [String] stands for?

instance Show Term where
        show t = render $ prettyTerm t

type Prog = (Term, [(String, ([String], Term))])

showProg :: (Term, [(String, ([String], Term))]) -> String
showProg p = render $ prettyProg p

-- equality of terms

instance Eq Term where
        (==) t t' = eqTerm [] [] (t, t')

eqTerm :: [(String, Term)] -> [(String, Term)] -> (Term, Term) -> Bool
eqTerm s1 s2 (Free x, t)
  | x `elem` fst (unzip s1) =
    eqTerm [] [] (instantiate s1 (Free x), instantiate s2 t)
eqTerm _ _ (Free x, Free x') = x == x'
eqTerm _ _ (Bound i, Bound i') = i == i'
eqTerm s1 s2 (Lambda _ t, Lambda _ t') = eqTerm s1 s2 (t, t')
eqTerm s1 s2 (Con c ts, Con c' ts') | c == c' = all (eqTerm s1 s2) (zip ts ts')
eqTerm _ _ (Fun f, Fun f') = f == f'
-- Q: is there no need to check second arg of Apply (Bound _)?
eqTerm _ _ (Apply (Bound i) _, Apply (Bound i') _) = i == i'
eqTerm s1 s2 (Apply t ts, Apply t' ts')
  = eqTerm s1 s2 (t, t') && all (eqTerm s1 s2) (zip ts ts')
eqTerm s1 s2 (Case t bs, Case t' bs')
  | match bs bs' =
    eqTerm s1 s2 (t, t') &&
    -- Q: should ConNames be compared in Case?
      all (\ ((_, _, t1), (_, _, t2)) -> eqTerm s1 s2 (t1, t2)) (zip bs bs')
eqTerm s1 s2 (Let _ t u, Let _ t' u')
  = eqTerm s1 s2 (t, t') && eqTerm s1 s2 (u, u')
eqTerm s1 s2 (Letrec _ xs t u, Letrec _ xs' t' u')
  = eqTerm (zip xs (args (instantiate s1 u)))
           (zip xs' (args (instantiate s2 u')))
           (foldr concrete t xs, foldr concrete t' xs')
eqTerm _ _ (_, _) = False

-- context surrounding redex

data Context = EmptyCtx
             | ApplyCtx Context [Term]
             | CaseCtx Context [(String, [String], Term)]

-- place term in context
place :: Term -> Context -> Term
place t EmptyCtx = t
place t (ApplyCtx k ts) = place (Apply t ts) k
place t (CaseCtx k bs) = place (Case t bs) k

match :: (Eq a1, Foldable t1, Foldable t2) 
   => [(a1, t1 a2, c1)] -> [(a1, t2 a3, c2)] 
   -> Bool
match bs bs'
  = length bs == length bs' &&
      all (\ ((c, xs, _), (c', xs', _)) -> c == c' && length xs == length xs')
        (zip bs bs')

-- checking for renaming
renaming :: Term -> Term -> Maybe [(String, String)]
renaming t u = renaming' [] [] t u []

renaming'
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [(String, String)]
   -> Maybe [(String, String)]
renaming' s1 s2 (Free x) t r
  | x `elem` fst (unzip s1) =
    renaming' [] [] (instantiate s1 (Free x)) (instantiate s2 t) r
renaming' _ _ (Free x) (Free x') r
  = if x `elem` fst (unzip r) then if (x, x') `elem` r then Just r else Nothing
      else Just ((x, x') : r)
renaming' _ _ (Bound i) (Bound i') r | i == i' = Just r
renaming' s1 s2 (Lambda _ t) (Lambda _ t') r = renaming' s1 s2 t t' r
renaming' s1 s2 (Con c ts) (Con c' ts') r
  | c == c' = foldrM (\ (t, t') r' -> renaming' s1 s2 t t' r') r (zip ts ts')
renaming' _ _ (Fun f) (Fun f') s | f == f' = Just s
renaming' _ _ (Apply (Bound i) _) (Apply (Bound i') _) r | i == i' = Just r
renaming' s1 s2 (Apply t ts) (Apply t' ts') r
  = renaming' s1 s2 t t' r >>=
      (\ r' -> foldrM (\ (t1, t2) r'' -> renaming' s1 s2 t1 t2 r'') r' (zip ts ts'))
renaming' s1 s2 (Case t bs) (Case t' bs') r
  | match bs bs' =
    renaming' s1 s2 t t' r >>=
      (\ r' ->
         foldrM (\ ((_, _, t1), (_, _, t2)) r'' -> renaming' s1 s2 t1 t2 r'') r'
           (zip bs bs'))
renaming' s1 s2 (Let _ t u) (Let _ t' u') r
  = renaming' s1 s2 t t' r >>= renaming' s1 s2 u u'
renaming' s1 s2 (Letrec _ xs t u) (Letrec _ xs' t' u') r
  = renaming' (zip xs (args (instantiate s1 u)))
      (zip xs' (args (instantiate s2 u')))
      (foldr concrete t xs)
      (foldr concrete t' xs')
      r
renaming' _ _ _ _ _ = Nothing

-- checking for instance
inst :: Term -> Term -> Maybe [(String, Term)]
inst t u = inst' [] [] t u []

inst'
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [(String, Term)]
   -> Maybe [(String, Term)]
inst' s1 s2 (Free x) t s
  | x `elem` fst (unzip s1) =
    inst' [] [] (instantiate s1 (Free x)) (instantiate s2 t) s
inst' _ _ (Free x) t s
  = if x `elem` fst (unzip s) then if (x, t) `elem` s then Just s else Nothing
      else Just ((x, t) : s)
inst' _ _ (Bound i) (Bound i') s | i == i' = Just s
inst' s1 s2 (Lambda _ t) (Lambda _ t') s = inst' s1 s2 t t' s
inst' s1 s2 (Con c ts) (Con c' ts') s
  | c == c' = foldrM (\ (t, t') s' -> inst' s1 s2 t t' s') s (zip ts ts')
inst' _ _ (Fun f) (Fun f') s | f == f' = Just s
inst' _ _ (Apply (Bound i) _) (Apply (Bound i') _) s | i == i' = Just s
inst' s1 s2 (Apply t ts) (Apply t' ts') s
  = inst' s1 s2 t t' s >>=
      (\ s' -> foldrM (\ (t1, t2) s'' -> inst' s1 s2 t1 t2 s'') s' (zip ts ts'))
inst' s1 s2 (Case t bs) (Case t' bs') s
  | match bs bs' =
    inst' s1 s2 t t' s >>=
      (\ s' ->
         foldrM (\ ((_, _, t1), (_, _, t2)) s'' -> inst' s1 s2 t1 t2 s'') s'
           (zip bs bs'))
inst' s1 s2 (Let _ t u) (Let _ t' u') s
  = inst' s1 s2 t t' s >>= inst' s1 s2 u u'
inst' s1 s2 (Letrec _ xs t u) (Letrec _ xs' t' u') s
  = inst' (zip xs (args (instantiate s1 u)))
      (zip xs' (args (instantiate s2 u')))
      (foldr concrete t xs)
      (foldr concrete t' xs')
      s
inst' _ _ _ _ _ = Nothing

-- checking for embedding for generalisation
embed :: Term -> Term -> [[(String, String)]]
embed t u = couple [] [] t u []

embedding
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [(String, String)]
   -> [[(String, String)]]
embedding s1 s2 t u r = couple s1 s2 t u r ++ dive s1 s2 t u r

couple
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [(String, String)]
   -> [[(String, String)]]
couple s1 s2 (Free x) (Free x') r
  | x `elem` fst (unzip s1) && x' `elem` fst (unzip s2) =
    embedding [] [] (instantiate s1 (Free x)) (instantiate s2 (Free x')) r
couple _ _ (Free x) (Free x') r
  = if x `elem` fst (unzip r) then [r | (x, x') `elem` r] else [(x, x') : r]
couple _ _ (Bound i) (Bound i') r | i == i' = [r]
couple s1 s2 (Lambda _ t) (Lambda _ t') r = embedding s1 s2 t t' r
couple s1 s2 (Con c ts) (Con c' ts') r
  | c == c' =
    foldr (\ (t, t') rs -> concat [embedding s1 s2 t t' r' | r' <- rs]) [r]
      (zip ts ts')
couple _ _ (Fun f) (Fun f') r | f == f' = [r]
couple _ _ (Apply (Bound i) _) (Apply (Bound i') _) r | i == i' = [r]
couple s1 s2 (Apply t ts) (Apply t' ts') r
  = foldr (\ (t1, t2) rs -> concat [embedding s1 s2 t1 t2 r'| r' <- rs])
      (embedding s1 s2 t t' r)
      (zip ts ts')
couple s1 s2 (Case t bs) (Case t' bs') r
  | match bs bs' =
    foldr
      (\ ((_, _, t1), (_, _, t2)) rs ->
         concat [embedding s1 s2 t1 t2 r' | r' <- rs])
      (embedding s1 s2 t t' r)
      (zip bs bs')
couple s1 s2 (Let _ t u) (Let _ t' u') r
  = concat [embedding s1 s2 u u' r' | r' <- embedding s1 s2 t t' r]
couple s1 s2 (Letrec _ xs t u) (Letrec _ xs' t' u') r
  = couple (zip xs (args (instantiate s1 u)))
      (zip xs' (args (instantiate s2 u')))
      (foldr concrete t xs)
      (foldr concrete t' xs')
      r
couple _ _ _ _ _ = []

dive
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [(String, String)]
   -> [[(String, String)]]
dive s1 s2 t (Lambda x t') r = embedding s1 s2 t (concrete x t') r
dive s1 s2 t (Con _ ts) r = concat [embedding s1 s2 t t' r | t' <- ts]
dive s1 s2 t (Apply t' ts) r
  = embedding s1 s2 t t' r ++ concat [embedding s1 s2 t u r | u <- ts]
dive s1 s2 t (Case t' bs) r
  = embedding s1 s2 t t' r ++
      concatMap (\ (_, xs, t'') -> embedding s1 s2 t (foldr concrete t'' xs) r) bs
dive s1 s2 t (Let x t' u) r
  = embedding s1 s2 t t' r ++ embedding s1 s2 t (concrete x u) r
dive s1 s2 t (Letrec _ xs t' u) r
  = embedding s1 s2 t u r ++ embedding s1 s2 t (foldr concrete t' xs) r
dive _ _ _ _ _ = []

-- most specific generalisation of terms
generalise :: Term -> Term -> (Term, [(String, Term)], [(String, Term)])
generalise t u = generalise' [] [] t u (free t ++ free u) [] [] []

generalise'
   :: [(String, Term)]
   -> [(String, Term)]
   -> Term
   -> Term
   -> [String]
   -> [String]
   -> [(String, Term)]
   -> [(String, Term)]
   -> (Term, [(String, Term)], [(String, Term)])
generalise' s1 s2 (Free x) t fv bv g1 g2
  | x `elem` fst (unzip s1) =
    let (t', g1', g2')
          = generalise' [] [] (instantiate s1 (Free x)) (instantiate s2 t) fv bv
              g1
              g2
      in
      case t' of
          Free x' -> (Free x, (x, fromJust (lookup x' g1')) : g1,
                      (x, fromJust (lookup x' g2')) : g2)
          _ -> (t', g1', g2')
generalise' _ _ (Free x) (Free x') _ _ g1 g2 | x == x' = (Free x, g1, g2)
generalise' _ _ (Bound i) (Bound i') _ _ g1 g2 | i == i' = (Bound i, g1, g2)
generalise' s1 s2 (Lambda x t) (Lambda _ t') fv bv g1 g2
  = let x'' = rename (fv ++ fst (unzip (s2 ++ g2))) x
        (t'', g1', g2')
          = generalise' s1 s2 (concrete x'' t) (concrete x'' t') (x'' : fv)
              (x'' : bv)
              g1
              g2
      in (Lambda x (abstract t'' x''), g1', g2')
generalise' s1 s2 (Con c ts) (Con c' ts') fv bv g1 g2
  | c == c' =
    let ((g1', g2'), ts'')
          = mapAccumL
              (\ (g11, g22) (t, t') ->
                 let (t'', g11', g22') = generalise' s1 s2 t t' fv bv g11 g22 in
                   ((g11', g22'), t''))
              (g1, g2)
              (zip ts ts')
      in (Con c ts'', g1', g2')
generalise' _ _ (Fun f) (Fun f') _ _ g1 g2 | f == f' = (Fun f, g1, g2)
generalise' _ _ (Apply (Free x) ts) (Apply (Free x') _) _ bv g1 g2
  | x `elem` bv && x == x' = (Apply (Free x) ts, g1, g2)
generalise' s1 s2 (Apply t ts) (Apply t' ts') fv bv g1 g2
  | not (null (embed t t')) =
    let (t'', g1', g2') = generalise' s1 s2 t t' fv bv g1 g2
        ((g1'', g2''), ts'')
          = mapAccumL
              (\ (g11, g22) (t0, t1) ->
                 let (t2, g11', g22') = generalise' s1 s2 t0 t1 fv bv g11 g22
                 in ((g11', g22'), t2))
              (g1', g2')
              (zip ts ts')
    in (Apply t'' ts'', g1'', g2'')
generalise' s1 s2 (Case t bs) (Case t' bs') fv bv g1 g2 | match bs bs' = 
  let (t'', g1', g2') = generalise' s1 s2 t t' fv bv g1 g2
      ((g1'', g2''), bs'')
        = mapAccumL 
          (\ (g11, g22) ((c, xs, t0), (_, _, t1)) -> 
            let fv' = foldr (\x fvs -> let x' = rename (fvs ++ fst(unzip (s2 ++ g22))) x in x':fvs) fv xs
                xs'' = take (length xs) fv'
                (t2, g11', g22') = generalise' s1 s2 (foldr concrete t0 xs'') (foldr concrete t1 xs'') fv' (xs'' ++ bv) g11 g22
            in ((g11',g22'),(c,xs,foldl abstract t2 xs'')))
          (g1',g2') 
          (zip bs bs')
  in (Case t'' bs'',g1'',g2'')
generalise' s1 s2 (Let x t u) (Let _ t' u') fv bv g1 g2
  = let x'' = rename (fv ++ fst (unzip (s2 ++ g2))) x
        (t'', g1', g2') = generalise' s1 s2 t t' fv bv g1 g2
        (u'', g1'', g2'')
          = generalise' s1 s2 (concrete x'' u) (concrete x'' u') fv bv g1' g2'
      in (Let x t'' (abstract u'' x''), g1'', g2'')
generalise' s1 s2 (Letrec f xs t u) (Letrec _ xs' t' u') fv bv g1 g2
  | not (null rs) =
    let xs1 = [renameVar (head rs) x' | x' <- xs]
        (t'', g1', g2')
          = generalise' (zip xs1 (args (instantiate s1 u)))
              (zip xs2 (args (instantiate s2 u')))
              (foldr concrete t (x : xs1))
              (foldr concrete t' (x : xs2))
              (x : xs1 ++ fv)
              (x : xs1 ++ bv)
              g1
              g2
      in
      (Letrec f xs1 (foldl abstract t'' (x : xs1))
         (Apply (Bound 0) (map Free xs1)),
       g1', g2')
  where x : fv'
          = foldr
              (\ x' fvs ->
                 let x'' = rename (fvs ++ fst (unzip (s2 ++ g2))) x' in x'' : fvs)
              fv
              (f : xs')
        xs2 = take (length xs') fv'
        rs = embed (foldr concrete t xs) (foldr concrete t' xs2)
generalise' s1 s2 t u fv bv g1 g2
  = let xs = intersect (free t) bv
        t' = instantiate s1 (foldl (\ t'' x -> Lambda x (abstract t'' x)) t xs)
        u' = instantiate s2 (foldl (\ t'' x -> Lambda x (abstract t'' x)) u xs)
      in
      case find (\ (x, t'') -> t'' == t' && (lookup x g2 == Just u')) g1 of
          Just (x, _) -> (makeApplication (Free x) (map Free xs), g1, g2)
          Nothing -> let x = rename (fv ++ fst (unzip (s2 ++ g2))) "x" in
                       (makeApplication (Free x) (map Free xs), (x, t') : g1,
                        (x, u') : g2)

makeLet :: Foldable t => t (String, Term) -> Term -> Term
makeLet s t = foldl (\ u (x, t') -> Let x t' (abstract u x)) t s

makeApplication :: Term -> [Term] -> Term
makeApplication t [] = t
makeApplication t ts = Apply t ts

eval :: Num a => Term -> Context -> [(String, ([String], Term))] -> Int -> a
   -> (Term, Int, a)
eval t (ApplyCtx k []) d r a = eval t k d r a
eval (Free x) _ _ _ _ = error ("Unbound identifier: " ++ x)
eval (Lambda x t) EmptyCtx _ r a = (Lambda x t, r, a)
eval (Lambda _ t) (ApplyCtx k (t' : ts)) d r a
  = eval (subst t' t) (ApplyCtx k ts) d (r + 1) a
eval (Lambda x t) (CaseCtx _ _) _ _ _
  = error ("Unapplied function in case selector: " ++ show (Lambda x t))
eval (Con c ts) EmptyCtx d r a
  = let ((r', a'), ts')
          = mapAccumL
              (\ (r1, a1) t ->
                 let (t', r'', a'') = eval t EmptyCtx d r1 a1 in ((r'', a''), t'))
              (r, a)
              ts
      in (Con c ts', r' + 1, a' + 1)
eval (Con c ts) (ApplyCtx k ts') _ _ _
  = error
      ("Constructor application is not saturated: " ++
         show (place (Con c ts) (ApplyCtx k ts')))
eval (Con c ts) (CaseCtx k bs) d r a
  = case find (\ (c', xs, _) -> c == c' && length xs == length ts) bs of
        Nothing -> error
                     ("No matching pattern in case for term:\n\n" ++
                        show (Case (Con c ts) bs))
        Just (_, _, t) -> eval (foldr subst t ts) k d (r + length ts) a
eval (Fun f) k d r a
  = case lookup f d of
        Nothing -> error ("Undefined function: " ++ f)
        Just (xs, t) -> eval (foldr (\ x t' -> Lambda x (abstract t' x)) t xs) k d
                          (r + 1)
                          a
eval (Apply t ts) k d r a = eval t (ApplyCtx k ts) d r a
eval (Case t bs) k d r a = eval t (CaseCtx k bs) d r a
eval (Let _ t u) k d r a = eval (subst t u) k d (r + 1) a
eval (Letrec f xs t u) k d r a
  = let f' = rename (fst (unzip d)) f
        t' = concreteFun f' (foldr concrete t xs)
        u' = concreteFun f' u
      in eval u' k ((f', (xs, t')) : d) (r + 1) a
-- to remove incomplete patterns warning
eval (Bound _) EmptyCtx _ _ _ = 
  error "unexpected call: eval (Bound _) EmptyCtx _ _ _"
eval (Bound _) (ApplyCtx _ (_:_)) _ _ _ = 
  error "unexpected call: eval (Bound _) (ApplyCtx _ (_:_)) _ _ _"
eval (Bound _) (CaseCtx _ _) _ _ _ = 
  error "unexpected call: eval (Bound _) (CaseCtx _ _) _ _ _"

-- free variables in a term
free :: Term -> [String]
free t = free' t []

-- Note: Free may be inserted with function abstract
free' :: Term -> [VarName] -> [VarName]
free' (Free x) xs = if x `elem` xs then xs else x : xs
free' (Bound _) xs = xs
free' (Lambda _ t) xs = free' t xs
free' (Con _ ts) xs = foldr free' xs ts
free' (Fun _) xs = xs
free' (Apply t ts) xs = foldr free' (free' t xs) ts
free' (Case t bs) xs = foldr (\ (_, _, t') xs' -> free' t' xs') (free' t xs) bs
free' (Let _ t u) xs = free' t (free' u xs)
free' (Letrec _ _ t u) xs = free' t (free' u xs)

-- functions in a program
funs :: Term -> [FuncName]
funs = funs' []

funs' :: [FuncName] -> Term -> [FuncName]
funs' fs (Free _) = fs
funs' fs (Bound _) = fs
funs' fs (Lambda _ t) = funs' fs t
funs' fs (Con _ ts) = foldl funs' fs ts
funs' fs (Apply t ts) = foldl funs' (funs' fs t) ts
funs' fs (Fun f) = if f `elem` fs then fs else (f : fs)
funs' fs (Case t bs) = foldl (\ _ (_, _, t') -> funs' fs t') (funs' fs t) bs
funs' fs (Let _ t u) = funs' (funs' fs t) u
funs' fs (Letrec _ _ t u) = funs' (funs' fs t) u

-- shift global de Bruijn indices by i, where current depth is d
shift ::Int -> Term -> Term
shift = shift' 0

shift' :: Int -> Int -> Term -> Term
shift' _ 0 u = u
shift' _ _ (Free x) = Free x
shift' d i (Bound i') = if i' >= d then Bound (i' + i) else Bound i'
shift' d i (Lambda x t) = Lambda x (shift' (d + 1) i t)
shift' d i (Con c ts) = Con c (map (shift' d i) ts)
shift' _ _ (Fun f) = Fun f
shift' d i (Apply t ts) = Apply (shift' d i t) (map (shift' d i) ts)
shift' d i (Case t bs)
  = Case (shift' d i t)
      (map (\ (c, xs, t') -> (c, xs, shift' (d + length xs) i t')) bs)
shift' d i (Let x t u) = Let x (shift' d i t) (shift' (d + 1) i u)
shift' d i (Letrec f xs t u)
  = Letrec f xs (shift' (d + 1 + length xs) i t) (shift' (d + 1) i u)

-- substitute term t for variable with de Bruijn index i
-- Q: cannot understand what is going on here
subst :: Term -> Term -> Term
subst = subst' 0

subst' :: Int -> Term -> Term -> Term
subst' _ _ (Free x) = Free x
subst' i t (Bound i')
  | i' < i = Bound i'
  | i' == i = shift i t
  | otherwise = Bound (i' - 1)
subst' i t (Lambda x t') = Lambda x (subst' (i + 1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' _ _ (Fun f) = Fun f
subst' i t (Apply t' ts) = Apply (subst' i t t') (map (subst' i t) ts)
subst' i t (Case t' bs)
  = Case (subst' i t t')
      (map (\ (c, xs, u) -> (c, xs, subst' (i + length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i + 1) t u)
subst' i t (Letrec f xs t' u)
  = Letrec f xs (subst' (i + 1 + length xs) t t') (subst' (i + 1) t u)

-- instantiate a term t using substitution s
instantiate :: [(String, Term)] -> Term -> Term
instantiate = instantiate' 0

instantiate' :: Int -> [(String, Term)] -> Term -> Term
instantiate' d s (Free x)
  = case lookup x s of
        Just t -> shift d t
        Nothing -> Free x
instantiate' _ _ (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d + 1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' _ _ (Fun f) = Fun f
instantiate' d s (Apply t ts)
  = Apply (instantiate' d s t) (map (instantiate' d s) ts)
instantiate' d s (Case t bs)
  = Case (instantiate' d s t)
      (map (\ (c, xs, t') -> (c, xs, instantiate' (d + length xs) s t')) bs)
instantiate' d s (Let x t u)
  = Let x (instantiate' d s t) (instantiate' (d + 1) s u)
instantiate' d s (Letrec f xs t u)
  = Letrec f xs (instantiate' (d + 1 + length xs) s t)
      (instantiate' (d + 1) s u)

-- replace variable x with de Bruijn index
-- Note: making lambda abstraction
abstract :: Term -> VarName -> Term
abstract = abstract' 0

abstract' :: DeBruijnIndex -> Term -> VarName -> Term
abstract' i (Free x') x = if x == x' then Bound i else Free x'
abstract' i (Bound i') _ = if i' >= i then Bound (i' + 1) else Bound i'
-- Q: Is there mix of de Bruijn notation and LC?
abstract' i (Lambda x' t) x = Lambda x' (abstract' (i + 1) t x)
abstract' i (Con c ts) x = Con c (map (\ t -> abstract' i t x) ts)
abstract' _ (Fun f) _ = Fun f
abstract' i (Apply t ts) x
  = Apply (abstract' i t x) (map (\ t' -> abstract' i t' x) ts)
abstract' i (Case t bs) x
  = Case (abstract' i t x)
      (map (\ (c, xs, t') -> (c, xs, abstract' (i + length xs) t' x)) bs)
abstract' i (Let x' t u) x = Let x' (abstract' i t x) (abstract' (i + 1) u x)
abstract' i (Letrec f xs t u) x
  = Letrec f xs (abstract' (i + 1 + length xs) t x) (abstract' (i + 1) u x)

-- replace de Bruijn index 0 with variable x
concrete :: String -> Term -> Term
concrete = concrete' 0

concrete' :: Int -> String -> Term -> Term
concrete' _ _ (Free x') = Free x'
concrete' i x (Bound i')
  | i' < i = Bound i'
  | i' == i = Free x
  | otherwise = Bound (i' - 1)
concrete' i x (Lambda x' t) = Lambda x' (concrete' (i + 1) x t)
concrete' i x (Con c ts) = Con c (map (concrete' i x) ts)
concrete' _ _ (Fun f) = Fun f
concrete' i x (Apply t ts) = Apply (concrete' i x t) (map (concrete' i x) ts)
concrete' i x (Case t bs)
  = Case (concrete' i x t)
      (map (\ (c, xs, t') -> (c, xs, concrete' (i + length xs) x t')) bs)
concrete' i x (Let x' t u) = Let x' (concrete' i x t) (concrete' (i + 1) x u)
concrete' i x (Letrec f xs t u)
  = Letrec f xs (concrete' (i + 1 + length xs) x t) (concrete' (i + 1) x u)

-- replace function f with de Bruijn index
abstractFun :: Term -> String -> Term
abstractFun = abstractFun' 0

abstractFun' :: Int -> Term -> String -> Term
abstractFun' _ (Free x) _ = Free x
abstractFun' i (Bound i') _ = if i' >= i then Bound (i' + 1) else Bound i'
abstractFun' i (Lambda x t) f = Lambda x (abstractFun' (i + 1) t f)
abstractFun' i (Con c ts) f = Con c (map (\ t -> abstractFun' i t f) ts)
abstractFun' i (Fun f') f = if f == f' then Bound i else Fun f'
abstractFun' i (Apply t ts) f
  = Apply (abstractFun' i t f) (map (\ t' -> abstractFun' i t' f) ts)
abstractFun' i (Case t bs) f
  = Case (abstractFun' i t f)
      (map (\ (c, xs, t') -> (c, xs, abstractFun' (i + length xs) t' f)) bs)
abstractFun' i (Let x' t u) f
  = Let x' (abstractFun' i t f) (abstractFun' (i + 1) u f)
abstractFun' i (Letrec f' xs t u) f
  = Letrec f' xs (abstractFun' (i + 1 + length xs) t f)
      (abstractFun' (i + 1) u f)

-- replace de Bruijn index 0 with function f
concreteFun :: String -> Term -> Term
concreteFun = concreteFun' 0

concreteFun' :: Int -> String -> Term -> Term
concreteFun' _ _ (Free x) = Free x
concreteFun' i f (Bound i')
  | i' < i = Bound i'
  | i' == i = Fun f
  | otherwise = Bound (i' - 1)
concreteFun' i f (Lambda x t) = Lambda x (concreteFun' (i + 1) f t)
concreteFun' i f (Con c ts) = Con c (map (concreteFun' i f) ts)
concreteFun' _ _ (Fun f') = Fun f'
concreteFun' i f (Apply t ts)
  = Apply (concreteFun' i f t) (map (concreteFun' i f) ts)
concreteFun' i f (Case t bs)
  = Case (concreteFun' i f t)
      (map (\ (c, xs, t') -> (c, xs, concreteFun' (i + length xs) f t')) bs)
concreteFun' i f (Let x t u)
  = Let x (concreteFun' i f t) (concreteFun' (i + 1) f u)
concreteFun' i f (Letrec f' xs t u)
  = Letrec f' xs (concreteFun' (i + 1 + length xs) f t)
      (concreteFun' (i + 1) f u)

rename :: Foldable t => t [Char] -> [Char] -> [Char]
rename fv x = if x `elem` fv then rename fv (x ++ "'") else x

-- rename a term t using renaming r
renameVar :: Eq a => [(a, a)] -> a -> a
renameVar r x = fromMaybe x (lookup x r)

renameTerm :: [(String, String)] -> Term -> Term
renameTerm r (Free x) = Free (renameVar r x)
renameTerm _ (Bound i) = Bound i
renameTerm r (Lambda x t) = Lambda x (renameTerm r t)
renameTerm r (Con c ts) = Con c (map (renameTerm r) ts)
renameTerm _ (Fun f) = Fun f
renameTerm r (Apply t ts) = Apply (renameTerm r t) (map (renameTerm r) ts)
renameTerm r (Case t bs)
  = Case (renameTerm r t) (map (\ (c, xs, t') -> (c, xs, renameTerm r t')) bs)
renameTerm r (Let x t u) = Let x (renameTerm r t) (renameTerm r u)
renameTerm r (Letrec f xs t u) = Letrec f xs (renameTerm r t) (renameTerm r u)

-- redex
redex :: Term -> Term
redex (Apply t _) = redex t
redex (Case t _) = redex t
redex t = t

-- function name and args
fun :: Term -> Term
fun (Apply t _) = t
-- to remove incomplete patterns warning
fun (Free _) =
  error "unexpected call: fun (Free _)"
fun (Bound _) =
  error "unexpected call: fun (Bound _)"
fun (Lambda _ _) =
  error "unexpected call: fun (Lambda _ _)"
fun (Con _ _) =
  error "unexpected call: fun (Con _ _)"
fun (Fun _) =
  error "unexpected call: fun (Fun _)"
fun (Case _ _) =
  error "unexpected call: fun (Case _ _)"
fun (Let _ _ _) =
  error "unexpected call: fun (Let _ _ _)"
fun (Letrec _ _ _ _) =
  error "unexpected call: fun (Letrec _ _ _ _)"

args :: Term -> [Term]
args (Apply _ ts) = ts
--to remove incomplete patterns warning
args (Free _) =
  error "unexpected call: args (Free _)"
args (Bound _) =
  error "unexpected call: args (Bound _)"
args (Lambda _ _) =
  error "unexpected call: args (Lambda _ _)"
args (Con _ _) =
  error "unexpected call: args (Con _ _)"
args (Fun _) =
  error "unexpected call: args (Fun _)"
args (Case _ _) =
  error "unexpected call: args (Case _ _)"
args (Let _ _ _) =
  error "unexpected call: args (Let _ _ _)"
args (Letrec _ _ _ _) =
  error "unexpected call: args (Letrec _ _ _ _)"

-- unfold function
unfold
   :: Term
   -> [[Char]]
   -> [(String, ([String], Term))]
   -> (Term, [(String, ([String], Term))])
unfold (Apply t ts) fs d = let (t', d') = unfold t fs d in (Apply t' ts, d')
unfold (Case t bs) fs d = let (t', d') = unfold t fs d in (Case t' bs, d')
unfold (Fun f) _ d
  = case lookup f d of
        Just (xs, t) -> (foldr (\ x t' -> Lambda x (abstract t' x)) t xs, d)
        Nothing -> error "unexpected Nothing in unfold"
unfold (Let _ t u) fs d = unfold (subst t u) fs d
unfold (Letrec f xs t u) fs d
  = let f' = rename fs f
        t' = concreteFun f' (foldr concrete t xs)
        u' = concreteFun f' u
      in unfold u' (f' : fs) ((f', (xs, t')) : d)
unfold t _ d = (t, d)

-- pretty printing

stripLambda :: Term -> ([[Char]], Term)
stripLambda (Lambda x t)
  = let x' = rename (free t) x
        (xs, u) = stripLambda $ concrete x' t
      in (x' : xs, u)
stripLambda t = ([], t)

blank :: Doc
blank = P.space

prettyTerm :: Term -> P.Doc
prettyTerm (Free x) = text x
prettyTerm (Bound i) = text "#" <> int i
prettyTerm t@(Lambda _ _)
  = let (xs, t') = stripLambda t in
      text "\\" <> hsep (map text xs) <> text "." <> prettyTerm t'
prettyTerm t@(Con c ts)
  | isNat t = int $ con2nat t
  | isList t =
    text "[" <> hcat (punctuate comma $ map prettyTerm $ con2list t) <> text "]"
  | null ts = text c
  | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)
prettyTerm (Fun f) = text f
prettyTerm (Apply t ts) = prettyAtom t <+> hsep (map prettyAtom ts)
prettyTerm (Case trm (b : bs))
  = hang (text "case" <+> prettyAtom trm <+> text "of") 1
      (blank <+> prettyBranch b $$
         vcat (map ((text "|" <+>) . prettyBranch) bs))
  where prettyBranch (c, [], t) = text c <+> text "->" <+> prettyTerm t
        prettyBranch (c, xs, t)
          = let fv
                  = foldr (\ x fvs -> let x' = rename fvs x in x' : fvs) (free t)
                      xs
                xs' = take (length xs) fv
                t' = foldr concrete t xs'
              in
              text c <> parens (hcat $ punctuate comma $ map text xs') <+>
                text "->"
                <+> prettyTerm t'
                $$ empty
prettyTerm (Let x t u)
  = let x' = rename (free u) x in
      (text "let" <+> text x' <+> text "=" <+> prettyTerm t) $$
        (text "in" <+> prettyTerm (concrete x' u))
prettyTerm (Letrec f xs t u)
  = let fv = foldr (\ x fvs -> let x' = rename fvs x in x' : fvs) (free t) xs
        f' = rename fv f
        xs' = take (length xs) fv
        t' = foldr concrete t (f' : xs')
        u' = concrete f' u
      in
      (text "letrec" <+> text f' <+> hsep (map text xs') <+> text "=" <+>
         prettyTerm t')
        $$ (text "in" <+> prettyTerm u')
--to remove incomplete patterns warning
prettyTerm (Case _ []) = 
  error "unexpected call: prettyTerm (Case _ [])"

prettyAtom :: Term -> P.Doc
prettyAtom (Free x) = text x
prettyAtom t@(Con c ts)
  | isNat t = int $ con2nat t
  | isList t =
    text "[" <> hcat (punctuate comma $ map prettyTerm $ con2list t) <> text "]"
  | null ts = text c
  | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)
prettyAtom (Fun f) = text f
prettyAtom t = parens $ prettyTerm t

prettyProg :: (Term, [([Char], ([String], Term))]) -> P.Doc
prettyProg (t, d) = prettyProg' (("main", ([], t)) : d)

prettyProg' :: [(String, ([String], Term))] -> P.Doc
prettyProg' [] = empty
prettyProg' [(f, (xs, t))]
  = text f <+> hsep (map text xs) <+> equals <+> prettyTerm t
prettyProg' ((f, (xs, t)) : fs)
  = text f <+> hsep (map text xs) <+> equals <+> prettyTerm t <> semi $$
      prettyProg' fs

isList :: Term -> Bool
isList (Con "Nil" []) = True
isList (Con "Cons" [_, t]) = isList t
isList _ = False

list2con :: [Term] -> Term
list2con [] = Con "Nil" []
list2con (h : t) = Con "Cons" [h, list2con t]

con2list :: Term -> [Term]
con2list (Con "Nil" []) = []
con2list (Con "Cons" [h, t]) = h : con2list t
--to remove incomplete patterns warning
con2list (Free _) =
  error "unexpected call: con2list (Free _)"
con2list (Bound _) =
  error "unexpected call: con2list (Bound _)"
con2list (Lambda _ _) =
  error "unexpected call: con2list (Lambda _ _)"
con2list (Con [] _) =
  error "unexpected call: con2list (Con [] _)"
con2list (Con ['C', 'o'] _) =
  error "unexpected call: con2list (Con ['C', 'o'] _)"
con2list (Con ('C':_:_) _) =
  error "unexpected call: con2list (Con ('C':_:_) _)"
con2list (Con ['C'] _) =
  error "unexpected call: con2list (Con ['C'] _)"
con2list (Con (_:_) _) =
  error "unexpected call: con2list (Con (_:_) _)"
con2list (Fun _) =
  error "unexpected call: con2list (Fun _)"
con2list (Apply _ _) =
  error "unexpected call: con2list (Apply _ _)"
con2list (Case _ _) =
  error "unexpected call: con2list (Case _ _)"
con2list (Let _ _ _) =
  error "unexpected call: con2list (Let _ _ _)"
con2list (Letrec _ _ _ _) =
  error "unexpected call: con2list (Letrec _ _ _ _)"

isNat :: Term -> Bool
isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con :: (Eq t, Num t) => t -> Term
nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con $ n - 1]

con2nat :: Num p => Term -> p
con2nat (Con "Zero" []) = 0
con2nat (Con "Succ" [n]) = 1 + con2nat n
--to remove incomplete patterns warning
con2nat (Free _) =
  error "unexpected call: con2nat (Free _)"
con2nat (Bound _) =
  error "unexpected call: con2nat (Bound _)"
con2nat (Lambda _ _) =
  error "unexpected call: con2nat (Lambda _ _)"
con2nat (Con [] _) =
  error "unexpected call: con2nat (Con [] _)"
con2nat (Con ['S', 'u'] _) =
  error "unexpected call: con2nat (Con ['S', 'u'] _)"
con2nat (Con ('S':_:_) _) =
  error "unexpected call: con2nat (Con ('S':_:_) _)"
con2nat (Con ['S'] _) =
  error "unexpected call: con2nat (Con ['S'] _)"
con2nat (Con (_:_) _) =
  error "unexpected call: con2nat (Con (_:_) _)"
con2nat (Fun _) = 
  error "unexpected call: con2nat (Fun _)"
con2nat (Apply _ _) =
  error "unexpected call: con2nat (Apply _ _)"
con2nat (Case _ _) =
  error "unexpected call: con2nat (Case _ _))"
con2nat (Let _ _ _) =
  error "unexpected call: con2nat (Let _ _ _)"
con2nat (Letrec _ _ _ _) =
  error "unexpected call: con2nat (Letrec _ _ _ _)"

-- lexing and parsing

potDef :: T.GenLanguageDef
   String u Data.Functor.Identity.Identity
potDef
  = emptyDef{commentStart = "/*", commentEnd = "*/", commentLine = "--",
             nestedComments = True, identStart = lower,
             identLetter = letter <|> oneOf "_'",
             reservedNames =
               ["import", "case", "of", "let", "in", "letrec", "ALL", "EX",
                "ANY"],
             reservedOpNames = ["~", "/\\", "\\/", "<=>", "=>"],
             caseSensitive = True}

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser potDef

symbol :: String -> ParsecT String u Identity String
symbol = T.symbol lexer

bracks :: ParsecT String u Identity a -> ParsecT String u Identity a
bracks = T.parens lexer

semic :: ParsecT String u Identity String
semic = T.semi lexer

comm :: ParsecT String u Identity String
comm = T.comma lexer

identifier :: ParsecT String u Identity String
identifier = T.identifier lexer

reserved :: String -> ParsecT String u Identity ()
reserved = T.reserved lexer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = T.reservedOp lexer

natural :: ParsecT String u Identity Integer
natural = T.natural lexer

makeFuns :: [(String, (a, Term))] -> [(String, (a, Term))]
makeFuns ds
  = let fs = fst (unzip ds) in
      map (\ (f, (xs, t)) -> (f, (xs, makeFuns' fs t))) ds

makeFuns' :: Foldable t => t String -> Term -> Term
makeFuns' fs (Free x) = if x `elem` fs then Fun x else Free x
makeFuns' _ (Bound i) = Bound i
makeFuns' fs (Lambda x t) = Lambda x (makeFuns' fs t)
makeFuns' fs (Con c ts) = Con c (map (makeFuns' fs) ts)
makeFuns' fs (Apply t ts) = Apply (makeFuns' fs t) (map (makeFuns' fs) ts)
makeFuns' fs (Case t bs)
  = Case (makeFuns' fs t) (map (\ (c, xs, t') -> (c, xs, makeFuns' fs t')) bs)
makeFuns' fs (Let x t u) = Let x (makeFuns' fs t) (makeFuns' fs u)
makeFuns' fs (Letrec f xs t u) = Letrec f xs (makeFuns' fs t) (makeFuns' fs u)
--to remove incomplete patterns warning
makeFuns' _ (Fun _) = error "unexpected call: _ (Fun _)"

con :: Text.Parsec.Prim.ParsecT
   String u Data.Functor.Identity.Identity [Char]
con
  = do c <- upper
       cs <- many letter
       spaces
       return (c : cs)

modul :: Text.Parsec.Prim.ParsecT
   String u Data.Functor.Identity.Identity
   ([[Char]], [(String, ([String], Term))])
modul
  = do fs <- many imp
       ds <- sepBy1 fundef semic
       return (fs, ds)

imp :: Text.Parsec.Prim.ParsecT
   String u Data.Functor.Identity.Identity [Char]
imp
  = do reserved "import"
       con

expr :: Text.Parsec.Prim.ParsecT
   String u Data.Functor.Identity.Identity Term
expr
  = do reserved "ALL"
       x <- identifier
       _ <- symbol ":"
       c <- con
       _ <- symbol "."
       e <- expr
       return (Apply (Free ("all" ++ c)) [Lambda x (abstract e x)])
      <|>
      do reserved "EX"
         x <- identifier
         _ <- symbol ":"
         c <- con
         _ <- symbol "."
         e <- expr
         return (Apply (Free ("ex" ++ c)) [Lambda x (abstract e x)])
      <|>
      do reserved "ANY"
         x <- identifier
         _ <- symbol ":"
         c <- con
         _ <- symbol "."
         e <- expr
         return
           (Apply (Free ("any" ++ c))
              [Apply (Free "construct") [Lambda x (abstract e x)]])
      <|> term

fundef :: Text.Parsec.Prim.ParsecT
      String u Data.Functor.Identity.Identity (String, ([String], Term))
fundef
  = do f <- identifier
       xs <- many identifier
       _ <- symbol "="
       e <- expr
       return (f, (xs, e))

term :: Text.Parsec.Prim.ParsecT
   String u Data.Functor.Identity.Identity Term
term
  = do t <- atom
       ts <- many atom
       return (makeApplication t ts)
      <|>
      do _ <- symbol "\\"
         xs <- many1 identifier
         _ <- symbol "->"
         t <- term
         return (foldr (\ x t' -> Lambda x (abstract t' x)) t xs)
      <|>
      do reserved "case"
         t <- term
         reserved "of"
         bs <- sepBy1 branch (symbol "|")
         return (Case t bs)
      <|>
      do reserved "let"
         x <- identifier
         _ <- symbol "="
         t <- term
         reserved "in"
         u <- term
         return (Let x t (abstract u x))
      <|>
      do reserved "letrec"
         f <- identifier
         xs <- many identifier
         _ <- symbol "="
         t <- term
         reserved "in"
         u <- term
         return (Letrec f xs (abstract (foldl abstract t xs) f) (abstract u f))

atom :: Text.Parsec.Prim.ParsecT
      String u Data.Functor.Identity.Identity Term
atom
  = do x <- identifier
       return (Free x)
      <|>
      do c <- con
         ts <- bracks (sepBy1 term comm) <|>
                 do spaces
                    return []
         return (Con c ts)
      <|>
      do n <- natural
         return (nat2con n)
      <|>
      do _ <- symbol "["
         ts <- sepBy term comm
         _ <- symbol "]"
         return (list2con ts)
      <|> bracks expr

branch :: Text.Parsec.Prim.ParsecT
      String u Data.Functor.Identity.Identity (String, [String], Term)
branch
  = do c <- con
       xs <- bracks (sepBy1 identifier comm) <|>
               do spaces
                  return []
       _ <- symbol "->"
       t <- term
       return (c, xs, foldl abstract t xs)

parseTerm :: String -> Either ParseError Term
parseTerm = parse term "Parse error"

parseModule
  :: String
     -> Either ParseError ([[Char]], [(String, ([String], Term))])
parseModule = parse modul "Parse error"
