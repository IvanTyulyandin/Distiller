module Trans where

import Data.List
import Data.Maybe
import Debug.Trace
import Exception
import Term

-- Note: cases of this function are annotated with input -> result.
--       Using syntax from article. N == this function
super
   :: Term      -- term t
   -> Context   -- Context
   -> [VarName]  -- free variables in t
   -- process tree (a part of it that is needed for folding etc)
   -> [(FuncName, ([VarName], Term))]
   -- user-defined definitions (name, vars, body)
   -> [(FuncName, ([VarName], Term))]
   -> Exception (String, Term) Term
-- Note: seems like optimisation, but not sure
--       if this situation should be possible
super t (ApplyCtx k []) fv m d = super t k fv m d
super (Free x) (CaseCtx k bs) fv m d =
  do bs' <- mapM
              (\ (conName, conVars, t) ->
                let t'    = place t k
                    fv'   = foldr (\ x' fvs -> let x'' = rename fvs x' in x'' : fvs) fv conVars
                    vars' = take (length conVars) fv'
                    u     = subst (Con conName (map Free vars'))
                              (abstract (foldr concrete t' vars') x)
                in do u' <- super u EmptyCtx fv' m d
                      return (conName, conVars, foldl abstract u' vars'))
              bs
     return (Case (Free x) bs')
-- free variable then supercompile context
super (Free x)     k        fv m d = superCtx (Free x) k fv m d
super (Lambda x t) EmptyCtx fv m d =
  let x' = rename fv x
  in do t' <- super (concrete x' t) EmptyCtx (x' : fv) m d
        return (Lambda x (abstract t' x'))
-- N (con< (λv.e) e1..en >) = N (con< e{v := e1} e2..en >)
super (Lambda _ t) (ApplyCtx k (t' : ts)) fv m d
  = super (subst t' t) (ApplyCtx k ts) fv m d
-- N (con< case (λv.e) b1..bn >) = error
super (Lambda _ _) (CaseCtx _ _) _ _ _
  = error "Unapplied function in case selector"
-- N (con< (c t1..tn) >) = c (N t1, .., N tn)
super (Con c ts) EmptyCtx fv m d
  = do ts' <- mapM (\ t -> super t EmptyCtx fv m d) ts
       return (Con c ts')
-- N (con< (c t1..tn) e1..en >) = error
super (Con c ts) (ApplyCtx k ts') _ _ _
  = error ("Constructor application is not saturated: " ++
           show (place (Con c ts) (ApplyCtx k ts')))
-- N (con< case (c t1..tn) b1..bn >) = N (e{v1 := t1, .., vn := tn})
-- where bi == (c v1..vn) -> e
  -- Note: unfold case with known constructor c to expr e in branch bi
  --       with substitution t1..tn instead of x1..xn in e
super (Con c ts) (CaseCtx k bs) fv m d
  = case find (\ (c', xs, _) -> c == c' && length xs == length ts) bs of
      Nothing -> error ("No matching pattern in case for term:\n\n" ++
                        show (Case (Con c ts) bs))
      -- Q: is k equal to EmptyCtx?
      Just (_, _, t) -> super (foldr subst t ts) k fv m d
-- non used-refined function call then supercompile context
super (Fun f) k fv m d | f `notElem` fst (unzip d) = superCtx (Fun f) k fv m d
-- user-defined function call
super (Fun f) k fv m d =
  let t = place (Fun f) k -- place term (Fun f) in context
     -- try to find an ancestor (in m --- a form of process tree history)
     -- term t' s.t. t is an instance of term t'
  in case find (\ (_, (_, t')) -> isJust (inst t' t)) m of
       -- if found
       Just (f',(xs,t')) -> 
         let Just s = inst t' t --- s is a substitution s.t. t s = t'
             -- create let-expression and supercompile the result of let
         in  super (makeLet s (Apply (Fun f') (map Free xs))) EmptyCtx fv m d
       -- else try to find term t' s.t. t' is embedded in t
       Nothing -> case find (\ (_, (_,t')) -> not (null (embed t' t))) m of
         -- if found t' s.t. t' is embedded in t then throw exception (i.e. abstract_up)
         Just (f',_) -> throw (f', t)
         -- else driving
         Nothing -> let fs       = fst . unzip $ m ++ d
                        renf     = rename fs "f"
                        xs       = free t
                        (t', d') = unfold t (renf:fs) d -- unfold f
                        -- define new handler that "catches" an exception
                        -- if function names are equal
                        handler (f', t1) = if renf == f'
                                                -- chatch an exception and generalize
                                                -- i.e. abstract(_up) and rebuild the tree
                                           then let (t2, s1, _) = generalise t t1
                                                in  super (makeLet s1 t2) EmptyCtx fv m d
                                                -- throw exception futher
                                           else throw (f', t1)
                                   -- unfolding-driving step with extended m
                      in do t'' <- handle (super t' EmptyCtx fv ((renf,(xs,t)):m) d') handler
                            return (if renf `elem` funs t''
                                    -- if function was used in the result of supercompilation
                                    -- (i.e. there is a a-la fold to the function renf)
                                    -- then generate a local function definition using letrec
                                    then Letrec renf xs
                                          (foldl abstract (abstractFun t'' renf) xs)
                                          (Apply (Bound 0) (map Free xs))
                                    -- else do nothing (i.e. the current node is transit)
                                    -- i.e. it is not added == automatically removed from tree
                                    else t'')
-- k [ t @ ts ] => ApplyCtx [ t ] k ts
super (Apply t ts) k fv m d = super t (ApplyCtx k ts) fv m d
-- k [ Case t of bs ] => CaseCtx [ t ] k bs
super (Case t bs) k fv m d = super t (CaseCtx k bs) fv m d
-- let x = t in u =>(split)=> u'[x' <- t']
super (Let x t u) k fv m d =
  let x' = rename fv x                              -- fresh x'
  in do t' <- super t EmptyCtx fv m d               -- supercompile t
        u' <- super (concrete x' u) k (x' : fv) m d -- supercompile u
        return (subst t' (abstract u' x'))          -- return u'[x' <- t']
-- letrec f (x1 ... xs) = t in u
super (Letrec f xs t u) k fv m d =
  let f' = rename (fst (unzip (m ++ d))) f      -- generate fresh function name
      t' = concreteFun f' (foldr concrete t xs) -- replace indexes with fv-names from xs
      u' = concreteFun f' u                     -- replace 0-index with fun name f'
  in super u' k fv m ((f', (xs, t')) : d)       -- supercompile u' (i.e. body)

-- to remove incomplete patterns warnings
super (Bound _) _ _ _ _ =
  error "unexpected call: (Bound _) _ _ _ _"

-- supercompilation of context
superCtx
   :: Term
   -> Context
   -> [String]
   -> [(String, ([String], Term))]
   -> [(String, ([String], Term))]
   -> Exception (String, Term) Term
superCtx t EmptyCtx _ _ _ = return t
superCtx t (ApplyCtx k ts) fv m d
  = do ts' <- mapM (\ trm -> super trm EmptyCtx fv m d) ts
       superCtx (Apply t ts') k fv m d
superCtx t (CaseCtx k bs) fv m d
  = do bs' <- mapM
                (\ (c, xs, trm) ->
                   let fv'
                         = foldr (\ x fvs -> let x' = rename fvs x in x' : fvs) fv
                             xs
                       xs' = take (length xs) fv'
                     in
                     do t' <- super (foldr concrete trm xs') k fv' m d
                        return (c, xs, foldl abstract t' xs'))
                bs
       return (Case t bs')

dist :: (Term, [(String, ([String], Term))]) -> Term
dist (t, d) = returnval (distill t EmptyCtx (free t) [] d)

distill
   :: Term
   -> Context
   -> [String]
   -> [(String, ([String], Term))]
   -> [(String, ([String], Term))]
   -> Exception (String, Term) Term
distill t k fv = trace (show fv ++ show (place t k)) distill' t k fv

distill'
  :: Term
     -> Context
     -> [String]
     -> [(String, ([String], Term))]
     -> [(String, ([String], Term))]
     -> Exception (String, Term) Term
distill' t (ApplyCtx k []) fv m d = distill t k fv m d
distill' (Free x) (CaseCtx k bs) fv m d
  = do bs' <- mapM
                (\ (c, xs, t) ->
                   let t' = place t k
                       fv'
                         = foldr (\ x' fvs -> let x'' = rename fvs x' in x'' : fvs) fv
                             xs
                       xs' = take (length xs) fv'
                       u = subst (Con c (map Free xs'))
                             (abstract (foldr concrete t' xs') x)
                     in
                     do u' <- distill u EmptyCtx fv' m d
                        return (c, xs, foldl abstract u' xs'))
                bs
       return (Case (Free x) bs')
distill' (Free x) k fv m d = distillCtx (Free x) k fv m d
distill' (Lambda x t) EmptyCtx fv m d
  = let x' = rename fv x in
      do t' <- distill (concrete x' t) EmptyCtx (x' : fv) m d
         return (Lambda x (abstract t' x'))
distill' (Lambda _ t) (ApplyCtx k (t' : ts)) fv m d
  = distill (subst t' t) (ApplyCtx k ts) fv m d
distill' (Lambda _ _) (CaseCtx _ _) _ _ _
  = error "Unapplied function in case selector"
distill' (Con c ts) EmptyCtx fv m d
  = do ts' <- mapM (\ t -> distill t EmptyCtx fv m d) ts
       return (Con c ts')
distill' (Con c ts) (ApplyCtx k ts') _ _ _
  = error
      ("Constructor application is not saturated: " ++
         show (place (Con c ts) (ApplyCtx k ts')))
distill' (Con c ts) (CaseCtx k bs) fv m d
  = case find (\ (c', xs, _) -> c == c' && length xs == length ts) bs of
        Nothing -> error
                     ("No matching pattern in case for term:\n\n" ++
                        show (Case (Con c ts) bs))
        Just (_, _, t) -> distill (foldr subst t ts) k fv m d
distill' (Fun f) k fv m d
  | f `notElem` fst (unzip d) = distillCtx (Fun f) k fv m d
distill' (Fun f) k fv m d
  = let t = returnval (super (Fun f) k fv [] d) in
      case find (\ (_, (_, t')) -> isJust (inst t' t)) m of
          Just (f', (xs, t')) -> let Just s = inst t' t in
                                  return
                                    (instantiate s
                                       (Apply (Fun f') (map Free xs)))
          Nothing -> case find (\(_, (_, t')) -> not (null (embed t' t))) m of
            Just (f',_) -> throw (f',t)
            Nothing -> let fs = fst(unzip (m++d))
                           renf = rename fs "f"
                           xs = free t
                           (t',d') = unfold t (renf:fs) d
                           handler (f',t1) = 
                             if renf == f'
                             then let (t2, s1, _) = generalise t t1
                                  in  distill (makeLet s1 t2) EmptyCtx fv m d
                             else throw (f',t1)
                        in do t'' <- handle (distill t' EmptyCtx fv ((renf,(xs,t)):m) d') handler
                              return (if renf `elem` funs t'' 
                                      then Letrec renf xs
                                            (foldl abstract (abstractFun t'' renf) xs)
                                            (Apply (Bound 0) (map Free xs))
                                      else t'')
distill' (Apply t ts) k fv m d = distill t (ApplyCtx k ts) fv m d
distill' (Case t bs) k fv m d = distill t (CaseCtx k bs) fv m d
distill' (Let x t u) k fv m d
  = let x' = rename fv x in
      do t' <- distill t EmptyCtx fv m d
         u' <- distill (concrete x' u) k (x' : fv) m d
         return (subst t' (abstract u' x'))
distill' (Letrec f xs t u) k fv m d
  = let f' = rename (fst (unzip (m ++ d))) f
        t' = concreteFun f' (foldr concrete t xs)
        u' = concreteFun f' u
      in distill u' k fv m ((f', (xs, t')) : d)
-- to remove incomplete patterns warning
distill' (Bound _) _ _ _ _ =
  error "unexpected call: distill' (Bound _) _ _ _ _"

distillCtx
    :: Term
    -> Context
    -> [String]
    -> [(String, ([String], Term))]
    -> [(String, ([String], Term))]
    -> Exception (String, Term) Term
distillCtx t EmptyCtx _ _ _ = return t
distillCtx t (ApplyCtx k ts) fv m d
  = do ts' <- mapM (\ trm -> distill trm EmptyCtx fv m d) ts
       distillCtx (Apply t ts') k fv m d
distillCtx t (CaseCtx k bs) fv m d
  = do bs' <- mapM
                (\ (c, xs, trm) ->
                   let fv'
                         = foldr (\ x fvs -> let x' = rename fvs x in x' : fvs) fv
                             xs
                       xs' = take (length xs) fv'
                     in
                     do trm' <- distill (foldr concrete trm xs') k fv' m d
                        return (c, xs, foldl abstract trm' xs'))
                bs
       return (Case t bs')
