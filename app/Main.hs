module Main (main) where

import System.Directory
import System.IO
import Term
import Trans

data Command = Load String
             | Prog
             | Term
             | Eval
             | SuperCompile
             | Distill
             | Quit
             | Help
             | Reload
             | Unknown

command :: String -> Command
command str
  = let res = words str in
      case res of
          [":load", f] -> Load f
          [":l", f]    -> Load f
          [":prog"]    -> Prog
          [":p"]       -> Prog
          [":term"]    -> Term
          [":t"]       -> Term
          [":eval"]    -> Eval
          [":e"]       -> Eval
          [":sc"]      -> SuperCompile
          [":distill"] -> Distill
          [":d"]       -> Distill
          [":quit"]    -> Quit
          [":q"]       -> Quit
          [":help"]    -> Help
          [":h"]       -> Help
          [":reload"]  -> Reload
          [":r"]       -> Reload
          _            -> Unknown

helpMessage :: String
helpMessage
  = "\n:load filename\t\tTo load the given filename\n" ++
      ":reload\t\t\tTo reload the current program\n" ++
      ":prog\t\t\tTo print the current program\n" ++
      ":term\t\t\tTo print the current term\n" ++
      ":eval\t\t\tTo evaluate the current term\n" ++
      ":sc\t\t\tTo supercompile the current term\n" ++
      ":distill\t\t\tTo distill the current program\n" ++
      ":quit\t\t\tTo quit\n" ++
      ":help\t\t\tTo print this message\n" ++
      "You can use only first letters"

-- Entry point for main program
main :: IO ()
main = toplevel Nothing Nothing

toplevel :: Maybe Prog -> Maybe String -> IO ()
toplevel p fileName =
  let -- g :: Imports -> _ -> _ -> Previously loaded file
      g [] _ ds prevLoaded =
        let ds' = makeFuns ds in
          case lookup "main" ds' of
            Nothing -> do putStrLn "No main function"
                          toplevel Nothing fileName
            Just (_, t) -> toplevel (Just (t, ds')) (Just prevLoaded)
      g (y : ys) zs ds prevLoaded =
        if y `elem` zs
        then g ys zs ds prevLoaded
        else do r <- loadFile y
                case r of
                  Nothing -> toplevel Nothing (Just prevLoaded)
                  Just (fs, ds2) ->
                    g (ys ++ fs) (y : zs) (ds ++ ds2) prevLoaded
      printFail = do
        putStrLn "No program loaded"
        toplevel p fileName
  in
  do  putStr "POT> "
      hFlush stdout
      x <- getLine
      case command x of
        Load f -> g [f] [] [] f

        Reload ->
          case fileName of
            Nothing -> printFail
            Just f  -> g [f] [] [] f

        Prog ->
          case p of
            Nothing -> printFail
            Just (t, ds) -> do
              putStrLn (showProg (t, ds))
              toplevel p fileName

        Term ->
          case p of
            Nothing -> printFail
            Just (t, _) -> do
              print t
              toplevel p fileName

        Eval ->
          case p of
            Nothing -> printFail
            Just (t, ds) -> f (free t) t
              where f [] trm = do
                      let (v, r, a) = eval trm EmptyCtx ds 0 0
                      print v
                      putStrLn ("Reductions: " ++ show r)
                      putStrLn ("Allocations: " ++ show (a :: Int))
                      toplevel p fileName

                    f (y : ys) trm = do
                      putStr (y ++ " = ")
                      hFlush stdout
                      l <- getLine
                      case parseTerm l of
                          Left s -> do
                            putStrLn ("Could not parse term: " ++ show s)
                            f (y : ys) trm
                          Right u -> f ys (subst u (abstract trm y))
        SuperCompile ->
          case p of
            Nothing -> printFail
            Just t  -> do
                let u = runSC t
                print u
                toplevel (Just (u, [])) fileName
        Distill ->
          case p of
            Nothing -> printFail
            Just t  -> do
              let u = dist t
              print u
              toplevel (Just (u, [])) fileName
        Quit -> return ()
        Help -> do putStrLn helpMessage
                   toplevel p fileName
        Unknown -> do putStrLn
                        "Err: Could not parse command, type ':help' for a list of commands"
                      toplevel p fileName

loadFile :: String -> IO (Maybe ([String], [(String, ([String], Term))]))
loadFile f
  = do x <- doesFileExist (f ++ ".pot")
       if x then
         do putStrLn ("Loading file: " ++ f ++ ".pot")
            c <- readFile (f ++ ".pot")
            case parseModule c of
                Left s -> do putStrLn
                               ("Could not parse program in file " ++
                                  f ++ ".pot: " ++ show s)
                             return Nothing
                Right t -> return (Just t)
         else
         do putStrLn ("No such file: " ++ f ++ ".pot")
            return Nothing
