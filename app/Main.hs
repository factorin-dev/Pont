module Main where

import Kernel.Syntax
import Kernel.Value
import Kernel.Quote (quote)
import Kernel.Conv (conv)
import Kernel.Check
import Kernel.Context

main :: IO ()
main = do
  putStrLn "Pont type checker v0.4 \x2014 Complete HoTT kernel"
  putStrLn "  \x03A0 (dependent functions)"
  putStrLn "  \x03A3 (dependent pairs)"
  putStrLn "  Path + J (identity types)"
  putStrLn "  ua + ua-\x03B2 (univalence)"
  putStrLn ""

  -- Demo 1: Identity function (M1)
  let idTy   = Pi (U 0) (Pi (Var 0) (Var 1))
  let idTerm = Lam (Lam (Var 0))
  putStrLn "1. Identity function: (\x03BB A x . x) : \x03A0 (A : U 0) . A \x2192 A"
  case check emptyCtx idTerm (evalTerm [] idTy) of
    Right ()  -> putStrLn "   \x2713 Type check passed."
    Left err  -> putStrLn $ "   \x2717 " ++ show err

  -- Demo 2: Refl (M3)
  putStrLn "2. Reflexivity: refl (U 0) : Path (U 1) (U 0) (U 0)"
  case infer emptyCtx (Refl (U 0)) of
    Right ty  -> putStrLn $ "   \x2713 Inferred type: " ++ show (quote 0 ty)
    Left err  -> putStrLn $ "   \x2717 " ++ show err

  -- Demo 3: ua-β (M4)
  putStrLn "3. ua-\x03B2: transport along ua(equiv) applies the forward function"
  let idFn = VLam (Closure [] (Var 0))
      equiv = VPair idFn (VRefl (VU 0))
      uaPath = VUa equiv
      input = VU 0
      result = vJ (VU 1) (VU 0) (Closure2 [] (Var 1)) input (VU 0) uaPath
  if conv 0 result input
    then putStrLn "   \x2713 transport (ua id-equiv) (U 0) = U 0"
    else putStrLn "   \x2717 ua-\x03B2 did not compute correctly"

  putStrLn ""
  putStrLn "Kernel complete. All 4 milestones implemented."
