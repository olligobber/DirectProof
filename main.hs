{-# LANGUAGE OverloadedStrings #-}

import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Data.String (fromString)
import System.Environment (getArgs)
import System.IO (hFlush, stdout)

import WFF (WFF(..))
import Convert
import WFFParser
import Render (putRender)
import ReLabel (SmartIndex(Value))
import Logical (counterexample)
import Proof (verify)
import DirectedProof (toPlain)

-- Simple prompt for input
prompt :: String -> IO Text
prompt p = putStr p >> hFlush stdout >> TIO.getLine

-- Prompt for a conclusion and assumptions
promptInput :: IO [WFF Text]
promptInput = do
	goal <- prompt "Conclusion: "
	case parseWFF "Conclusion" goal of
		Left e -> print e >> promptInput
		Right c -> (c:) <$> promptAssumptions 1

-- Prompt for the nth assumption
promptAssumptions :: Int -> IO [WFF Text]
promptAssumptions 1 = do
	newa <- prompt "Assumption 1: "
	case parseWFF "Assumption 1" newa of
		Left e -> print e >> promptAssumptions 1
		Right a -> (a:) <$> promptAssumptions 2
promptAssumptions i = do
	newa <- prompt $ "Assumption " ++ show i ++ " (leave blank to finish): "
	case (newa, parseWFF ("Assumption " ++ show i) newa) of
		("", _) -> return []
		(_, Left e) -> print e >> promptAssumptions i
		(_, Right a) -> (a:) <$> promptAssumptions (i+1)

-- Print out feedback for selected input
solve :: [WFF Text] -> IO ()
solve [] = error "No conclusion"
solve [_] = error "No assumptions"
solve (goal:starts) = case (counterexample [False,True] starts goal,
	counterexample [Just False, Nothing, Just True] starts goal) of
		(Nothing, Nothing) -> do
			let pf = convert (fmap Value <$> starts) (Value <$> goal)
			putRender pf
			case verify $ toPlain pf of
				Nothing -> return ()
				Just l -> error $ "Proof has an error on line " ++ show l
		(Nothing, Just t) -> do
			putStrLn "Cannot be proven directly, due to the following"
			putStrLn "3-valued assignment being a counter-example:"
			putRender t
		(Just t, Just _) -> do
			putStrLn "Cannot be proven, due to the following boolean"
			putStrLn "assignment being a counter-example:"
			putRender t
		(Just _, Nothing) -> error "Counter-example function failed"

main :: IO ()
main = do
	args <- getArgs
	case args of
		[] -> promptInput >>= solve -- Interactive mode
		[_] -> do -- Tried to use arguments but was wrong, providing help
			putStrLn "To use command line arguments, provide the conclusion"
			putStrLn "as the first argument, and the assumptions as the rest"
			promptInput >>= solve -- Now enter interactive mode
		_ -> case traverse -- Arguments provided, try and parse
			(\(i,x) -> parseWFF
				(if i == 0 then "Conclusion" else "Assumption " ++ show i) $
				fromString x) $
			zip ([0..] :: [Int]) args of
				-- Error parsing, show it and enter interactive mode
				Left e -> print e >> promptInput >>= solve
				-- Success parsing, output feedback
				Right as -> solve as
