{-# LANGUAGE OverloadedStrings #-}

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Maybe (listToMaybe)
import WFF (WFF(..))
import qualified WFF
-- import Deductions (Deduction)
-- import qualified Deductions as D

data Proof c = Proof {
    formulas :: [WFF c],
    justifications :: [(Text, [Int])],
    propRender :: c -> String,
    numlines :: Int
}

-- Given a function to render propositions and a list of premises, make a proof
newProof :: (c -> String) -> [WFF c] -> Proof c
newProof rend premises = Proof premises (("Premise", []) <$ premises) rend (length premises)

-- -- Apply any rule to the proof
-- addLine :: Eq c => Proof c -> [Proof c]
-- addLine proof = do
--     (name, rule) <- D.rules
--     (references, newline) <- D.applyAny rule $ formulas proof
--     return $ Proof
--         (newline:formulas proof)
--         ((name, (numlines proof -) <$> references):justifications proof)
--         (propRender proof)
--         (numlines proof + 1)

renderProof :: Proof c -> Text
renderProof proof = T.unlines $ reverse renderedLines
    where
        renderedFormulas = T.pack . WFF.render (propRender proof) <$> formulas proof
        renderedLineNumbers = T.pack . show <$> [numlines proof, numlines proof-1..1]
        renderedJustifications = (\(name, references) -> mconcat [name, " ", T.intercalate "," $ T.pack . show <$> references]) <$> justifications proof
        longestFormula = maximum $ T.length <$> renderedFormulas
        longestLineNumber = maximum $ T.length <$> renderedLineNumbers
        justifiedFormulas = T.center longestFormula ' ' <$> renderedFormulas
        justifiedLineNumbers = T.justifyRight longestLineNumber ' ' <$> renderedLineNumbers
        renderedLines = T.intercalate " | " <$> zipWith3 (\x y z -> [x,y,z]) justifiedLineNumbers justifiedFormulas renderedJustifications

-- allProofsLength :: Eq c => Proof c -> Int -> [Proof c]
-- allProofsLength proof len
--     | len < numlines proof      = []
--     | len == numlines proof     = [proof]
--     | otherwise                 = allProofsLength proof (len-1) >>= addLine
--
-- allProofs :: Eq c => Proof c -> [Proof c]
-- allProofs proof = [1..] >>= allProofsLength proof
--
-- anyProofLogging :: Eq c => WFF c -> Proof c -> [Text]
-- anyProofLogging goal proof = goLog $ filter (\(n,pf) -> head (formulas pf) == goal || n `mod` 1000000 == 0) $ zip [(1::Integer)..] $ allProofs proof where
--     goLog ((n, pf):pfs)
--         | head (formulas pf) == goal    = [renderProof pf]
--         | otherwise                     = mconcat ["Proof ", T.pack . show . (`div` 1000000) $ n, " million has length ", T.pack . show $ numlines pf] : goLog pfs
--
-- main :: IO ()
-- main = mapM_ TIO.putStrLn $ anyProofLogging (Prop "Z" :&: Prop "Y") $ newProof id [(Prop "V" :>: Not (Prop "W")) :&: (Prop "X" :>: Prop "Y"), Not (Prop "W") :>: Prop "Z", Prop "V" :&: Prop "X"]

-- Find all proofs up to a given length to prove a given goal
-- allProofs :: Eq c => Int -> WFF c -> Proof c -> [Proof c]
-- allProofs maxlength goal proof
--     | maxlength <= numlines proof = if head (formulas proof) == goal then [proof] else []
--     | otherwise = (if head (formulas proof) == goal then (proof:) else id) $ addLine proof >>= allProofs maxlength goal

-- Find any proof up to a given length to prove a given goal
-- anyProof :: Eq c => Int -> WFF c -> Proof c -> Maybe (Proof c)
-- anyProof maxlength goal proof = listToMaybe $ allProofs maxlength goal proof
