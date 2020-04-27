module Convert (convert) where

import qualified Control.Monad.Writer as W

import WFF (WFF)
import DNF (toDNF)
import DNFConvert
import DirectedProof (DirectedProof)
import qualified DirectedProof as D
import ReLabel (SmartIndex)

-- Make a proof from some assumptions to a conclusion
convert :: Ord x => [WFF (SmartIndex x)] -> WFF (SmartIndex x) ->
	DirectedProof (SmartIndex x)
convert starts goal = combine <> ptoDNF <> pconvertDNF <> pfromDNF where
	-- Combine all assumptions into one formula
	(start, combine) = W.runWriter $ D.assumptions starts
	-- Convert assmuptions to DNF
	(startDNF, ptoDNF) = D.toDirected <$> W.runWriter (toDNF start)
	-- Convert conclusion to DNF
	(goalDNF, pfromDNF) = D.toDirected . D.invert <$> W.runWriter (toDNF goal)
	-- Convert between DNFs
	pconvertDNF = W.execWriter $ convertDNF startDNF goalDNF
