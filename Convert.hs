module Convert (convert) where

import qualified Control.Monad.Writer as W

import WFF (WFF)
import DNF (toDNF)
import DNFConvert
import DirectedProof (DirectedProof)
import qualified DirectedProof as D
import ReLabel (SmartIndex)

convert :: Ord x => WFF (SmartIndex x) -> WFF (SmartIndex x) ->
    DirectedProof (SmartIndex x)
convert start goal = ptoDNF <> pconvertDNF <> pfromDNF where
    (startDNF, ptoDNF) = D.toDirected <$> W.runWriter (toDNF start)
    (goalDNF, pfromDNF) = D.toDirected . D.invert <$> W.runWriter (toDNF goal)
    pconvertDNF = W.execWriter $ convertDNF startDNF goalDNF
