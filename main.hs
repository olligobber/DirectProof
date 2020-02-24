import Data.Function (on)
import Data.Functor.Compose (Compose(Compose))

import WFF (WFF(..))
import Convert
import Render (putRenders)
import ReLabel (SmartIndex(Value))

start :: WFF String
start = Prop "A" :&: (Prop "A" :>: Prop "B")

goal :: WFF String
goal = Prop "B"

main :: IO ()
main = putRenders $ Compose $ (convert `on` fmap Value) start goal
