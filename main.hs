import Data.Function (on)
import Data.Functor.Compose (Compose(Compose))

import WFF (WFF(..))
import Convert
import Render (putRenders, putRenders2)
import ReLabel (SmartIndex(Value))
import Logical (counterexample)

start :: WFF String
start = Not (Prop "A") :&: Prop "A"

goal :: WFF String
goal = Prop "B"

main :: IO ()
main =
    case (counterexample [False,True] start goal,
        counterexample [Just False, Nothing, Just True] start goal) of
            (Nothing, Nothing) -> putRenders $ Compose $
                (convert `on` fmap Value) start goal
            (Nothing, Just t) -> do
                putStrLn "Cannot be proven directly, due to the following"
                putStrLn "3-valued assignment being a counter-example:"
                putRenders2 t
            (Just t, Just _) -> do
                putStrLn "Cannot be proven, due to the following boolean"
                putStrLn "assignment being a counter-example:"
                putRenders2 t
            (Just _, Nothing) -> putStrLn "What the fuck"
