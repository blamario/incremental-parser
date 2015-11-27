
import Control.Applicative (empty, many, optional, (<$>), (<|>))
import Control.Monad.Trans (lift)
import Data.Void (Void)
import Data.Conduit
import Text.ParserCombinators.Incremental.LeftBiasedLocal

main = upstream $$ parseC

upstream :: ConduitM () String IO ()
upstream = do yield "hello"
              yield "yoyo"
              yield "yowait"
              yield "bye"
              yield "hello"
              yield "bye"
              yield "hello"
              yield "hello"
              yield "bye"
              yield "yo"

parseC :: ConduitM String Void IO ()
parseC = parseWith parser

parseWith :: Parser String [Either String (String, [String], Maybe String, String)] -> ConduitM String Void IO ()
parseWith p = do next <- await
                 case next
                    of Just s -> do let (r, p') = resultPrefix (feed s p)
                                    lift (mapM print r)
                                    parseWith p'
                       Nothing -> lift (putStrLn $ "Final result: " ++ show (completeResults (feedEof p)))

parser :: Parser String [Either String (String, [String], Maybe String, String)]
parser = myMany $ (
         do greeting <- string "hello"
            more <- many (string "yo")
            w <- optional (string "wait")
            end <- string "bye"
            return $ Right (greeting, more, w, end)
         <|>
         Left <$> string "hello"
         <|>
         Left <$> concatSome (notFollowedBy (string "hello" <|> eof) >< anyToken)
         )
--         Left <$> manyTill anyToken (string "hello")
