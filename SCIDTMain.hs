module Main where
import System.Environment (getArgs, getProgName)
import System.IO (hSetBuffering, stdout, BufferMode(..))
import SCITypes (trapError, sciSubst, SCIFormula(..), SCIError(..))
import SCIParse (readFormula)
import SCITest (putCompare, putTruths, putSizes, putSubs, putCheckModel,
                putRSProof, putRSDecision, putRSResult, putRSSizes,
                mod3, mod4)
import SCIModel (mod1, mod2)
import RSProof (rsProof)
import SCIRS (SCINode(..), startNode)

cmd :: String -> Char
cmd (x:_)
        | x == 's' || x == 'S' = 's'
        | x == 'n' || x == 'N' = 'n'
        | x == 'l' || x == 'L' = 'l'
        | otherwise = 'h'
cmd _ = 'h'

help :: IO ()
help = do
    name <- getProgName
    putStrLn $ "Usage: " ++ name ++ " [action [formula]]"
    putStrLn "action = S (short): show if the program finds a proof or not"
    putStrLn "action = N (normal): show successful proof or failed branch"
    putStrLn "action = L (long): always show full tree"
    putStrLn "action = H (help): this message"
    putStrLn ""
    putStrLn "The program asks for inputs not given on the command line."
    putStrLn "Example formulas: x, x or not x, (x & y) & z, a -> b, m <-> ~~m, u = v"

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    argline <- getArgs
    input1 <- if length argline > 0
        then return $ argline !! 0
        else putStrLn "Short/Normal/Long output, or Help (S/N/L/H)?" >> getLine
    input2 <- if length argline > 1
        then return $ argline !! 1
        else if cmd input1 == 'h' then return "x"
        else putStrLn "Input formula: " >> getLine
    let f = readFormula input2
    case f of
        Left x -> putStrLn $ "Input error: " ++ show x
        Right x -> do
            let prf = rsProof $ startNode x
            case cmd input1 of
                's' -> putRSResult prf >> putRSSizes prf
                'n' -> putRSDecision prf
                'l' -> putRSProof prf >> putRSSizes prf
                'h' -> help
