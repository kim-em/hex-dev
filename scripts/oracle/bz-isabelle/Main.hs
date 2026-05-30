module Main where

import Control.Exception (SomeException, evaluate, try)
import Data.Char (isSpace)
import Hex_BZ (factor_int_poly)
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdin, stdout)
import Text.Read (readMaybe)

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

findNeedle :: String -> String -> Maybe String
findNeedle [] hay = Just hay
findNeedle _ [] = Nothing
findNeedle needle hay@(_:rest)
  | needle `prefixOf` hay = Just (drop (length needle) hay)
  | otherwise = findNeedle needle rest
  where
    prefixOf [] _ = True
    prefixOf _ [] = False
    prefixOf (x:xs) (y:ys) = x == y && prefixOf xs ys

arrayPayload :: String -> Maybe String
arrayPayload line = do
  rest <- findNeedle "\"coeffs\"" line
  afterOpen <- case dropWhile (/= '[') rest of
    [] -> Nothing
    (_:xs) -> Just xs
  let (payload, suffix) = span (/= ']') afterOpen
  case suffix of
    [] -> Nothing
    _ -> Just payload

parseCoeffs :: String -> Maybe [Integer]
parseCoeffs line = do
  payload <- arrayPayload line
  readMaybe ("[" ++ payload ++ "]")

jsonList :: [Integer] -> String
jsonList xs = "[" ++ go xs ++ "]"
  where
    go [] = ""
    go [x] = show x
    go (x:rest) = show x ++ "," ++ go rest

jsonFactors :: [([Integer], Integer)] -> String
jsonFactors xs = "[" ++ go xs ++ "]"
  where
    one (coeffs, mult) =
      "{\"coeffs\":" ++ jsonList coeffs ++ ",\"multiplicity\":" ++ show mult ++ "}"
    go [] = ""
    go [x] = one x
    go (x:rest) = one x ++ "," ++ go rest

reply :: [Integer] -> String
reply coeffs =
  let (scalar, factors) = factor_int_poly coeffs
  in "{\"ok\":true,\"result\":{\"scalar\":" ++ show scalar ++
     ",\"factors\":" ++ jsonFactors factors ++ "}}"

handleLine :: String -> IO String
handleLine line =
  case parseCoeffs line of
    Nothing -> pure "{\"ok\":false,\"error\":\"expected JSON object with integer array field coeffs\"}"
    Just coeffs -> do
      result <- try (evaluate (reply coeffs)) :: IO (Either SomeException String)
      case result of
        Left err -> pure ("{\"ok\":false,\"error\":" ++ show (show err) ++ "}")
        Right out -> pure out

main :: IO ()
main = do
  hSetBuffering stdin LineBuffering
  hSetBuffering stdout LineBuffering
  interactLines
  where
    interactLines = do
      done <- getLineOrEnd
      case done of
        Nothing -> pure ()
        Just line -> do
          handleLine (trim line) >>= putStrLn
          interactLines

getLineOrEnd :: IO (Maybe String)
getLineOrEnd = do
  result <- try getLine :: IO (Either SomeException String)
  case result of
    Left _ -> pure Nothing
    Right line -> pure (Just line)
