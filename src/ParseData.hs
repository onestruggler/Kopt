-- ParseData.hs
-- Parse experiment_data.dat and draw the distribution of lde values.
-- Usage: runghc ParseData.hs experiment_data.dat
--    or: ghc -O2 ParseData.hs -o parsedata && ./parsedata experiment_data.dat

module Main where

import Data.Char (isSpace)
import Data.List (group, sort, intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)
import Numeric (showFFloat)
import System.IO (hPutStrLn, stderr)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A Gaussian integer a + bi, stored as (a, b).
type GaussInt = (Integer, Integer)

-- | A 4×4 matrix of Gaussian integers.
type Mat4 = [[GaussInt]]

-- | One record: (lde, matrix, ourCS, theirCS, ourK, theirK)
data Record = Record
  { lde     :: !Int
  , mat     :: Mat4
  , ourCS   :: !Int
  , theirCS :: !Int
  , ourK    :: !Int
  , theirK  :: !Int
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Minimal hand-rolled parser (no dependencies beyond base)
-- ---------------------------------------------------------------------------

-- | Parser: consumes a prefix of the string, returns (value, rest).
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> case p s of
    Nothing      -> Nothing
    Just (a, s') -> Just (f a, s')

instance Applicative Parser where
  pure a = Parser $ \s -> Just (a, s)
  Parser pf <*> Parser pa = Parser $ \s -> do
    (f, s')  <- pf s
    (a, s'') <- pa s'
    pure (f a, s'')

instance Monad Parser where
  Parser pa >>= f = Parser $ \s -> do
    (a, s') <- pa s
    runParser (f a) s'

-- | Consume optional whitespace.
spaces :: Parser ()
spaces = Parser $ \s -> Just ((), dropWhile isSpace s)

-- | Consume a specific character (with leading whitespace).
char :: Char -> Parser ()
char c = Parser $ \s ->
  let s' = dropWhile isSpace s
  in case s' of
       (x:xs) | x == c -> Just ((), xs)
       _               -> Nothing

-- | Parse a (possibly negative) integer.
int :: Parser Int
int = Parser $ \s ->
  let s' = dropWhile isSpace s
  in case s' of
       ('-':rest) ->
         let (digits, rest') = span (`elem` "0123456789") rest
         in if null digits then Nothing
            else Just (negate (read digits), rest')
       _ ->
         let (digits, rest') = span (`elem` "0123456789") s'
         in if null digits then Nothing
            else Just (read digits, rest')

-- | Parse a (possibly negative) Integer (arbitrary precision).
integer :: Parser Integer
integer = Parser $ \s ->
  let s' = dropWhile isSpace s
  in case s' of
       ('-':rest) ->
         let (digits, rest') = span (`elem` "0123456789") rest
         in if null digits then Nothing
            else Just (negate (read digits), rest')
       _ ->
         let (digits, rest') = span (`elem` "0123456789") s'
         in if null digits then Nothing
            else Just (read digits, rest')

-- | Parse a Gaussian integer: (a, b)
gaussInt :: Parser GaussInt
gaussInt = do
  char '('
  a <- integer
  char ','
  b <- integer
  char ')'
  pure (a, b)

-- | Parse a list: [x, x, x, ...]
listOf :: Parser a -> Parser [a]
listOf p = do
  char '['
  xs <- sepBy p (char ',')
  char ']'
  pure xs

-- | Parse items separated by a delimiter.
sepBy :: Parser a -> Parser () -> Parser [a]
sepBy p sep = do
  x <- p
  xs <- many' (sep >> p)
  pure (x : xs)
  where
    many' q = Parser $ \s ->
      case runParser q s of
        Nothing      -> Just ([], s)
        Just (a, s') -> case runParser (many' q) s' of
          Nothing       -> Just ([a], s')
          Just (as, s'') -> Just (a : as, s'')

-- | Parse one record line.
record :: Parser Record
record = do
  char '('                   -- outer (
  char '('                   -- matrix pair (
  l <- int                   -- lde
  char ','
  m <- listOf (listOf gaussInt)  -- 4×4 matrix
  char ')'                   -- close matrix pair
  char ','
  cs1 <- int
  char ','
  cs2 <- int
  char ','
  k1 <- int
  char ','
  k2 <- int
  char ')'                   -- close outer
  pure (Record l m cs1 cs2 k1 k2)

-- ---------------------------------------------------------------------------
-- Histogram rendering (terminal + SVG file)
-- ---------------------------------------------------------------------------

-- | Build a frequency map from a list of values.
histogram :: (Ord a) => [a] -> Map a Int
histogram = Map.fromListWith (+) . map (\x -> (x, 1))

-- | Render an ASCII histogram to the terminal.
asciiHist :: Map Int Int -> String
asciiHist h = asciiHistLabelled h (\k -> let s = show k in replicate (4 - length s) ' ' ++ s)

-- | Render an ASCII histogram with custom label function.
asciiHistLabelled :: Map Int Int -> (Int -> String) -> String
asciiHistLabelled h labelFn =
  let maxCount = maximum (Map.elems h)
      maxBarW  = 60 :: Int
      scale c  = (c * maxBarW) `div` maxCount
      lo       = fst (Map.findMin h)
      hi       = fst (Map.findMax h)
      line k   = let c = Map.findWithDefault 0 k h
                 in labelFn k ++ " |" ++ replicate (scale c) '#'
                    ++ " (" ++ show c ++ ")"
      keys     = Map.keys h
  in unlines $
       ["", "  (n = " ++ show (sum (Map.elems h)) ++ ")", ""]
       ++ map line keys

-- | Write an SVG histogram to a file.
writeSvgHist :: FilePath -> Map Int Int -> String -> String -> IO ()
writeSvgHist path h chartTitle xLabel = do
  let entries   = Map.toAscList h
      lo        = fst (head entries)
      hi        = fst (last entries)
      allKeys   = [lo..hi]
      vals      = [Map.findWithDefault 0 k h | k <- allKeys]
      n         = length allKeys
      maxVal    = maximum vals
      -- Layout
      marginL   = 60 :: Int
      marginR   = 30
      marginT   = 50
      marginB   = 70
      barW      = max 8 (min 30 (800 `div` max 1 n))
      gap       = max 1 (barW `div` 6)
      chartW    = n * (barW + gap) - gap
      chartH    = 400 :: Int
      svgW      = marginL + chartW + marginR
      svgH      = marginT + chartH + marginB
      barH v    = (v * chartH) `div` max 1 maxVal
      barX i    = marginL + i * (barW + gap)
      barY v    = marginT + chartH - barH v

      -- Color palette: a gradient from teal to indigo
      barColor i =
        let t = fromIntegral i / fromIntegral (max 1 (n - 1)) :: Double
            r = round (83 * (1 - t) + 83 * t)   :: Int
            g = round (158 * (1 - t) + 74 * t)   :: Int
            b = round (117 * (1 - t) + 183 * t)  :: Int
        in "rgb(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ ")"

      header = unlines
        [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        , "<svg xmlns=\"http://www.w3.org/2000/svg\""
        , "     width=\"" ++ show svgW ++ "\" height=\"" ++ show svgH ++ "\""
        , "     viewBox=\"0 0 " ++ show svgW ++ " " ++ show svgH ++ "\">"
        , "<style>"
        , "  text { font-family: 'Helvetica Neue', Helvetica, sans-serif; }"
        , "  .title { font-size: 16px; font-weight: 500; fill: #1a1a1a; }"
        , "  .axis  { font-size: 11px; fill: #555; }"
        , "  .tick  { font-size: 10px; fill: #777; }"
        , "  .bar   { opacity: 0.88; }"
        , "  .bar:hover { opacity: 1; }"
        , "  .grid  { stroke: #e0e0e0; stroke-width: 0.5; }"
        , "</style>"
        , "<rect width=\"100%\" height=\"100%\" fill=\"#fafafa\" rx=\"6\"/>"
        ]

      title_ = "<text class=\"title\" x=\"" ++ show (svgW `div` 2)
               ++ "\" y=\"30\" text-anchor=\"middle\">" ++ chartTitle
               ++ " (n = " ++ show (sum vals) ++ ")</text>"

      -- Y-axis gridlines
      nTicks = 5 :: Int
      tickStep = maxVal `div` nTicks
      yTicks = if tickStep == 0 then [0, maxVal]
               else [0, tickStep .. maxVal]
      gridLines = concatMap (\v ->
        let y = barY v
        in "<line class=\"grid\" x1=\"" ++ show marginL
           ++ "\" y1=\"" ++ show y
           ++ "\" x2=\"" ++ show (marginL + chartW)
           ++ "\" y2=\"" ++ show y ++ "\"/>\n"
           ++ "<text class=\"tick\" x=\"" ++ show (marginL - 8)
           ++ "\" y=\"" ++ show (y + 4)
           ++ "\" text-anchor=\"end\">" ++ show v ++ "</text>\n"
        ) yTicks

      -- Bars
      bars = concat
        [ "<rect class=\"bar\" x=\"" ++ show (barX i)
          ++ "\" y=\"" ++ show (barY v)
          ++ "\" width=\"" ++ show barW
          ++ "\" height=\"" ++ show (barH v)
          ++ "\" rx=\"2\" fill=\"" ++ barColor i ++ "\"/>\n"
          -- X-axis label
          ++ "<text class=\"tick\" x=\""
          ++ show (barX i + barW `div` 2)
          ++ "\" y=\"" ++ show (marginT + chartH + 16)
          ++ "\" text-anchor=\"middle\">" ++ show k ++ "</text>\n"
        | (i, (k, v)) <- zip [0..] (zip allKeys vals)
        ]

      -- Axis labels
      xAxisLabel = "<text class=\"axis\" x=\"" ++ show (marginL + chartW `div` 2)
               ++ "\" y=\"" ++ show (svgH - 10)
               ++ "\" text-anchor=\"middle\">" ++ xLabel ++ "</text>"
      yLabel = "<text class=\"axis\" x=\"15\" y=\""
               ++ show (marginT + chartH `div` 2)
               ++ "\" text-anchor=\"middle\""
               ++ " transform=\"rotate(-90,15,"
               ++ show (marginT + chartH `div` 2) ++ ")\">count</text>"

      footer = "</svg>"

  writeFile path $ unlines
    [header, title_, gridLines, bars, xAxisLabel, yLabel, footer]

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  let file = case args of
               (f:_) -> f
               []    -> "experiment_data.dat"
  contents <- readFile file
  let ls = filter (not . null) . filter ((/= '#') . head) $
           lines contents
  let parsed = [ r | l <- ls
               , Just (r, _) <- [runParser record l]
               ]
  let failed = length ls - length parsed
  hPutStrLn stderr $ "Parsed " ++ show (length parsed)
                     ++ " records (" ++ show failed ++ " failed)"

  let ldes = map lde parsed
  let hist = histogram ldes

  -- Terminal output
  putStrLn (asciiHist hist)

  -- Summary statistics
  let n    = length ldes
      lo   = minimum ldes
      hi   = maximum ldes
      avg  = fromIntegral (sum ldes) / fromIntegral n :: Double
      med  = sort ldes !! (n `div` 2)
  putStrLn $ "  min = " ++ show lo
  putStrLn $ "  max = " ++ show hi
  putStrLn $ "  mean = " ++ show (round avg :: Int)
  putStrLn $ "  median = " ++ show med
  putStrLn ""

  -- Write SVG for lde
  let svgFile = "lde_distribution.svg"
  writeSvgHist svgFile hist "Distribution of lde" "lde"
  putStrLn $ "SVG histogram written to " ++ svgFile

  -- K-count reduction: (theirK - ourK) / theirK
  putStrLn "\n  === K-count reduction (Glaudell - ours) / Glaudell ==="
  let reductions = [ fromIntegral (theirK r - ourK r)
                     / fromIntegral (theirK r) * 100.0
                   | r <- parsed, theirK r > 0 ] :: [Double]
      nR       = length reductions
      sortedR  = sort reductions
      minR     = minimum reductions
      maxR     = maximum reductions
      avgR     = sum reductions / fromIntegral nR
      medR     = sortedR !! (nR `div` 2)
      zeroR    = length (filter (== 0) reductions)
  putStrLn $ "  min  = " ++ showFFloat (Just 1) minR "%"
  putStrLn $ "  max  = " ++ showFFloat (Just 1) maxR "%"
  putStrLn $ "  mean = " ++ showFFloat (Just 1) avgR "%"
  putStrLn $ "  median = " ++ showFFloat (Just 1) medR "%"
  putStrLn $ "  zero reduction = " ++ show zeroR ++ " / " ++ show nR
  putStrLn ""

  -- Bin into 2% buckets
  let bucket x = floor (x / 2) * 2 :: Int
      redHist  = histogram (map bucket reductions)
  putStrLn (asciiHistLabelled redHist
              (\k -> let s = show k ++ "-" ++ show (k+2) ++ "%"
                     in replicate (8 - length s) ' ' ++ s))

  -- Write SVG for reduction
  let svgFile2 = "k_reduction_distribution.svg"
  writeSvgHist svgFile2 redHist
    "K-count reduction (Glaudell - ours) / Glaudell"
    "reduction %"
  putStrLn $ "SVG histogram written to " ++ svgFile2
