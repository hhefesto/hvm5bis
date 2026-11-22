-- Order: put a Bend file's defs in dependency order.
--
-- Bend checks defs in file order and refuses a call to a def written
-- below its caller (and so refuses mutual recursion). This reads one
-- .bend file, splits it into top-level blocks (a def, type or law with
-- the comment lines right above it), and writes the blocks back so each
-- comes after every block it names, keeping the original order where
-- the dependencies allow. A cycle is reported and the file is left as
-- is. Usage: runghc tools/Order.hs FILE.bend
module Main (main) where

import Data.Char (isAlphaNum)
import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

data Block = Block { bName :: Maybe String, bLines :: [String] }

isStart :: String -> Bool
isStart l = any (`startsWith` l) ["def ", "type ", "law ", "@unsafe"]

startsWith :: String -> String -> Bool
startsWith p s = take (length p) s == p

-- the name a block defines: `def f.x(` / `type T` / `law f:`
nameOf :: String -> Maybe String
nameOf l
  | "def " `startsWith` l = Just (takeWhile nameChar (drop 4 l))
  | "type " `startsWith` l = Just (takeWhile nameChar (drop 5 l))
  | "law " `startsWith` l = Just (takeWhile nameChar (drop 4 l))
  | otherwise = Nothing

nameChar :: Char -> Bool
nameChar c = isAlphaNum c || c == '_' || c == '.'

-- split: a header (imports and the file comment) and the blocks; the
-- comment lines directly above a start line join that block
split :: [String] -> ([String], [Block])
split ls =
  let (hdr, rest) = breakHeader ls
  in (hdr, go [] rest)
  where
    go acc [] = finish acc []
    go acc (l : r)
      | isStart l =
          let (body0, r0) = span (not . isStart) r
              (body, moved) = splitTrailing body0
              (cs, acc') = takeTrailingComments acc
          in finish acc' [] ++ [Block (nameOf (dropUnsafe l r)) (cs ++ [l] ++ body)] ++ go moved r0
      | otherwise = go (acc ++ [l]) r
    finish [] _ = []
    finish acc _ = [Block Nothing acc]
    -- comment lines right above the next start belong to the next block
    splitTrailing xs =
      let rev = reverse xs
          (cs, keep) = span (\x -> "#" `startsWith` x) rev
      in (reverse keep, reverse cs)
    takeTrailingComments acc =
      let rev = reverse acc
          (cs, keep) = span (\x -> "#" `startsWith` x) rev
      in (reverse cs, reverse keep)
    dropUnsafe l r = if "@unsafe" `startsWith` l then case r of (x : _) -> x; [] -> l else l

-- the header: everything before the first block start or first comment
-- block that precedes one
breakHeader :: [String] -> ([String], [String])
breakHeader ls =
  let idx = length (takeWhile (not . isStart) ls)
      before = take idx ls
      rev = reverse before
      (cs, keep) = span (\x -> "#" `startsWith` x) rev
  in (reverse keep, reverse cs ++ drop idx ls)

-- the names a block mentions as calls `name(` (or `~name`), minus itself
refs :: S.Set String -> Block -> S.Set String
refs known (Block me ls) =
  let body = concatMap ((++ "\n") . takeWhile (/= '#')) (drop 1 (dropWhile (not . isStart) ls))
      toks = tokens body
      ref = S.fromList [t | t <- toks, t `S.member` known]
  in maybe ref (`S.delete` ref) me

tokens :: String -> [String]
tokens [] = []
tokens ('"' : r) = tokens (skipStr r)
  where
    skipStr ('\\' : _ : x) = skipStr x
    skipStr ('"' : x) = x
    skipStr (_ : x) = skipStr x
    skipStr [] = []
tokens s@(c : r)
  | nameChar c = let (t, r') = span nameChar s in t : tokens r'
  | otherwise = tokens r

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
    [p] -> pure p
    _ -> hPutStrLn stderr "usage: Order FILE.bend" >> exitFailure
  src <- readFile path
  length src `seq` pure ()
  let (hdr, blocks) = split (lines src)
      known = S.fromList [n | Block (Just n) _ <- blocks]
      idxd = zip [0 :: Int ..] blocks
      deps = M.fromList [(i, refs known b) | (i, b) <- idxd]
      owner = M.fromList [(n, i) | (i, Block (Just n) _) <- idxd]
      depIdx i = S.fromList [j | n <- S.toList (deps M.! i), Just j <- [M.lookup n owner], j /= i]
      loop done out pending
        | null pending = Right (reverse out)
        | otherwise =
            case [i | i <- pending, depIdx i `S.isSubsetOf` done] of
              (i : _) -> loop (S.insert i done) (i : out) (filter (/= i) pending)
              [] -> Left [n | i <- pending, Block (Just n) _ <- [blocks !! i]]
  case loop S.empty [] (map fst idxd) of
    Left cyc -> hPutStrLn stderr ("cycle among: " ++ unwords (take 20 cyc)) >> exitFailure
    Right order -> do
      let out = hdr ++ concatMap (\i -> bLines (blocks !! i)) order
      writeFile path (unlines (trimBlank out))
  where
    trimBlank = foldl' (\acc l -> if null l && not (null acc) && null (last acc) then acc else acc ++ [l]) []
