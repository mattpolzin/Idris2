||| Provides semantic versioning `Version` type and utilities.
||| See [semver](https://semver.org/) for proper definition of semantic versioning
module Data.Version

import Data.List
import Data.SnocList
import Data.String

%default total

||| Semantic versioning with optional tag
public export
record Version where
  constructor MkVersion
  ||| Semantic version
  ||| Should follow the (major, minor, patch) convention
  semVer : (Nat, Nat, Nat)
  ||| Optional tag
  ||| Usually contains git sha1 of this software's build in between releases
  versionTag : Maybe String

||| String representation of a Version with optional display of `tag`
export
showVersion : Bool -> Version -> String
showVersion tag (MkVersion (maj,min,patch) versionTag) =
  concat (intersperse "." (map show [ maj, min, patch])) ++
         if tag then showTag else ""
  where
    showTag : String
    showTag = case versionTag of
                Nothing => ""
                Just tag => "-" ++ tag

export
Show Version where
  show = showVersion True

export
Eq Version where
  (==) (MkVersion ver tag) (MkVersion ver' tag') = ver == ver' && tag == tag'

export
Ord Version where
  compare (MkVersion ver tag) (MkVersion ver' tag')  =
    case compare ver ver' of
      EQ => compare tag tag'
      other => other

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

record Parser (ty : Type) where
  constructor MkParser
  runParser : List Char -> Maybe (List Char, ty)

Functor Parser where
  map f (MkParser g) = MkParser $ \s => mapSnd f <$> (g s)

Applicative Parser where
  pure x = MkParser $ \s => Just (s, x)
  (MkParser f) <*> (MkParser g) =
    MkParser $ \s =>
      do (s', f') <- f s
         map f' <$> g s'

Alternative Parser where
  empty = MkParser (\_ => Nothing)
  (MkParser f) <|> p2 =
    MkParser $ \s =>
      case f s of
           Just res => pure res
           Nothing  => runParser p2 s

Monad Parser where
  (MkParser g) >>= f =
    MkParser $ \s =>
      do (s', g') <- g s
         let (MkParser f') = f g'
         f' s'

end : Parser ()
end = MkParser $ \case [] => Just ([], ())
                       _  => Nothing

char : Parser Char
char = MkParser c
where
  c : List Char -> Maybe (List Char, Char)
  c [] = Nothing
  c (x :: xs) = Just (xs, x)

exact : Char -> Parser Char
exact x = MkParser $ \case []        => Nothing
                           (y :: xs) => case x == y of
                                             False => Nothing
                                             True  => Just (xs, y)

string : Parser String
string =
  MkParser $ \case [] => Nothing
                   xs => Just ([], pack xs)

digit : Char -> Maybe Nat
digit '0' = Just 0
digit '1' = Just 1
digit '2' = Just 2
digit '3' = Just 3
digit '4' = Just 4
digit '5' = Just 5
digit '6' = Just 6
digit '7' = Just 7
digit '8' = Just 8
digit '9' = Just 9
digit _   = Nothing

num : Parser Nat
num =
  MkParser $ \xs =>
    do (xs', n) <- firstDigit xs
       pure $ go xs' n
  where
    firstDigit : List Char -> Maybe (List Char, Nat)
    firstDigit [] = Nothing
    firstDigit (x :: xs) = (xs,) <$> digit x

    go : List Char -> (acc : Nat) -> (List Char, Nat)
    go [] acc = ([], acc)
    go (x :: xs) acc = case digit x of
                            Nothing  => (x :: xs, acc)
                            (Just y) => go xs ((acc * 10) + y)

version : Parser Version
version =
  do maj <- num
     _ <- exact '.'
     min <- num
     _ <- exact '.'
     patch <- num
     tag <- versionTag <|> pure Nothing
     pure (MkVersion (maj, min, patch) tag)
  where
    versionTag : Parser (Maybe String)
    versionTag =
      do _ <- exact '-'
         Just <$> string

||| Parse given string into a proper `Version` record
|||
||| Expected format must be:
||| ```
||| <major>.<minor>.<patch>(-<tag>)?
||| ```
||| where <major>, <minor> and <patch> are natural integers and tag is an optional
||| alpha-numeric string.
export
parseVersion : String -> Maybe Version
parseVersion str =
  do ([], version) <- runParser version (unpack str)
       | (extra, _) => Nothing
     pure version

