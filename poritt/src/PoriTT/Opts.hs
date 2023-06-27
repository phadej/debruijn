module PoriTT.Opts (
    Opts (..),
    defaultOpts,
    parseOpts,
) where

import PoriTT.Base

import qualified Options.Applicative as O

data Opts = Opts
    { optsEvalFull :: !Bool  -- ^ Evaluate the terms fully
    , optsEcho     :: !Bool  -- ^ Echo the poritt statements
    , dumpPs       :: !Bool
    , dumpRn       :: !Bool
    , dumpTc       :: !Bool
    , dumpSt       :: !Bool
    , dumpSimpl    :: !Bool
    }
  deriving Show

defaultOpts :: Opts
defaultOpts = Opts
    { optsEvalFull = False
    , optsEcho     = True
    , dumpPs       = False
    , dumpRn       = False
    , dumpTc       = False
    , dumpSt       = False
    , dumpSimpl    = False
    }

optsP :: O.Parser [Opts -> Opts]
optsP = many $ asum
    [ O.flag' (\ o -> o { dumpTc = True }) $ O.long "dump-tc" <> O.help "Dump type-checked term"
    , O.flag' (\ o -> o { dumpSt = True }) $ O.long "dump-st" <> O.help "Dump staged term"
    ]

argP :: O.Parser FilePath
argP = O.strArgument $ mconcat
    [ O.metavar "FILE"
    , O.help "input file"
    ]

parseOpts :: IO (Opts, [FilePath])
parseOpts = do
    (endos, args) <- O.execParser opts
    return (foldl' (&) defaultOpts endos, args)
  where
    opts = O.info (liftA2 (,) optsP (many argP) <**> O.helper) $ mconcat
        [ O.fullDesc
        , O.header "poritt - a type system from up north"
        ]
