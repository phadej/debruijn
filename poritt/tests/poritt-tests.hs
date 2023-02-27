module Main (main) where

import Control.Exception (handle)
import Control.Monad     (forM, void)
import Data.List         (sort)
import System.Directory  (doesDirectoryExist, doesFileExist, listDirectory, setCurrentDirectory)
import System.Exit       (ExitCode (..))
import System.FilePath   (dropExtension, takeExtension, takeFileName, (-<.>), (</>))
import System.IO         (IOMode (WriteMode), hPutStrLn, withFile)
import System.IO.Temp    (withSystemTempDirectory)
import Test.Tasty        (defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsFileDiff)

import PoriTT.Main (batchFile, builtinEnvironment)
import PoriTT.Opts (defaultOpts)

main :: IO ()
main = do
    cwd
    examples <- sort . filter (\fn -> takeExtension fn == ".ptt") <$> listFilesRecursively "examples"
    withSystemTempDirectory "poritt-tests" $ \tmpDir -> do
        defaultMain $ testGroup "poritt"
            [ goldenVsFileDiff (dropExtension ex) diff out tmp $
                withFile tmp WriteMode $ \hdl -> do
                    let exitCode :: ExitCode -> IO ()
                        exitCode (ExitFailure _) = hPutStrLn hdl "ExitFailure"
                        exitCode _               = return ()

                    handle exitCode $ void $ batchFile defaultOpts inp hdl builtinEnvironment

            | ex <- examples
            , let tmp = tmpDir </> takeFileName ex -<.> "tmp"
            , let out = "examples" </> ex -<.> "stdout"
            , let inp = "examples" </> ex
            ]
  where
    diff ref new = ["diff", "-u", ref, new]

listFilesRecursively :: FilePath -> IO [FilePath]
listFilesRecursively = go "" where
    go :: FilePath -> FilePath -> IO [FilePath]
    go pfx dir = do
        xs <- listDirectory dir
        fmap concat $ forM xs $ \x -> do
            does <- doesDirectoryExist (dir </> x)
            if does
            then go (pfx </> x) (dir </> x)
            else return [pfx </> x]

cwd :: IO ()
cwd = do
    here <- doesFileExist "poritt.cabal"
    if here then return () else setCurrentDirectory "poritt"
