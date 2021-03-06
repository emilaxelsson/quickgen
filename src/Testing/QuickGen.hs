{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Testing.QuickGen
       ( -- generate

       -- Rexports
       defineLanguage
       ) where

-- import Control.Lens (_1, _2, _3, (^.), to, (.~), (&), (%~))
-- import Control.Monad
-- import Data.Char (ord, chr)
-- import Data.Maybe (catMaybes, listToMaybe, fromJust)
-- import Data.Typeable
-- import System.Random
-- import Test.Feat

-- Local imports
import Testing.QuickGen.ExpGen
import Testing.QuickGen.TH
import Testing.QuickGen.Types

{-

generate :: Type -> Int -> Context -> Maybe Exp
generate t seed ctx = case runEG g seed ctx of
    Nothing             -> Nothing
    Just (Prim (e,_,_)) -> Just e
  where
    (_, ts) = extractPrimType t
    g       = generate' ts

generate' :: [Type] -> GenContext (Maybe Primitive)
generate' [t] = replicateM 2 p >>= return . listToMaybe . catMaybes
  where
    p = do
        m <- randomMatching t
        case m of
            Nothing                    -> return Nothing
            Just p@(Prim (e, c, [t]))  -> decUses p >> return m
            Just p@(Prim (e, c, all@(t:ts))) -> do
                decUses p
                let go [] acc = return (True, acc)
                    go (t : ts) acc = do
                        mp <- generate' [t]
                        case mp of
                            Nothing -> return (False, acc)
                            Just p  -> go ts (p : acc)

                (b, args) <- go ts []
                case b of
                    False -> mapM_ incUses args >> incUses p >> return Nothing
                    True  ->
                        let e' = foldl AppE e (map ((^. _1) . unPrimitive) args)
                        in return (Just (Prim (e', c, [t])))

    toExpList :: [Maybe Primitive] -> Maybe [Exp]
    toExpList = fmap (reverse . map ((^. _1) . unPrimitive)) . sequence

generate' all@(t:ts) = do
    ret <- localLambda ts (generate' [t])
    case ret of
        Nothing        -> return Nothing
        Just (Prim (e, c, _)) -> do
            d <- getDepth
            let vars = [ VarP (mkName [chr (i + d + ord 'a')])
                       | i <- [0 .. length ts - 1]
                       ]
                e' = LamE vars e
            return (Just (Prim (e', c, all)))

randomMatching :: Type -> GenContext (Maybe Primitive)
randomMatching match = do
    ms <- getMatching match
    case length ms of
        0 -> return Nothing
        n -> do
            i <- getRandomR (0, n-1)

            getRandomR (0, n-1) >>= return . Just . (ms !!)

-}
