{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}

module Testing.QuickGen.Types
       ( Exp(..)
       , Pat(..)
       , Type(..)
       , Cxt(..)
       , HValue(..)
       , Context(..)
       , Uses
       , Primitive(..)
       , ClassEnv
       , Substitution(..)
       , Id
       , mkName
       , listToContext
       , extractPrimType
       , complexity
       , subst
       , nextId
       -- rexports
       , (<>)
       , pprint
       ) where

import Control.Applicative
import Control.Lens ((&), _2, (%~), _1, (.~))
import Control.Monad
import Control.Monad.State.Lazy
import Data.List (lookup)
import Data.Maybe (fromJust, maybe, listToMaybe, catMaybes)
import Data.Monoid
import Language.Haskell.TH
import System.Random

type Uses = Maybe Int
type Substitution = [(Name, Type)]
type Id = Int

-- | A primitive value is an Expression together with the type of the
--   expression. The type is represented as a list where the first
--   element is the return type, the second element is the last
--   argument. The type `(a -> b) -> a -> b' whould then be
--   represented as `[b, a, (a -> b)]'.
newtype Primitive = Prim { unPrimitive :: (Id, Exp, Cxt, [Type]) }

instance Eq Primitive where
    Prim (id1, _, _, _) == Prim (id2, _, _, _) = id1 == id2

newtype Context = C { unContext :: [(Uses, Primitive)] }

substVars :: Int -> Type -> (Int, Type)
substVars k t = (k', t')
  where
    lookupAny name = listToMaybe . catMaybes . map (lookup name)
    (t', (k', _)) = runState (go t) (k, [[]])
    go :: Type -> State (Int, [[(Name, Name)]]) Type
    go (ForallT ns cxt t) = do
        (n, ms) <- get
        put (n, [] : ms)

        ns' <- forM ns $ \(PlainTV name) -> do
            (n, all@(m:ms)) <- get
            case lookupAny name ms of
                Just name' -> return name'
                Nothing -> do
                    let new = mkName ("g_" ++ show k)
                        m' = (name, new) : m
                    put (n+1, m' : ms)
                    return new
        cxt' <- forM cxt $ \(ClassP n ts) ->
            ClassP n <$> mapM go ts

        t' <- go t
        (n', _) <- get
        put (n', ms)

        return $ ForallT (map PlainTV ns') cxt' t'

    go (AppT t1 t2) = AppT <$> go t1 <*> go t2
    go (VarT name) = do
        (n, all@(m:ms)) <- get
        case lookupAny name all of
            Just name' -> return (VarT name')
            Nothing -> do
                let new = mkName ("g_" ++ show n)
                    m' = (name, new) : m
                put (n+1, m' : ms)
                return (VarT new)
    go t@(ConT _) = return t
    go t@ArrowT = return t
    go t@ListT = return t
    go t = error $ "hngh " ++ show t

listToContext :: Int -> [(Exp, Type)] -> Context
listToContext uses xs = C ctx
  where
    (_, _, ctx) = foldr f (0, 0, []) xs
    f (e, t) (i, d, acc) =
        let (d', t') = substVars d t
            (c, ts)  = extractPrimType t'
            uses'    = case ts of
                [_] -> Nothing
                _   -> Just uses
        in (i+1, d', (uses', Prim (i, e, c, ts)) : acc)

instance Monoid Context where
    mempty  = C []
    mappend (C c1) (C c2) = C $ mappend c1 c2

instance Show Primitive where
    show (Prim (i, e, c, t)) = "Prim #" ++ show i ++ ": " ++ show e ++ " :: " ++ show c ++ " => " ++ show t

instance Show Context where
    show = show . map showPrim . unContext
      where
        showPrim (uses, p) = "Uses: " ++ show uses ++ " " ++ show p

-- TODO: figure out why this is needed
newtype HValue = HV (forall a. a)

type ClassEnv = [(Name, [InstanceDec])]

extractPrimType :: Type -> (Cxt, [Type])
extractPrimType t = (cxt, reverse ts)
  where
    (cxt, ts) = go t
    go (AppT (AppT ArrowT t1) rest) = go rest & _2 %~ (t1:)

    -- TODO: merge constraints somehow. Right now I'm only overriding the
    -- current value, i.e. I'm hoping there were no constraints before.
    go (ForallT vars cxt rest)      = go rest & _1 .~ cxt

    go a                            = ([], [a])

complexity :: Type -> Int
complexity (ConT _)     = 0
complexity (VarT _)     = 1
complexity ArrowT       = 1
complexity ListT        = 0
complexity (AppT t1 t2) = complexity t1 + complexity t2
complexity (TupleT _)   = 0
complexity t            = error $ "Types.complexity: " ++ show t ++ " not matched!"

subst :: Name -> Type -> Type -> Type
subst match new t@(VarT name)
    | match == name = new
    | otherwise     = t
subst match new (AppT t1 t2) = AppT (subst match new t1) (subst match new t2)
subst match new t@(ForallT ns c t') = case match `elem` map (\(PlainTV n) -> n) ns of
    True  -> t
    False -> ForallT ns c (subst match new t')
subst match new (SigT t k) = SigT (subst match new t) k
subst _ _ t = t

nextId :: Context -> Id
nextId (C [])                        = 0
nextId (C ((_, Prim (i,_,_,_)) : _)) = i+1
