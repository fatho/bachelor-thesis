{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TemplateHaskell           #-}
module Denotational.CuMin.Interpreter where

import qualified Data.Map                     as M
import           Data.Maybe

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader

import           Control.Lens                 hiding (each)
import           Data.Default.Class
import qualified Data.List                    as List

import qualified Data.Traversable             as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Language.CuMin.AST           as CuMin
import qualified Language.CuMin.TypeChecker   as CuMin

import qualified Debug.Trace                  as Debug

-- | Encapsulates the Alternative and MonadPlus constraints to be prepared
-- for the upcoming Applicative/Monad hierarchy in GHC 7.10
type NonDeterministic m = (Alternative m, MonadPlus m)

-- | A CuMin value, parameterized over a non-deterministic Monad n.
data Value n
  = VCon CuMin.DataConName [Value n]
  -- ^ ADT constructor
  | VNat Integer
  -- ^ natural number
  | VFun (Value n -> n (Value n))
  -- ^ function
  | VBot String
  -- ^ bottom with an annotation, which is ignored during computation but displayed in the result

-- | Allows transformation of Haskell values to CuMin values.
class ToValue a where
  -- | Takes a Haskell value and converts it to the corresponding CuMin value.
  toValue :: a -> Value n

instance ToValue Bool where
  toValue True = VCon "True" []
  toValue False = VCon "False" []

instance ToValue Integer where
  toValue = VNat

instance ToValue CuMin.Lit where
  toValue (CuMin.LNat n) = toValue n

instance PP.Pretty (Value n) where
  pretty (VCon con []) = PP.text con
  pretty (VCon con args) = PP.text con PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma (map PP.pretty args)
  pretty (VNat i)        = PP.integer i
  pretty (VFun _)        = PP.text "<closure>"
  pretty (VBot ann)      = PP.text "\x22A5"
    PP.<> if null ann then PP.empty else PP.enclose PP.langle PP.rangle $ PP.text ann -- "_|_"

-- | Environment needed during evaluation
data EvalEnv n
  = EvalEnv
  { _termEnv   :: M.Map CuMin.VarName (Value n)
  -- ^ the mapping from variable names to values \sigma
  , _typeEnv   :: M.Map CuMin.TVName (n (Value n))
  -- ^ the mapping from type variables to sets of value \theta
  , _moduleEnv :: CuMin.Module
  -- ^ the module providing a context for evaluating the expression
  , _constrEnv :: M.Map CuMin.DataConName CuMin.TyDecl
  -- ^ a map of data constructors with their respective types, derived from _moduleEnv.
  , _stepIdx   :: Integer
  -- ^ the current step index
  }

-- | The evaluation monad is just a reader monad with the above environment.
type Eval n = ReaderT (EvalEnv n) n

makeLenses ''EvalEnv

runEval :: Eval n a -> CuMin.Module -> Integer -> n a
runEval action context stepMax = runReaderT action env where
  env = EvalEnv M.empty M.empty context cns stepMax
  cns = context ^. CuMin.modADTs . traverse . to CuMin.adtConstructorTypes

-- | Decrements the step index by one in the action passed as argument
decrementStep :: Monad n => Eval n a -> Eval n a
decrementStep = local (stepIdx -~ 1)

-- | Converts list to an arbitrary non-deterministic monad.
each :: NonDeterministic m => [a] -> m a
each = foldr (mplus . return) mzero

-- | Applies variable substitution to a type
applySubst :: (CuMin.TVName -> CuMin.Type) -> CuMin.Type -> CuMin.Type
applySubst f (CuMin.TVar tv) = f tv
applySubst f (CuMin.TCon n xs) = CuMin.TCon n $ map (applySubst f) xs

-- | Generates all possible inhabitants of the given type up to the step index provided by the environment.
anything :: NonDeterministic n => CuMin.Type -> Eval n (Value n)
anything (CuMin.TVar tv) = view (typeEnv.at tv) >>= lift . fromMaybe (error "free type variable")
anything (CuMin.TFun _ _) = error "free variables cannot have a function type"
anything (CuMin.TNat) = view stepIdx >>= each . fmap VNat . enumFromTo 0
anything (CuMin.TCon tycon args) = view stepIdx >>= \case
  n | n <= 0 -> return $ VBot "anything: maximum number of steps exceeded"
    | otherwise -> do
      adt <- fromMaybe (error "ADT not found") <$> view (moduleEnv . CuMin.modADTs . at tycon)
      let subst = M.fromList $ zip (adt ^. CuMin.adtTyArgs) args
      join $ each <$> T.mapM (anythingCon subst) (adt ^. CuMin.adtConstr)

-- | Generates all inhabitants of the given constructor
anythingCon :: NonDeterministic n => M.Map CuMin.TVName CuMin.Type -> CuMin.ConDecl -> Eval n (Value n)
anythingCon subst (CuMin.ConDecl name args) = do
  let appF tv = fromMaybe (CuMin.TVar tv) (subst^.at tv)
  anyargs <- mapM (decrementStep . anything . applySubst appF) args
  return $ VCon name anyargs

-- | Evaluates a CuMin expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: NonDeterministic n => CuMin.Exp -> Eval n (Value n)
eval (CuMin.EVar var) = view (termEnv.at var) >>= \case
  Just val -> return val
  Nothing -> error "local variable not declared"
eval (CuMin.ELet var bnd body) = eval bnd >>= letVar body var
eval (CuMin.ELetFree var ty body) = anything ty >>= letVar body var
eval (CuMin.EFailed _) = return $ VBot "explicit failure"
eval (CuMin.EFun fun tyargs) = do
  curStepIdx <- view stepIdx
  if curStepIdx <= 0
    then return $ VBot $ "maximum number of steps exceeded when calling " ++ fun
    else do
      (CuMin.Binding _ args body (CuMin.TyDecl tyvars _ _) _) <- view $ moduleEnv . CuMin.modBinds . at fun . to fromJust
      curEnv <- ask
      let tyEnv = fmap (flip runReaderT curEnv . anything) $ M.fromList $ zip tyvars tyargs
      let f name rst vars = return $ VFun $ \val -> rst (M.insert name val vars)
          g vars = runReaderT (decrementStep $ withVars vars $ withTyVars tyEnv $ eval body) curEnv
      lift $ foldr f g args M.empty
eval (CuMin.EApp fun arg) =
  join $ liftM2 primApp (eval fun) (eval arg)

eval (CuMin.ELit lit) = return $ toValue lit

eval (CuMin.EPrim CuMin.PrimEq [ex,ey]) =
  liftM2 primEq (eval ex) (eval ey)
eval (CuMin.EPrim CuMin.PrimAdd [ex,ey]) =
  liftM2 primAdd (eval ex) (eval ey)
eval (CuMin.EPrim _ _) = error "illegal primitive operation call"
-- REMARK: Add future prim-ops to evaluator at this point

eval (CuMin.ECon con tyargs) = do
  tydecl <- fromMaybe (error "unknown type constructor") <$> view (constrEnv.at con)
  case CuMin.instantiate' tyargs tydecl :: Either (CuMin.TCErr CuMin.CuMinErrCtx) CuMin.Type of
    Left err -> error $ show tyargs ++ "\n" ++ show tydecl ++ "\ntype error when instantiating constructor: "
      ++ show (PP.plain $ PP.pretty err)
    Right inst ->
      let f _ rst dxs = VFun $ \x -> return $ rst (dxs . (x:))
          g _     dxs = VCon con (dxs [])
      in return $ foldType f g inst id
eval (CuMin.ECase scrut alts) = do
  scrutVal <- eval scrut
  patternMatch scrutVal alts

-- | Evaluate the body with a new variable in the term environment.
letVar :: NonDeterministic n => CuMin.Exp -> CuMin.VarName -> Value n -> Eval n (Value n)
letVar body var val = local (termEnv.at var .~ Just val) $ eval body

-- | Evaluate the body with new variable bindings in the term environment
withVars :: Monad n => M.Map CuMin.VarName (Value n) -> Eval n a -> Eval n a
withVars vars = local (termEnv %~ M.union vars)

withTyVars :: Monad n => M.Map CuMin.TVName (n (Value n)) -> Eval n a -> Eval n a
withTyVars tyvars = local (typeEnv %~ M.union tyvars)

-- | Folds along a function type signature
foldType :: (CuMin.Type -> a -> a) -> (CuMin.Type -> a) -> CuMin.Type -> a
foldType ff fe (CuMin.TFun s t) = ff s $ foldType ff fe t
foldType _ fe ty = fe ty

-- | Matches the given value against the list of case alternatives and evaluates it.
patternMatch :: NonDeterministic n => Value n -> [CuMin.Alt] -> Eval n (Value n)
patternMatch (VBot x) _ = return $ VBot x
patternMatch (VNat _) _ = error "cannot pattern match on Nat"
patternMatch (VFun _) _ = error "cannot pattern match on functions"
patternMatch con@(VCon cname args) alts = case List.find (matches cname) alts of
  Nothing -> return $ VBot "incomplete pattern match"
  Just (CuMin.Alt (CuMin.PVar v) body) -> withVars (M.singleton v con) $ eval body
  Just (CuMin.Alt (CuMin.PCon _ vs) body)
    | length vs == length args -> withVars (M.fromList $ zip vs args) $ eval body
    | otherwise -> error "number constructor arguments does not match the pattern"

-- | Checks if a pattern matches a constructor
matches :: CuMin.DataConName -> CuMin.Alt -> Bool
matches _ (CuMin.Alt (CuMin.PVar _) _) = True
matches cname (CuMin.Alt (CuMin.PCon pname _) _) = cname == pname

-- | Primitive equality operator which is built-in for naturals.
primEq :: Value n -> Value n -> Value n
primEq (VNat n) (VNat m) = toValue $ n == m
primEq (VBot n) (VNat _) = VBot n
primEq (VNat _) (VBot n) = VBot n
primEq (VBot n) (VBot _) = VBot n
primEq _ _ = error "primEq: wrong type"

-- | Primitive addition which is built-in for naturals.
primAdd :: Value n -> Value n -> Value n
primAdd (VNat n) (VNat m) = toValue $ n + m
primAdd (VBot n) (VNat _) = VBot n
primAdd (VNat _) (VBot n) = VBot n
primAdd (VBot n) (VBot _) = VBot n
primAdd _ _ = error "primAdd: wrong type"

-- | Function application lifted to values.
primApp :: NonDeterministic n => Value n -> Value n -> Eval n (Value n)
primApp (VFun f) a = lift $ f a
primApp (VBot n) _ = return $ VBot n
primApp _ _ = error "application of non-function type"
