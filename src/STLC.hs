{- | 
Implementation of the STLC in the paper.
-}

import Control.Monad
import Control.Monad.Trans.Either
import Control.Monad.Trans

-- Abstract Syntax

infixl 0 :@:

-- | Inferable Term
data UpTerm
  = Ann DownTerm Type -- Annotated term
  | Bound Int -- DeBruijn Index
  | Free Name 
  -- ^ Free Variable, usually refer to global entities using Strings
  | UpTerm :@: DownTerm -- Application
    deriving (Show, Eq)

-- | Checkable Term
data DownTerm
  = Inf UpTerm
  -- ^ Inferable terms
  | Lam DownTerm
  -- ^ Lambdas (De Bruijn)
    deriving (Show, Eq)

data Name
  = Global String
  -- ^ Normal global entity
  | Local Int
  -- ^ Convert a bound variable into a free variable temporarily
  | Quote Int
  -- ^ For use during quoting
    deriving (Show, Eq)

data Type
  = TFree Name
  -- ^ Type Identifiers
  | Fun Type Type
  -- ^ Function Arrows
    deriving (Show, Eq)

data Value 
  = VLam (Value -> Value)
  -- ^ HOAS Lambda abstraction
  | VNeutral Neutral
  -- ^ Neutral term

data Neutral
  = NFree Name
  -- ^ Neutral Variable
  | NApp Neutral Value
  -- ^ Application of a neutral term to a value

-- | Creates the value corresponding to a free var
vfree :: Name -> Value
vfree = VNeutral . NFree

-- Evaluation

-- | Environment of Values
-- The i'th position corresponds to the value of variable i
-- (De Bruijn Index i)
type Env = [Value]

-- | Big-step evaluation rules for inferable terms
upEval :: UpTerm -> Env -> Value
upEval (Ann e _)  d = downEval e d
-- ^ Evaluate e with current environment
upEval (Free x)   d = vfree x
-- ^ Free variable
upEval (Bound i)  d = d !! i
-- ^ De bruijn _indices_
upEval (e :@: e') d = vapp (upEval e d) (downEval e' d)
-- ^ Evaluate e and e', and perform application e e'

-- | Value application
vapp :: Value -> Value -> Value
vapp (VLam f) v     = f v
-- ^ Simple application
vapp (VNeutral n) v = VNeutral (NApp n v)
-- ^ NB. This is where Molecule failed! n might be a function.

-- | Big-step evaluation rules for checkable terms
--   Lambdas modify the environment!
downEval :: DownTerm -> Env -> Value
downEval (Inf i) d = upEval i d
-- ^ Propagate type checking to upEval, since value is inferable.
downEval (Lam e) d = VLam $ \x -> downEval e (x : d)
-- ^ HOAS; evaluate e with modified environment

-- Contexts

data Kind = Star
  deriving Show

data Info 
  = HasKind Kind
  | HasType Type
    deriving Show

-- | Context associates names with either
-- HasKind Star (*) or a HasType t (type)
type Context = [(Name, Info)]

-- Type Checking

-- @TODO: Annotate

-- | Result of typechecking
type Result a = Either String a

-- Report an error
throwError :: String -> Result a
throwError = Left

-- Check for the well-formedness of a type
downKind :: Context -> Type -> Kind -> Result ()
downKind ctx (TFree x) Star
   = case lookup x ctx of
      Just (HasKind Star) -> return ()
      Nothing             -> throwError "unknown identifier"

downKind ctx (Fun k k') Star = do
  downKind ctx k  Star
  downKind ctx k' Star

-- Start at 0 and typecheck an inferable variable
-- 0 is the number of binders we've encountered
upTypeZero :: Context -> UpTerm -> Result Type
upTypeZero = upType 0

-- | Check the type of an inferable variable
upType :: Int -> Context -> UpTerm -> Result Type
-- Corresponds to ANN (figure 3) in paper
upType i ctx (Ann e t) = do
  downKind ctx t Star
  downType i ctx e t
  return t

-- var (figure 3)
upType i ctx (Free x) = case lookup x ctx of
  Just (HasType t) -> return t
  Nothing          -> throwError "unknown identifier"

-- APP (figure 3)
upType i ctx (e :@: e') = do
  sigma <- upType i ctx e
  case sigma of 
    Fun t t' -> downType i ctx e' t >> return t
    _        -> throwError "illegal application"

-- | Check the type of a checkable term.
downType :: Int -> Context -> DownTerm -> Type -> Result ()
-- CHK (figure 3)
downType i ctx (Inf e) t = do
  t' <- upType i ctx e
  unless (t == t') (throwError "type mismatch")

-- LAM (figure 3)
downType i ctx (Lam e) (Fun t t') = 
  downType (i + 1)
           -- ^ We have a new binder
           ((Local i, HasType t) : ctx)
           -- ^ Add i with type t to the context
           (downSubst 0 (Free (Local i)) e) 
           -- ^ Substitute 0 for Local i in e
           t'

downType i ctx _ _ = throwError "type mismatch"

-- i corrsponds to which term is to be substituted

-- | Variable substitution for inferable terms
upSubst :: Int -> UpTerm -> UpTerm -> UpTerm
upSubst i r (Ann e t) = Ann (downSubst i r e) t
upSubst i r (Bound j) = if i == j then r else Bound j
upSubst i r (Free y)  = Free y
upSubst i r (e :@: e') = upSubst i r e :@: downSubst i r e'

-- | Variable substitution for checkable terms
downSubst :: Int -> UpTerm -> DownTerm -> DownTerm
downSubst i r (Inf e) = Inf (upSubst i r e)
downSubst i r (Lam e) = Lam (downSubst (i + 1) r e)

-- Quotation

-- Again, 0 is the number of binders traversed.
quoteZero :: Value -> DownTerm
quoteZero = quote 0

-- i is the number of binders traversed.
-- | Get the internal structure of a value, for instance to
--   display it.
quote :: Int -> Value -> DownTerm
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
-- ^ Generate a fresh variable Quote i and apply f to it.
--   Then, go a level deeper and evaluate the rest.
quote i (VNeutral n) = Inf (neutralQuote i n)
-- ^ Propagate to neutralQuote (application of a free variable
--   to other values)

-- | Quote a neutral value
neutralQuote :: Int -> Neutral -> UpTerm
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

-- | Check if the variable occuring at the head of the application is bound or free
boundfree :: Int -> Name -> UpTerm
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x

{-
Extended example of quoting, given:
Const = VLam (\x -> VLam (\y -> x))
  quote 0 (VLam (\x -> VLam (\y -> x))) -- quoteZero
= Lam (quote 1 (VLam (\y -> vfree (Quote 0)))) -- quote
= Lam (Lam (quote 2 (vfree (Quote 0)))) -- quote
= Lam (Lam (neutralQuote 2 (NFree (Quote 0)))) -- quote
= Lam (Lam (Bound 1)) -- neutralQuote
= λ λ 1 (in de bruijn indixes)
= λx. λy. x (normal notation)
-}

-- Example terms

id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))
tfree a = TFree (Global a)
free x = Inf (Free (Global x))
term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"
term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                        (Fun (tfree "a")
                             (Fun (tfree "b") (tfree "b"))))
        :@: id' :@: free "y"
env1 = [(Global "y", HasType (tfree "b")),
        (Global "a", HasKind Star)]
env2 = (Global "b", HasKind Star) : env1
