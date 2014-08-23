{- | 
Implementation of the STLC in the paper.
-}

-- Abstract Syntax

-- | Inferable Term
data UpTerm
  = Ann DownTerm Type -- Annotated term
  | Bound Int -- DeBruijn Index
  | Free Name 
  -- ^ Free Variable, usually refer to global entities
  -- using Strings
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
upEval (Free x)   d = vfree x
upEval (Bound i)  d = d !! i
upEval (e :@: e') d = vapp (upEval e d) (downEval e' d)

-- | Value application
vapp :: Value -> Value -> Value
vapp (VLam f) v     = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

-- | Big-step evaluation rules for checkable terms
--   Lambdas modify the environment!
downEval :: DownTerm -> Env -> Value
downEval (Inf i) d = upEval i d
downEval (Lam e) d = VLam $ \x -> downEval e (x : d)

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
