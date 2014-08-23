{- | 
Implementation of the STLC in the paper.
-}

data UpTerm
  = Ann DownTerm Type -- Annotated term
  | Bound Int -- DeBruijn Index
  | Free Name 
  -- ^ Free Variable, usually refer to global entities
  -- using Strings
  | UpTerm :@: DownTerm -- Application
    deriving (Show, Eq)

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

-- | creates the value corresponding to a free var
vfree :: Name -> Value
vfree n = VNeutral (NFree n)
