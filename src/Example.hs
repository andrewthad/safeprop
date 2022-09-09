{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-termination" @-}

-- We statically verify that function-call arity is correct and that
-- unbound variables are not referenced. We deliberately do not attempt
-- to do typechecking statically. Once user-defined types are in play,
-- it is not practical to do that.
--
-- At the moment, the argument to Apply must have arity 0. That is,
-- we cannot apply a lambda to another lambda. It might be possible
-- to lift this restriction.
module Example where

data Term
  = And Term Term
  | Lambda Term
  | Apply Term Term -- argument must not be lambda
  | All Term Term
  | Truth
  | Integer Integer
  | Plus Term Term
  | Var Int -- must not refer to a lambda
  deriving (Show)

-- How many arguments does this term need to be applied to
{-@ measure arity @-}
arity :: Term -> Int
arity (And _ _) = 0
arity (Lambda x) = arity x + 1
arity (Apply f _) = arity f - 1
arity (All _ _) = 0
arity Truth = 0
arity (Integer _) = 0
arity (Plus _ _) = 0
arity (Var _) = 0

{-@ measure wellFormed @-}
wellFormed :: Term -> Bool
wellFormed (And a b) = freeVarBound a >= 0 && freeVarBound b >= 0 && arity a == 0 && arity b == 0 && wellFormed a && wellFormed b
wellFormed (Lambda x) = wellFormed x && freeVarBound x >= 0
wellFormed (Apply f x) = arity x == 0 && arity f > 0 && wellFormed x && wellFormed f && freeVarBound f >= 0 && freeVarBound x >= 0
wellFormed (All f x) = arity x == 0 && arity f > 0 && wellFormed x && wellFormed f && freeVarBound f >= 0 && freeVarBound x >= 0
wellFormed Truth = True
wellFormed (Integer _) = True
wellFormed (Plus a b) = freeVarBound a >= 0 && freeVarBound b >= 0 && arity a == 0 && arity b == 0 && wellFormed a && wellFormed b
wellFormed (Var i) = i >= 0

{-@ measure freeVarBound @-}
freeVarBound :: Term -> Int
freeVarBound (And a b) = if freeVarBound a > freeVarBound b then freeVarBound a else freeVarBound b
freeVarBound (Lambda body) = if freeVarBound body == 0 then 0 else freeVarBound body - 1
freeVarBound (Apply f x) = if freeVarBound f > freeVarBound x then freeVarBound f else freeVarBound x
freeVarBound (All f x) = if freeVarBound f > freeVarBound x then freeVarBound f else freeVarBound x
freeVarBound Truth = 0
freeVarBound (Integer _) = 0
freeVarBound (Plus a b) = if freeVarBound a > freeVarBound b then freeVarBound a else freeVarBound b
freeVarBound (Var i) = i + 1

{-@ exA :: {t : Term | wellFormed t && freeVarBound t = 0 && arity t = 0} @-}
exA :: Term
exA = Apply (Lambda (Plus (Integer 42) (Var 0))) (Integer 55)

{-@ exB :: {t : Term | wellFormed t && freeVarBound t = 0 && arity t = 0} @-}
exB :: Term
exB = Apply (Apply (Lambda (Lambda (Plus (Var 0) (Var 1)))) (Integer 97)) (Integer 42)

data Context
  = ContextCons Term Context
  | ContextConsOpaque Context
  | ContextNil

{-@ measure contextSize @-}
contextSize :: Context -> Int
contextSize ContextNil = 0
contextSize (ContextCons _ c) = 1 + contextSize c
contextSize (ContextConsOpaque c) = 1 + contextSize c

{-@ measure allWellFormed @-}
allWellFormed :: Context -> Bool
allWellFormed ContextNil = True
allWellFormed (ContextCons t c) = wellFormed t && freeVarBound t >= 0 && freeVarBound t <= contextSize c && arity t == 0 && allWellFormed c
allWellFormed (ContextConsOpaque c) = allWellFormed c

size :: Term -> Int
size (And a b) = 1 + size a + size b
size (Plus a b) = 1 + size a + size b
size (Apply a b) = 1 + size a + size b
size (All a b) = 1 + size a + size b
size (Lambda a) = 1 + size a
size Truth = 1
size Integer{} = 1
size Var{} = 1

{-@ fullEval ::
     {t : Term | wellFormed t && freeVarBound t >= 0 && freeVarBound t <= 0 } ->
     {r : Term | wellFormed r && freeVarBound r >= 0 && freeVarBound r <= 0 && arity r = arity t}
@-}
fullEval :: Term -> Term
fullEval a =
  let b = evaluate 0 a
   in if size b < size a then fullEval b else a

{-@ evaluate ::
     {ctx : Int | ctx >= 0} ->
     {t : Term | wellFormed t && freeVarBound t >= 0 && freeVarBound t <= ctx } ->
     {r : Term | wellFormed r && freeVarBound r >= 0 && freeVarBound r <= ctx && arity r = arity t}
@-}
evaluate :: Int -> Term -> Term
evaluate ctx (Apply lam arg) = case lam of
  Lambda body -> evaluate ctx (substitute 0 (ctx + 1) arg body)
  _ -> Apply (evaluate ctx lam) (evaluate ctx arg)
evaluate ctx (All lam arg) = All (evaluate ctx lam) (evaluate ctx arg)
evaluate _ (Var v) = Var v
evaluate ctx (Lambda body) = Lambda (evaluate (ctx + 1) body)
evaluate ctx (And a b) = And (evaluate ctx a) (evaluate ctx b)
evaluate ctx (Plus a b) = case a of
  Integer a' -> case b of
    Integer b' -> Integer (a' + b')
    _ -> Plus (evaluate ctx a) (evaluate ctx b)
  _ -> Plus (evaluate ctx a) (evaluate ctx b)
evaluate _ Truth = Truth
evaluate _ (Integer i) = Integer i

{-@ lookupVar :: {ctx : Context | allWellFormed ctx } -> {v : Int | v >=0 && v < contextSize ctx} -> Maybe {r : Term | wellFormed r && freeVarBound r >= 0 && freeVarBound r <= contextSize ctx && arity r = 0 } @-}
lookupVar :: Context -> Int -> Maybe Term
lookupVar (ContextCons t ctx) i = if i == 0 then Just t else lookupVar ctx (i - 1)
lookupVar (ContextConsOpaque ctx) i = if i == 0 then Nothing else lookupVar ctx (i - 1)
lookupVar ContextNil _ = error "lookupVar: impossible"

{-@ substitute ::
     {var : Int | var >= 0} ->
     {ctx : Int | ctx >= 1 && var < ctx} ->
     {content : Term | wellFormed content && arity content = 0 && freeVarBound content >= 0 && freeVarBound content < ctx - var } ->
     {haystack : Term | wellFormed haystack && freeVarBound haystack >= 0 && freeVarBound haystack <= ctx } ->
     {out : Term | wellFormed out && arity out = arity haystack && freeVarBound out >= 0 && freeVarBound out < ctx }
@-}
substitute :: Int -> Int -> Term -> Term -> Term
substitute var ctx content haystack = case haystack of
  Var i -> if i == var
    then incrVars 0 var content
    else if i > var
      then Var (i - 1)
      else Var i
  And a b -> And (substitute var ctx content a) (substitute var ctx content b)
  Plus a b -> Plus (substitute var ctx content a) (substitute var ctx content b)
  Truth -> Truth
  Integer i -> Integer i
  Lambda body -> Lambda (substitute (var + 1) (ctx + 1) content body)
  Apply f x -> Apply (substitute var ctx content f) (substitute var ctx content x)
  All f x -> All (substitute var ctx content f) (substitute var ctx content x)

{-@ incrVars ::
     {cutoff : Int | cutoff >= 0} ->
     {n : Int | n >= 0} ->
     {t : Term | wellFormed t && freeVarBound t >= 0 } ->
     {r : Term | wellFormed r && freeVarBound r >= 0 && freeVarBound r <= freeVarBound t + n && arity r = arity t }
@-}
incrVars :: Int -> Int -> Term -> Term
incrVars cutoff n t = case t of
  Var i -> if i < cutoff then Var i else Var (i + n)
  And a b -> And (incrVars cutoff n a) (incrVars cutoff n b)
  Plus a b -> Plus (incrVars cutoff n a) (incrVars cutoff n b)
  Lambda a -> Lambda (incrVars (cutoff + 1) n a)
  Integer i -> Integer i
  Truth -> Truth
  Apply f x -> Apply (incrVars cutoff n f) (incrVars cutoff n x)
  All f x -> All (incrVars cutoff n f) (incrVars cutoff n x)

{-@ example :: {t : Term | wellFormed t && freeVarBound t = 0 && arity t = 0 } @-}
example :: Term
example = Apply (Apply (Lambda (Lambda (Plus (Var 0) (Var 1)))) (Integer 5)) (Integer 42)
