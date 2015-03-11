-- Lambda.hs
-- Lambda calculus evaluator

module Lambda (
  Lambda(..),
  eval
) where

data Lambda =
    Var String
  | Abs String Lambda
  | App Lambda Lambda
  deriving (Eq)

instance Show Lambda where
  show (Var var) = var
  show (Abs var body) = "(\\" ++ var ++ ". " ++ (show body) ++ ")"
  show (App expr1 expr2) = (show expr1) ++ " " ++ (show expr2)

-- alpha renaming
-- rename bound variables only
rename :: String -> String -> Lambda -> Lambda
rename old new l  = rn_bound old new l []
  where rn_bound old new (Var var) bound =
          if var `elem` bound && var == old then
            Var new
          else
            Var var
        rn_bound old new (Abs var body) bound =
          if var == old then
            Abs new (rn_bound old new body (var:bound))
          else
            Abs var (rn_bound old new body (var:bound))
        rn_bound old new (App expr1 expr2) bound =
          App (rn_bound old new expr1 bound) (rn_bound old new expr2 bound)


-- get a list of bound variables for an expr
bound_vars :: Lambda -> [String]
bound_vars (Var _) = []
bound_vars (Abs var body) = var:(bound_vars body)
bound_vars (App expr1 expr2) = (bound_vars expr1) ++ (bound_vars expr2)

-- helper for alpha renaming: generate a fresh variable
-- name that is not bound
get_unbound_name :: String -> [String] -> String
get_unbound_name var bound =
  case var `elem` bound of 
  True -> get_unbound_name (var ++ "#") bound
  False -> var

-- rename vars in expr to prevent capture
rename_vars :: [String] -> Lambda -> Lambda
rename_vars bound expr = foldr rename_var expr (bound_vars expr)
  where rename_var var acc =
          if var `elem` bound then
            rename var (get_unbound_name var bound) acc
          else
            acc

-- do substitution for beta reduction
apply :: Lambda -> String -> Lambda -> Lambda
apply arg param (Var var) =
  if param == var then arg else Var var
apply arg param (Abs var expr) =
  Abs var (apply arg param expr)
apply arg param (App expr1 expr2) =
  App (apply arg param expr1) (apply arg param expr2)

-- reduce a lambda expression
eval :: Lambda -> Lambda
-- redex exists!
eval orig@(App (Abs param body) arg) =
  -- if new expr is the same as the old, there is no more to eval
  -- if this check does not exist, exprs like (\y.y) (\y.y) won't terminate
  -- do alpha renaming before substitution to prevent variable name conflict
  if orig == next then orig else next
  where renamed_arg = rename_vars (bound_vars body) arg
        next        = apply renamed_arg param body
-- not a redex; nothing else to evaluate
eval l = l


