-- Lambda.hs
-- Lambda calculus evaluator

module Lambda (
  Lambda(..),
  eval, eval_normal, eval_by_name
) where

import Data.List
import Debug.Trace

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


-- get a list of variables for an expr
get_vars :: Lambda -> [String]
get_vars expr = nub $ collect_vars expr
  where collect_vars (Var var)         = [var]
        collect_vars (Abs var body)    = [var] ++ (collect_vars body)
        collect_vars (App expr1 expr2) = (collect_vars expr1) ++ (collect_vars expr2)

-- get a list of bound variables for an expr
bound_vars :: Lambda -> [String]
bound_vars expr = nub $ collect_vars expr
  where collect_vars (Var _)           = []
        collect_vars (Abs var body)    = var:(collect_vars body)
        collect_vars (App expr1 expr2) = (collect_vars expr1) ++ (collect_vars expr2)

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

-- check if an expression has a beta-redex
-- this is a helper function for evaluation
has_redex :: Lambda -> Bool
has_redex (Var _) = False
has_redex (Abs _ body) = has_redex body
-- this is a redex!
has_redex (App (Abs _ _) _) = True
has_redex (App expr1 expr2) = (has_redex expr1) || (has_redex expr2)

-- beta-reduce a redex
-- this doesn't do anything if the arg is not a redex!
reduce :: Lambda -> Lambda
reduce expr@(App (Abs param body) arg) = if expr == next then expr else next
  where renamed_body = rename_vars (get_vars arg) body
        next         = apply arg param renamed_body
reduce expr = expr

-- reduce a lambda expression
-- using normal order strategy
eval_normal :: Lambda -> Lambda
eval_normal expr@(Var _) = expr
eval_normal expr@(Abs var body) = Abs var (eval_normal body)
-- a redex!
eval_normal expr@(App (Abs _ _) _) =
  let next = reduce expr in
  if has_redex next then
    eval_normal next
  else
    next
-- eval the outermost and leftmost redex first
-- this means to eval expr1 first, then expr2
eval_normal expr@(App expr1 expr2) =
  if has_redex expr1 then
    eval_normal (App (eval_normal expr1) expr2)
  else
    if has_redex expr2 then
      eval_normal (App expr1 (eval_normal expr2))
    -- no redexes; stop eval
    else
      expr

-- reduce a lambda expression
-- using call-by-name (lazy) strategy
-- this is almost the same as normal order,
-- except redexes inside abstractions aren't reduced
eval_by_name :: Lambda -> Lambda
eval_by_name expr@(Var _) = expr
-- don't eval redexes inside abstractions!
eval_by_name expr@(Abs _ _) = expr
-- a redex!
eval_by_name expr@(App (Abs _ _) _) =
  let next = reduce expr in
  if has_redex next then
    eval_by_name next
  else
    next
-- eval the outermost and leftmost redex first
-- this means to eval expr1 first, then expr2
eval_by_name expr@(App expr1 expr2) =
  if has_redex expr1 then
    eval_by_name (App (eval_by_name expr1) expr2)
  else
    if has_redex expr2 then
      eval_by_name (App expr1 (eval_by_name expr2))
    -- no redexes; stop eval
    else
      expr

eval = eval_by_name
