
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

datatype term = 
| TMvar of string
| TMlam of (string, term)
| TMapp of (term, term)

typedef path = List0 (int)
typedef pathlst = List0 (path)

extern fun term_get_pathlst: term -> pathlst

implement term_get_pathlst (t) = 
case+ t of
| TMvar x => list_cons (list_nil, list_nil)
| TMlam (x, t') => let
  val paths = term_get_pathlst t'
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (0, x), acc)
  val paths' = list_foldright (paths, list_nil)
  val res = list_cons (list_nil, paths')
in
  res
end
| TMapp (t1, t2) => let
  val paths1 = term_get_pathlst t1
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (0, x), acc)
  val paths1' = list_foldright (paths1, list_nil)

  val paths2 = term_get_pathlst t2
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (1, x), acc)
  val paths2' = list_foldright (paths2, list_nil)

  val paths = list_append (paths1', paths2')
  // val paths = (paths1' + paths2'): pathlst
  val res = list_cons (list_nil, paths)
in
  paths
end

fun isLambda (t: term): bool = 
case+ t of
| TMlam _ => true
| _ => false

extern fun term_get_redexes: term -> pathlst
implement term_get_redexes (t) =
case+ t of
| TMvar x => list_nil
| TMlam (x, t') => let
  val paths = term_get_redexes t'
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (0, x), acc)
  val paths' = list_foldright (paths, list_nil)
in
  paths'
end
| TMapp (t1, t2) => let
  val paths1 = term_get_redexes t1
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (0, x), acc)
  val paths1' = list_foldright (paths1, list_nil)

  val paths2 = term_get_redexes t2
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (1, x), acc)
  val paths2' = list_foldright (paths2, list_nil)

  val paths = list_append (paths1', paths2')
in
  if isLambda t1 then list_cons (list_nil, paths)
  else paths
end

fun subterm (t: term, p: path): term =
case+ t of
| TMvar x => t
| TMlam (x, t') => 
  (
  case p of
  | list_cons (0, p') => subterm (t', p')
  | list_nil () => t
  )
| TMapp (t1, t2) =>
  (
  case p of
  | list_cons (0, p') => subterm (t1, p')
  | list_cons (1, p') => subterm (t2, p')
  | list_nil () => t
  )

fun remove_prefix (pre: path, p: path): Option path =
case+ (pre, p) of
| (list_nil (), _) => option_some p
| (list_cons _, list_nil ()) => option_none<path> ()
| (list_cons (0, pre'), list_cons (0, p')) => remove_prefix (pre', p')
| (list_cons (1, pre'), list_cons (1, p')) => remove_prefix (pre', p')
| (_, _) => option_none<path> ()

fun get_paths_with_free_x (t: term, x0: string): pathlst = 
case+ t of
| TMvar x => if x = x0 then list_cons (list_nil, list_nil)
             else list_nil
| TMlam (x, t') => if x = x0 then list_nil
  else let
    val paths = get_paths_with_free_x (t', x0)
    implement list_foldright$fopr<path><pathlst>(
      x, acc) = list_cons (list_cons (0, x), acc)
    val paths' = list_foldright (paths, list_nil)
    val res = list_cons (list_nil, paths')
  in
    res
  end
| TMapp (t1, t2) => let
  val paths1 = get_paths_with_free_x (t1, x0)
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (0, x), acc)
  val paths1' = list_foldright (paths1, list_nil)

  val paths2 = get_paths_with_free_x (t2, x0)
  implement list_foldright$fopr<path><pathlst>(
    x, acc) = list_cons (list_cons (1, x), acc)
  val paths2' = list_foldright (paths2, list_nil)

  val paths = list_append (paths1', paths2')
  val res = list_cons (list_nil, paths)
in
  res
end

                    
extern fun term_get_residuals0 (t: term, p0: path (*redex*), p: path): pathlst

implement term_get_residuals0 (t, p0, p) = let
  val po = remove_prefix (p0, p)
in
  if option_is_none (po) then list_sing p
  else let
    val pa = option_unsome po
  in
    case pa of
    | list_nil () => list_nil
    | list_cons (0, p') => list_sing (list_append (p0, p'))
    | list_cons (1, p') => let
      val- TMapp (TMlam (x, t1), _) = subterm (t, p0)
      val pxs = get_paths_with_free_x (t1, x)

      implement list_foldright$fopr<path><pathlst>(
        px, acc) = list_cons (list_append (p0, list_append (px, p')), acc)
      val residuals = list_foldright (pxs, list_nil)
    in
      residuals
    end
  end
end

fun term_get_residuals (t: term, redex: path, rs: pathlst): pathlst =  let
  implement list_foldright$fopr<path><pathlst>(
    p, acc) = list_append (term_get_residuals0 (t, redex, p), acc)
in
  list_foldright (rs, list_nil)
end





