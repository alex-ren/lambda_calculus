
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"


(* ************* ************* *)

datatype term = 
| TMvar of string
| TMlam of (string, term)
| TMapp of (term, term)

typedef path = List0 (int)
typedef pathlst = List0 (path)

#define :: list_cons
#define nil list_nil

// replace x with y
fun term_var_replace (t: term, x: string, y: string): term = let
  fun loop (t: term, x: string, y: string, u: &bool): term =
    case+ t of
    | TMvar v => if v = x then let
      val () = u := true
    in TMvar y end else let
      val () = u := false
    in t end
    | TMapp (t1, t2) => let
      var u1 = false: bool
      var u2 = false: bool
      val t1 = loop (t1, x, y, u1)
      val t2 = loop (t2, x, y, u2)
      val () = u := u1 || u2
    in
      if u then TMapp (t1, t2)
      else t
    end
    | TMlam (v, t1) => if v = x then let
      val () = u := false
    in t end else let
      val t1 = loop (t1, x, y, u)
    in
      if u = false then t else TMlam (v, t1)
    end

  var u = false: bool
in
  loop (t, x, y, u)
end


extern fun term_get_pathlst: term -> pathlst
 
// Implementation One
// implement term_get_pathlst (t) = 
// case+ t of
// | TMvar x => list_cons (list_nil, list_nil)
// | TMlam (x, t') => let
//   val paths = term_get_pathlst t'
//   implement list_foldright$fopr<path><pathlst>(
//     x, acc) = list_cons (list_cons (0, x), acc)
//   val paths' = list_foldright<path><pathlst> (paths, list_nil)
//   val res = list_cons (list_nil, paths')
// in
//   res
// end
// | TMapp (t1, t2) => let
//   val paths1 = term_get_pathlst t1
// 
//   implement list_foldright$fopr<path><pathlst>(
//     x, acc) = list_cons (list_cons (0, x), acc)
// 
//   val paths1' = list_foldright<path><pathlst> (paths1, list_nil)
// 
//   val paths2 = term_get_pathlst t2
//   implement list_foldright$fopr<path><pathlst>(
//     x, acc) = list_cons (list_cons (1, x), acc)
//   val paths2' = list_foldright<path><pathlst>(paths2, list_nil)
// 
//   val paths = (paths1' + paths2')
//   val res = list_cons (list_nil, paths)
// in
//   paths
// end

// Implementation two
implement term_get_pathlst (t) = let
  fun loop (t: term, route: path, accu: pathlst): pathlst = let
    val vp = list_reverse route
    val p = list_vt2t vp
    val accu = list_cons (p, accu)
  in
    case+ t of
    | TMvar x => accu
    | TMlam (x, t1) => loop (t1, list_cons (0, route), accu)
    | TMapp (t1, t2) => let
      val accu = loop (t1, list_cons (0, route), accu)
    in
      loop (t2, list_cons (1, route), accu)
    end
  end
in
  loop (t, list_nil, list_nil)
end

fun isLambda (t: term): bool = 
case+ t of
| TMlam _ => true
| _ => false

// Get the paths for all the redexes.
extern fun term_get_redexes: term -> pathlst
implement term_get_redexes (t) = let
  fun loop (t: term, route: path, accu: pathlst): pathlst =
    case+ t of
    | TMvar x => accu
    | TMlam (x, t1) => loop (t1, list_cons (0, route), accu)
    | TMapp (t1, t2) => let
      val accu = loop (t1, list_cons (0, route), accu)
      val accu = loop (t2, list_cons (1, route), accu)
    in
      if isLambda (t1) then let
        val vp = list_reverse route
        val p = list_vt2t vp
        val accu = list_cons (p, accu)
      in
        accu
      end else accu
    end
in
  loop (t, list_nil, list_nil)
end

// Get subterm according to the path.
fun subterm (t: term, p: path): term =
case+ t of
| TMvar x => t
| TMlam (x, t') => 
  (
  case- p of
  | list_cons (0, p') => subterm (t', p')
  | list_nil () => t
  )
| TMapp (t1, t2) =>
  (
  case- p of
  | list_cons (0, p') => subterm (t1, p')
  | list_cons (1, p') => subterm (t2, p')
  | list_nil () => t
  )

// Remove pre from p is pre is a prefix of p.
fun remove_prefix (pre: path, p: path): Option path =
case+ (pre, p) of
| (list_nil (), _) => option_some p
| (list_cons _, list_nil ()) => option_none<path> ()
| (list_cons (0, pre'), list_cons (0, p')) => remove_prefix (pre', p')
| (list_cons (1, pre'), list_cons (1, p')) => remove_prefix (pre', p')
| (_, _) => option_none<path> ()

// Get the paths for all the occurrance of free x0.
fun get_paths_with_free_x (t: term, x0: string): pathlst = let
  fun loop (t: term, route: path, accu: pathlst): pathlst = 
    case+ t of
    | TMvar x => if x = x0 then let
      val vp = list_reverse route
      val p = list_vt2t vp
      val accu = list_cons (p, accu)
    in
      accu
    end else accu
    | TMlam (x, t1) => loop (t1, list_cons (0, route), accu)
    | TMapp (t1, t2) => let
      val accu = loop (t1, list_cons (0, route), accu)
    in
      loop (t2, list_cons (1, route), accu)
    end
in
  loop (t, list_nil, list_nil)
end

extern fun term_get_residuals0 (t: term, p0: path (*redex*), p: path): pathlst

implement term_get_residuals0 (t, p0, p) = let
  val po = remove_prefix (p0, p)
in
  if option_is_none (po) then list_sing p
  else let
    val pa = option_unsome po
  in
    case- pa of
    | list_nil () => list_nil
    | list_cons (0, p') => list_sing (list_append (p0, p'))
    | list_cons (1, p') => let
      val- TMapp (TMlam (x, t1), _) = subterm (t, p0)
      val pxs = get_paths_with_free_x (t1, x)

      implement list_map$fopr<path><path> (x) = p0 + x + p'
      val residuals = list_map<path><path> pxs
      val residuals = list_vt2t residuals
    in
      residuals
    end
  end
end

fun term_get_residuals (t: term, redex: path, rs: pathlst): pathlst =  let
  implement list_foldright$fopr<path><pathlst>(
    p, acc) = list_append (term_get_residuals0 (t, redex, p), acc)
in
  list_foldright<path><pathlst> (rs, list_nil)
end


(* *********** *********** *)

fun print_pathlst (ps: pathlst): void = let
  implement print_list<path> (xs) =
  case+ xs of
  | x :: y :: xs => let
    val () = print! ("[", x, "] -> ")
  in
    print_list<path> (y :: xs)
  end
  | x :: nil () => print! ("[", x, "]")
  | nil () => ()
in
  print_list<path> ps
end

fun print_path (p: path): void = print_list<int> p

// Application is left-associative.
// Lambda has lowest precedence.
fun print_term (t: term): void = let
  // isleft: The current term is the left term of an application.
  fun print_term_impl (t: term, isleft: bool): void =
  case+ t of
  | TMvar x => print x
  | TMlam (x, t1) => (print ((if isleft then "(lam " else "lam "):string);
                      print x;
                      print ".";
                      print_term t1;
                      print ((if isleft then ")" else ""): string)
                      )
  | TMapp (t1, t2) => (print ((if isleft then "" else "("):string);
                       print_term_impl (t1, true);
                       print " ";
                       print_term_impl (t2, false);
                       print ((if isleft then "" else ")"):string);
                       )
in
  case+t of
  | TMvar x => print_term_impl (t, false)
  | TMlam (x, t1) => print_term_impl (t, false)
  | TMapp (t1, t2) => (print_term_impl (t1, true);
                       print " ";
                       print_term_impl (t2, false)
                       )
end

overload print with print_term

(* *********** *********** *)


implement main0 () = let
  // val () = println! (1, 2)
  // val p = (1 :: 2 :: 3 :: nil): path
  // val ps = (p :: p :: nil): pathlst
  // val () = print_path p
  // val () = println! ()

  // val () = print_pathlst ps
  // val () = println! ()

  // x
  val t_x = TMvar "x"

  // y
  val t_y = TMvar "y"

  // lam x.x
  val t1 = TMlam ("x", t_x)
  val () = println! ("t1 is ", t1)

  // (lam x.x) x y
  val t2 = TMapp (TMapp (t1, t_x), t_y)
  val () = println! ("t2 is ", t2)

  // (lam x.x) (x y)
  val t3 = TMapp (t1, TMapp (t_x, t_y))
  val () = println! ("t3 is ", t3)

  // x lam x.x y
  val t4 = TMlam ("x", TMapp (t_x, t_y))
  val t5 = TMapp (t_x, t4)
  val () = println! ("t5 is ", t5)

  val ps1 = term_get_pathlst (t1)
  val () = print "pathlst of t1 is "
  val () = print_pathlst ps1
  val () = print_newline ()
in end


%{
#include <fnmatch.h>
%}




