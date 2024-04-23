
open Format
open Print_terms
open Utils

let enable_verification () = verif := true
let disable_verification () = verif := false

let get_block ?(env = empty_env) stmts : string =
  asprintf "@[<v>%t@]" (of_block ~env stmts)

let print_block ?(env = empty_env) stmts =
  printf "@[<v>%t@]@." (of_block ~env stmts)

let print_stmt ?(env = empty_env) stmt =
  printf "@[<v>%t@]@." (fst $ of_stmt ~env stmt)

let print_expr ?(env = empty_env) expr =
  printf "@[<v>%t@]@." (fst $ of_expr ~env expr)

let combine_sep = Utils.combine_sep

let combine_ln = Utils.combine_ln

let print ft = printf "@[<v>%t@]" ft; print_flush ();;
let println ft = printf "@[<v>%t@]@." ft; print_flush ();;
let brkln () = printf "@\n";;
let brkln2 () = brkln (); brkln ();;

let print_combine l = print (combine_ln l)
let println_combine l = println (combine_ln l)
