
(* val ( $ ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b = <fun> *)
let ($) g x = g (x)

module StringSet = Set.Make(String)
type env = StringSet.t
let empty_env = StringSet.empty
let push_id = StringSet.add
let push_id_list l env = List.fold_left (fun env id -> push_id id env) env l

let verif = ref true

let verify_id id env =
  if !verif && not (StringSet.mem id env) then
    raise (Invalid_argument (Format.asprintf "Identifier %s not found in current context" id))

let identity x = x
let ismt = String.equal ""

let mt = Format.dprintf ""
let spc = Format.dprintf " "

let map_or_mt f = function
  | Some x -> f x
  | None -> mt

let get_or_mt = map_or_mt identity

let fnl = Format.dprintf "@\n"
let fnl2 = Format.dprintf "@\n@\n"

let of_int = Format.dprintf "%d"
let of_float = Format.dprintf "%f"
let of_bool = Format.dprintf "%b"

let str = Format.dprintf "%s"
let pat = Format.dprintf "%t"

let par_str = Format.dprintf "(%s)"
let par_pat = Format.dprintf "(%t)"
let brak_str = Format.dprintf "[%s]"
let brak_pat = Format.dprintf "[%t]"
let curly_str = Format.dprintf "{%s}"
let curly_pat = Format.dprintf "{%t}"

let par_if_not_mt l pp =
  match l with
  | [] -> mt
  | _ -> par_pat pp

let concat_sep sep f l =
  let rec aux = function
    | [] -> mt
    | [x] -> str (f x)
    | x :: xs -> Format.dprintf "%s%s%t" (f x) sep (aux xs)
  in
  aux l

let concat_sep_pp sep f l =
  let rec aux = function
    | [] -> mt
    | [x] -> pat (f x)
    | x :: xs -> Format.dprintf "%t%t%t" (f x) sep (aux xs)
  in
  aux l

let concat_map_comma_pp f l = concat_sep_pp (Format.dprintf ", ") f l
let concat_map_comma f l = concat_sep ", " f l
let concat_comma_pp l = concat_map_comma_pp identity l
let concat_comma l = concat_map_comma identity l

let combine_sep sep l =
  let rec fold i acc = function
  | [] -> acc
  | x :: xs ->
      fold (i + 1)
      (if i = 0 then Format.dprintf "%t" x
        else Format.dprintf "%t%t%t" acc sep x)
      xs
  in
  fold 0 mt l

let combine_ln l = combine_sep (Format.dprintf "@\n") l
