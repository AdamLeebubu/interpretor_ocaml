(* Honor code comes here:

   First Name: Jida
   Last Name: Li
   BU ID: U97480525

   I pledge that this program represents my own program code and that I have
   coded on my own. I received help from no one in designing and debugging my
   program. I have read the course syllabus of CS 320 and have read the sections
   on Collaboration and Academic Misconduct. I also understand that I may be
   asked to meet the instructor or the TF for a follow up interview on Zoom. I
   may be asked to explain my solution in person and may also ask you to solve a
   related problem. *)

(*NOTE: There are no restrictions on what you can use*)

(******************************************************************************)
let (%) (f : 'a -> 'output) (g : 'input -> 'a): 'input -> 'output = fun x -> f (g x)
let rec fold_left (f : 'a -> 'b -> 'a) (acc : 'a) (ls : 'b list): 'a = match ls with | [] -> acc | hd::rest -> fold_left f (f acc hd) rest
let length ls = fold_left (fun acc _ -> acc+1) 0 ls
let flip (f : 'a -> 'b -> 'c): 'b -> 'a -> 'c = fun a b -> f b a
let cons (hd : 'a) (tl : 'a list): 'a list = hd :: tl
let reverse (ls : 'a list): 'a list = fold_left (flip cons) [] ls
let map_fst (f : 'a -> 'c) ((a, b) : 'a * 'b): 'c * 'b = (f a, b) 
(******************************************************************************)

type token =
  | SYMBOL of string
  | NUMBER of int
  | STRING of string
  | GLOBAL of string
  | LOCAL of string
  | VAR of string
  | LPAREN
  | RPAREN
  | BEGIN
  | END
  | IFTHEN
  | ELSE
  | CASELEFT
  | RIGHT
  | FUN of string * string
  | MUT of string * string
  | MUTL of string * string
  | TUPLE of int
  | GET of int
  | EOF

type atom = | Number of int | String of string | Var of string
            | Symbol of string | LVariable of string | GVariable of string 
            | BeginEnd of token list 
            | IfThen of token | Else of token 
(******************************************************************************)
type stack_err = | EmptyStackError | InvalidGrammar

type 'a stack = Empty | Entry of 'a * 'a stack
(******************************************************************************)
type 'a env = | Entry of 'a * ('a env) | Empty

type sexpr =
  | Atom of atom
  | BeginEnd of sexpr_list
  | IfThenElse of sexpr * sexpr
  | IfThen of sexpr_list
  | Else of sexpr_list
  | Case of sexpr * sexpr
  | Left of sexpr_list
  | Right of sexpr_list
  | Tuple of int
  | Get of int
  | Fun of sexpr_list
  | Mut of sexpr_list
  | Header of string * string
and sexpr_list = sexpr list

type func = string * string * sexpr list

type value = Int of int | String of string
            | UnionL of value | UnionR of value
            | Tuple of value list
            | Clo of string * string * sexpr list * (string*value) env * func list
(******************************************************************************)
let slist (l : sexpr_list): sexpr = BeginEnd(l)
let sifthen (l : sexpr_list): sexpr = IfThen(l)
let selse (l : sexpr_list): sexpr = Else(l)
let sifthenelse (l1 : sexpr)(l2 : sexpr): sexpr = IfThenElse(l1,l2)
let sleft (l : sexpr_list): sexpr = Left(l)
let sright (l : sexpr_list): sexpr = Right(l)
let scase (l1 : sexpr)(l2 : sexpr): sexpr = Case(l1,l2)
let sfun (fn: string)(var:string)(l: sexpr_list): sexpr= Fun((Header(fn, var))::l)
let smut (fn: string)(var:string)(l: sexpr_list): sexpr= Mut((Header(fn, var))::l)
let snumber (n : int)   : sexpr = Atom(Number(n))
let ssymbol (s : string): sexpr = Atom(Symbol(s))
let sstr (s : string): sexpr = Atom(String(s))
let svarl (s : string): sexpr = Atom(LVariable(s))
let svarg (s : string): sexpr = Atom(GVariable(s))
let svar (s : string): sexpr = Atom(Var(s))
let sbeginend (ts: token list): sexpr = Atom(BeginEnd(ts))
let stuple (n: int): sexpr = Tuple(n)
let sget (n: int): sexpr = Get(n)
(******************************************************************************)
type 'a str =
  | Next of 'a * 'a stream
and 'a stream = unit -> 'a str
let head (st : 'a stream): 'a = let Next(h, _) = st () in h
let tail (st : 'a stream): 'a stream = let Next(_, t) = st () in t
let (^) (a : token) (st : token stream): token stream = fun _ -> Next(a, st)
let rec eof (_ : unit): token stream = fun _ -> Next(EOF, eof ())
(************************************************************)
type ('a, 'e) result = | Ok of 'a | Err of 'e
let ok  (res : 'a): ('a, 'e) result = Ok(res)
let err (err : 'e): ('a, 'e) result = Err(err)
let fold_result (f : 'a -> 'b) (g : 'e -> 'b) (res : ('a, 'e) result): 'b = match res with Ok(o) -> f o | Err(e) -> g e
let map_ok (f : 'a -> 'b) (res : ('a, 'e) result): ('b, 'e) result = fold_result (ok % f) err res 
let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result = fold_result f err res
(************************************************************)
let is_digit c = if c>='0' && c<='9' then true else false
let is_int s =
  if String.get s 0 = '-' then String.fold_left (fun acc c -> if is_digit c then acc else false) true (String.sub s 1 ((String.length s)-2))
  else String.fold_left (fun acc c -> if is_digit c then acc else false) true s
let is_char c = if (c>='a' && c<='z') || (c>='A' && c<='Z') then true else false
let is_string s =
  if String.length s = 0 then true
  else
    if (String.get s 0) = '\"' && (String.get s ((String.length s)-1)) = '\"' then
      String.fold_left(fun acc c -> if is_char c then acc else false) 
      true (String.sub s 1 ((String.length s)-2))
    else false
let valid_name s =
  if String.get s 0 >= 'a' || String.get s 0 <= 'z' then
    String.fold_left(fun acc c -> if is_char c || is_digit c || c = '_' then acc else false) 
    true (String.sub s 0 (String.length s))
  else false
let string_to_token_stream src =
  let sl = String.split_on_char '\n' src in
    let rec helper ls acc =
      match ls with
      |[] -> acc
      |s_instr::tl -> ( 
        if (String.length s_instr) > 5 && (String.sub s_instr 0 5) = "Push " then
        (
          let consval = String.sub s_instr 5 ((String.length s_instr)-5) in
            if String.get consval 0 = '"' && String.get consval ((String.length consval)-1) = '"' then
              (STRING(consval)) ^ (helper tl acc)
            else if is_int consval then (NUMBER((int_of_string consval))) ^ (helper tl acc)
            else if valid_name consval then (VAR(consval)) ^ (helper tl acc)
            else (SYMBOL(s_instr)) ^ (helper tl acc)
        )
      else if (String.length s_instr) > 6 && (String.sub s_instr 0 6) = "Tuple " then
        (
          let var = String.sub s_instr 6 ((String.length s_instr)-6) in
          (
            if is_int var then 
              (
                if (int_of_string var) >= 0 then (TUPLE((int_of_string var))) ^ (helper tl acc)
                else (SYMBOL(s_instr)) ^ (helper tl acc)
              )
            else (SYMBOL(s_instr)) ^ (helper tl acc)
          ) 
        ) 
        else if (String.length s_instr) > 4 && (String.sub s_instr 0 4) = "Get " then
        (
          let var = String.sub s_instr 4 ((String.length s_instr)-4) in
          (
            if is_int var then 
              (
                if (int_of_string var) >= 0 then (GET((int_of_string var))) ^ (helper tl acc)
                else (SYMBOL(s_instr)) ^ (helper tl acc)
              )
            else (SYMBOL(s_instr)) ^ (helper tl acc)
          ) 
        ) 
        else if (String.length s_instr) > 6 && (String.sub s_instr 0 6) = "Local " then 
          let var = String.sub s_instr 6 ((String.length s_instr)-6) in
            (
              if valid_name var then
                (LOCAL(var)) ^ (helper tl acc)
              else 
                (SYMBOL(s_instr)) ^ (helper tl acc)
            )
        else if (String.length s_instr) > 7 && (String.sub s_instr 0 7) = "Global " then
          let var = String.sub s_instr 7 ((String.length s_instr)-7) in
          (
            if valid_name var then
              (GLOBAL(var)) ^ (helper tl acc)
            else 
              (SYMBOL(s_instr)) ^ (helper tl acc)
          )  
        else if (String.length s_instr) > 4 && (String.sub s_instr 0 4) = "Fun " then
          let vl = String.split_on_char ' ' (String.sub s_instr 4 ((String.length s_instr)-4)) in
            (
              match vl with
              | fn::vl' ->
                (
                  match vl' with
                  | var::[] ->
                  (
                    if valid_name fn && valid_name var then
                      (FUN(fn, var)) ^ (helper tl acc)
                    else
                      (SYMBOL(s_instr)) ^ (helper tl acc)
                  )
                | _ -> (SYMBOL(s_instr)) ^ (helper tl acc)
                )
              | _ -> (SYMBOL(s_instr)) ^ (helper tl acc)
            )
        else if (String.length s_instr) > 4 && (String.sub s_instr 0 4) = "Mut " then
          let ls = String.split_on_char ' ' (String.sub s_instr 4 ((String.length s_instr)-4)) in
            (
              match ls with
              | fun_name::ls' -> 
                (
                  match ls' with
                  | var::[] ->
                  (
                    if valid_name fun_name && valid_name var then
                      (MUT(fun_name, var)) ^ (helper tl acc)
                    else
                      (SYMBOL(s_instr)) ^ (helper tl acc)
                  )
                | _ -> (SYMBOL(s_instr)) ^ (helper tl acc)
                )
              | _ -> (SYMBOL(s_instr)) ^ (helper tl acc)
            )
        else if (s_instr = "Begin") then BEGIN ^ (helper tl acc)
        else if (s_instr = "End") then END ^ (helper tl acc)
        else if (s_instr = "IfThen") then IFTHEN ^ (helper tl acc)
        else if (s_instr = "Else") then  ELSE ^ (helper tl acc)
        else if (s_instr = "CaseLeft") then  CASELEFT ^ (helper tl acc)
        else if (s_instr = "Right") then  RIGHT ^ (helper tl acc)
        (* else if (s_instr = "Return") then  RETURN ^ (helper tl acc) *)
        else (SYMBOL(s_instr)) ^ (helper tl acc)
      )
    in  LPAREN ^ helper sl (RPAREN^(eof()))
(************************************************************)
    
type parse_err =
  | InvalidString
  | InvalidSymbol
  | UnmatchedParen
  | UnmatchedParenRP
  | UnmatchedParenElse
  | UnmatchedParenMut
  | UnmatchedParenEnd
  | UnmatchedParenRight
  | UnexpectedEOF
  | MissingElse
  | ErrorCase
  | ErrorIf

let oksymbol s st =
  match s with
    | "Quit" -> ok(ssymbol s, st)
    | "Pop" -> ok(ssymbol s, st)
    | "Add" -> ok(ssymbol s, st)
    | "Sub" -> ok(ssymbol s, st)
    | "Mul" -> ok(ssymbol s, st)
    | "Div" -> ok(ssymbol s, st)
    | "Swap" -> ok(ssymbol s, st)
    | "Neg" -> ok(ssymbol s, st)
    | "Concat" -> ok(ssymbol s, st)
    | "And" -> ok(ssymbol s, st)
    | "Or" -> ok(ssymbol s, st)
    | "Not" -> ok(ssymbol s, st)
    | "Equal" -> ok(ssymbol s, st)
    | "Lte" -> ok(ssymbol s, st)
    | "Else" -> ok(ssymbol s, st)
    | "InjL" -> ok(ssymbol s, st)
    | "InjR" -> ok(ssymbol s, st)
    | "Call" -> ok(ssymbol s, st)
    | "End" -> ok(ssymbol s, st)
    | "Return" -> ok(ssymbol s, st)
    | _ -> Err(InvalidSymbol)

let rec parse_sexpr (st : token stream): (sexpr * token stream, parse_err) result =
  let Next(tok, st) = st () in
  match tok with
  | NUMBER(n) -> ok (snumber n, st)
  | STRING(s) -> if is_string s then ok (sstr s, st) else Err(InvalidString)
  | SYMBOL(s) -> oksymbol s st
  | TUPLE(n) -> ok(stuple n, st)
  | GET(n) -> ok(sget n, st)
  | LOCAL(s) -> ok(svarl s, st)
  | GLOBAL(s) -> ok(svarg s, st)
  | VAR(s) -> ok(svar s, st)
  | BEGIN -> parse_sexpr_list st |> map_ok @@ map_fst slist
  | IFTHEN -> 
    (
      match parse_sexpr_list st |> map_ok @@ map_fst sifthen with
          | Err(_) -> Err(ErrorIf)
          | Ok (sx1, st1) -> 
            (
              match parse_sexpr_list st1 |> map_ok @@ map_fst selse with
              | Err(_) -> Err(ErrorIf)
              | Ok (sx2, st2) -> ok(sifthenelse sx1 sx2, st2)
            )
    )
  | CASELEFT -> 
      (
        match parse_sexpr_list st |> map_ok @@ map_fst sleft with
            | Err(_) -> Err(ErrorCase)
            | Ok (sx1, st1) -> 
              (
                match parse_sexpr_list st1 |> map_ok @@ map_fst sright with
                | Err(_) -> Err(ErrorCase)
                | Ok (sx2, st2) -> ok(scase sx1 sx2, st2)
              )
      )
  | ELSE -> Err(UnmatchedParenElse)
  | END -> Err(UnmatchedParenEnd) 
  | FUN(f, va) -> parse_sexpr_list st |> map_ok @@ map_fst (sfun f va)
  | MUTL(f, va) -> parse_sexpr_list st |> map_ok @@ map_fst (smut f va)
  | MUT _ -> Err(UnmatchedParenMut)
  | LPAREN    -> parse_sexpr_list st |> map_ok @@ map_fst slist
  | RPAREN    -> Err(UnmatchedParenRP)
  | RIGHT -> Err(UnmatchedParenRight)
  | EOF       -> Err(UnexpectedEOF)
  
and parse_sexpr_list (st : token stream): (sexpr_list * token stream, parse_err) result =
    let Next(tok, st') = st () in
    match tok with
    | RPAREN -> ok ([], st')
    | END -> ok ([], st')
    | ELSE -> ok ([], st')
    | RIGHT -> ok ([], st')
    | MUT(a, b) -> ok([], MUTL(a, b)^st')
    | _ -> parse_sexpr st
           |> and_then @@ fun (fst, st') ->
           parse_sexpr_list st'
           |> and_then @@ fun (rst, st'') ->
           ok (fst::rst, st'')

let parse (st : token stream): (sexpr list, parse_err) result =
  let rec parse_all st acc =
    let Next(tok, _) = st () in
    match tok with
    | EOF -> Ok(reverse acc)
    | _   -> parse_sexpr st
             |> and_then @@ fun (s, ts) ->
      parse_all ts (s :: acc)
  in
  parse_all st []
(******************************************************************************)           
let get_rl ls = match ls with h::t -> t | [] -> []

let get_rl2 ls = match ls with h::t -> get_rl t | [] -> []
  
let renew_top1 helper f stk rest genv lenv (res, env1, env2, st)=
  match stk with
  | Entry(Int x, re) -> helper rest (Entry(Int(f x), re)) genv lenv ((string_of_int (f x))::(get_rl res), env1, env2, Entry(Int(f x), re))
  | _ -> (["\"Error\""], Empty, Empty, Empty)

let renew_top2 helper f stk rest genv lenv (res, env1, env2, st)=
  match stk with
  | Entry(Int x, Entry(Int y, re)) -> helper rest (Entry(Int(f x y), re)) genv lenv ((string_of_int (f x y))::(get_rl2 res), env1, env2, Entry(Int(f x y), re))
  | _ -> (["\"Error\""], Empty, Empty, Empty)
   
let is_bool x = if x = 0 then true else if x = 1 then true else false
let is_bool_pair x y = (is_bool x) && (is_bool y)
let and_res x y = if x = 1 && y = 1 then 1 else 0
let or_res x y = if x = 1 || y = 1 then 1 else 0
let not_res x = if x = 1 then 0 else 1
let eq_res x y = if x = y then 1 else 0
let lte_res x y = if x > y then 0 else 1
let renew_top2_bool helper f stk rest genv lenv (res, env1, env2, st)=
  match stk with
  | Entry(Int x, Entry(Int y, re)) -> 
  (
    if is_bool_pair x y then
      helper rest (Entry(Int(f x y), re)) genv lenv (((string_of_int (f x y))::(get_rl2 res)), env1, env2, Entry(Int(f x y), re))
    else (["\"Error\""], Empty, Empty, Empty)
  )
  | _ -> (["\"Error\""],Empty, Empty, Empty)
let renew_top1_bool helper f stk rest genv lenv (res, env1, env2, st) =
  match stk with
  | Entry(Int x, re) -> 
  (
    if is_bool x then
      helper rest (Entry(Int(f x), re)) genv lenv ((string_of_int (f x))::(get_rl res), env1, env2, Entry(Int(f x), re))
    else (["\"Error\""],Empty, Empty, Empty)
  )
  | _ -> (["\"Error\""],Empty, Empty, Empty)
(******************************************************************************)

let var_exist name env =
  let rec helper name env (va, acc)=
    match env with
    | Empty -> (va, acc)
    | Entry((s, n), env') -> if s = name then (n, true) else helper name env' (va, acc) 
  in helper name env (String("-1"), false)

let name_exist (name: string) (env: (string*value) env) =
  let rec helper name env (acc, b)=
    match env with
    | Empty -> (acc, b)
    | Entry((s, v), env') -> 
      if name = s then helper name env' (acc, true) else helper name env' (Entry((s, v), acc), b)
  in helper name env (Empty, false)

let store_lvar helper rest (name: string) stk genv (lenv: (string*value) env) (res, env1, env2, st)=
  match stk with
  | Entry(value, stk') -> 
    (
      match name_exist name lenv with
      | (ev, true) -> helper rest stk' genv (Entry((name, value), ev)) ((get_rl res), env1, Entry((name, value), ev), stk')
      | (_, false) -> helper rest stk' genv (Entry((name, value), lenv)) ((get_rl res), env1, Entry((name, value), lenv), stk')
    )
  | _ -> (["\"Error\""], Empty, Empty, Empty)

let store_gvar helper rest (s: string) stk genv lenv (res, env1, env2, st)=
  match stk with
  | Entry(value, stk') -> 
    (
      match name_exist s genv with   
      | (ev, true) -> helper rest stk' (Entry((s,value), ev)) lenv (get_rl res, Entry((s,value), ev), env2, stk')
      | (_, false) -> helper rest stk' (Entry((s,value), genv)) lenv (get_rl res, Entry((s,value), genv), env2, stk')
    )
  | _ -> (["\"Error\""], Empty, Empty, Empty)

let get_fun_env (name: string) (va: value) (env: (string*value) env):  (string*value) env=
  let rec helper env va acc =
    match env with
    | Empty ->  acc
    | Entry((na, v), env') ->
      (
        match v with
        | Clo _ -> helper env' va acc
        | _ ->
        if na = name then helper env' va acc
        else helper env' va (Entry((na, v), acc))
      )
      in helper env va (Entry((name, va), Empty))

let get_tuple_ele (tuple: value list) (num: int): value= 
  let rec helper tu n res =
    if n = -1 then res
    else match tu with [] -> String("\"Error\"") | v::tu' ->  helper tu' (n-1) v
  in helper tuple num (String("\"Error\""))

let get_left sl =
  match sl with
  | [] -> "error"
  | h::_ ->
  if String.length h > 5 then
    String.sub h 5 ((String.length h)-5)
  else
    "error"

let get_right sl =
  match sl with
  | [] -> "error"
  | h::_ ->
  if String.length h > 6 then
    String.sub h 6 ((String.length h)-6)
  else
    "error"

let clo2str name var =
  String.cat (String.cat (String.cat (String.cat "Clo (" name) ", ") var) ")" 
let rec tuple2str (tu: value list) =
  let rec helper tu acc =
    match tu with
    | [] -> acc
    | h::[] ->
      (
        match h with
        | String(s) -> (String.cat acc s)
        | Int(n) -> (String.cat acc (string_of_int n))
        | UnionL(u) -> (String.cat acc (String.cat "Left "(union2str u)))
        | UnionR(u) -> (String.cat acc (String.cat "Right "(union2str u)))
        | Tuple(t) -> (String.cat acc (tuple2str t))
        | Clo(name, var, _, _, _) -> String.cat acc (clo2str name var)
      )
    | h::tu' ->
      (
        match h with
        | String(s) -> helper tu' (String.cat acc (String.cat s ", "))
        | Int(n) -> helper tu' (String.cat acc (String.cat (string_of_int n) ", ") )
        | UnionL(u) -> helper tu' (String.cat acc (String.cat (String.cat "Left "(union2str u)) ", "))
        | UnionR(u) -> helper tu' (String.cat acc (String.cat (String.cat "Right "(union2str u)) ", "))
        | Tuple(t) -> helper tu' (String.cat acc (String.cat (tuple2str t) ", "))
        | Clo(name, var, _, _, _) -> String.cat acc (String.cat " "(clo2str name var) )
      )
    in String.cat "(" (String.cat (helper tu "") ")")
and union2str u =
  let rec helper u acc =
    match u with
    | String(s) -> String.cat acc s
    | Int(n) -> String.cat acc (string_of_int n)
    | Tuple(tu) -> String.cat acc (tuple2str tu)
    | UnionR u' -> helper u' (String.cat "Right " acc) 
    | UnionL u' -> helper u' (String.cat "Left " acc) 
    | Clo(name, var, _, _, _) -> String.cat acc (String.cat " "(clo2str name var) )
  in helper u ""

let rec find_mut (env: (string*value) env) (name: string) =
  match env with
  | Empty -> None
  | Entry((na, va), env') -> 
    if na = name then Some va 
    else find_mut env' name

let rec get_muts mut lenv acc =
  match mut with
  | [] -> acc
  | (name, var, prog)::mut' ->
      match find_mut lenv name with
      | None -> acc
      | Some(va) -> get_muts mut' lenv (Entry((name, va), acc))

let is_mut_name na mut_ls =
  let rec helper mut_ls acc =
    match mut_ls with
    | [] -> acc
    | (name, _, _)::t ->
      if name = na then true else helper mut_ls acc
  in helper mut_ls false
let rec update_fun_env (name: string) (env: (string*value) env) new_env acc =
  match env with
  | Empty -> acc
  | Entry((str, va), env') ->
    (
      if name = str then
        match va with
        | Clo(n, v, prog, e, mut) -> update_fun_env name env' new_env (Entry((n, Clo(n, v, prog, new_env, mut)), acc))
        | _ -> acc
      else update_fun_env name env new_env (Entry((str,va), acc))
    )

let create_fun_env func va fenv lenv acc: (string*value) env =
  match func with
      | Clo(name, var, prog, fenv, mut_ls) -> 
        if fenv = Empty then 
          let rec helper mut_ls lenv acc=
            match lenv with
            | Empty -> acc
            | Entry((na, f), lenv') -> 
              if is_mut_name na mut_ls then helper mut_ls lenv' (Entry((na, f), acc)) 
              else helper mut_ls lenv' acc
            in helper mut_ls lenv (Entry((name, func), Entry((var, va), Empty)))
        else 
          let rec helper var va fenv acc =
            match fenv with
            | Empty -> acc
            | Entry((name, value), fenv') ->
              if name = var then helper var va fenv' (Entry((name, va), acc))
              else helper var va fenv' (Entry((name, value), acc))
          in helper var va fenv Empty
    | _ -> Empty

(******************************************************************************)

let eval (e: (sexpr list, parse_err) result) =
  match e with
  | Err _ -> ["\"Error\""]
  | Ok el -> 
    (
      match el with
      | (BeginEnd resl)::_ -> 
        (
        let rec helper (sex_list: sexpr_list) stk (genv: (string*value) env) (lenv: (string*value) env) (res, env1, env2, st): string list*(string*value) env * (string*value) env * value env=
          match sex_list with
          | [] -> (res, env1, env2, st)
          | (Atom(Number(n)))::rest -> helper rest (Entry(Int(n), stk)) genv lenv (((string_of_int n)::res), env1, env2, Entry(Int(n), st))
          | (Atom(String(s)))::rest -> helper rest (Entry(String(s),stk)) genv lenv ((s::res), env1, env2, Entry(String(s),st))
          | (Fun(f))::rest -> 
            (
              let rec get_funs ls (acc, rest) =
                (* turn mutual functions into a list *)
                match ls with
                | (Mut(f))::tl -> get_funs tl ((Mut(f))::acc, tl)
                | _ -> (acc, rest)
              in let (fs, rest) = get_funs rest ([Fun(f)], rest) in
              let rec trav_fun ls acc =
                match ls with
                | [] -> acc
                | h::tl ->
                  (
                    match h with
                    | Fun(Header(name,var)::prog) -> trav_fun tl ((name, var, prog)::acc)
                    | Mut(Header(name,var)::prog) -> trav_fun tl ((name, var, prog)::acc)
                    | _ -> acc
                  )
              in let funlist = trav_fun fs [] in
                (
                  let rec create_clo ls (acc, prev) =
                    match ls with
                    | [] -> (acc, prev)
                    | (name, var, prog)::ls' -> create_clo ls' (Clo(name, var, prog, Empty, prev @ ls')::acc, (name, var, prog)::prev)
                  in 
                  match create_clo funlist ([], []) with (fun_ls, _) -> 
                    let rec str_funs fun_ls acc =
                        match fun_ls with
                        | [] -> acc
                        | h::tl -> 
                          (
                            match h with
                            | Clo(name, _, _, _, _) -> str_funs tl (Entry((name, h), acc))
                            | _ -> Empty
                          )
                    in helper rest stk genv (str_funs fun_ls lenv) (res, env1, str_funs fun_ls lenv, stk)
                )
            )
          | (Get(n))::rest -> 
            (
              match (stk, res) with
              | (Entry(Tuple(t), _), str::_) -> 
                (
                  let a = get_tuple_ele t n in
                  match a with
                  | String("\"Error\"") -> (["\"Error\""], Empty, Empty, Empty)
                  | _ -> 
                        (
                          match a with
                          | Tuple(tu) -> helper rest (Entry(a,stk)) genv lenv (((tuple2str tu)::res), env1, env2, Entry(a,st))
                          | String(s) -> helper rest (Entry(a,stk)) genv lenv ((s::res), env1, env2, Entry(a,st))
                          | Int(n) -> helper rest (Entry(a,stk)) genv lenv (((string_of_int n)::res), env1, env2, Entry(a,st))
                          | UnionL(u) -> helper rest (Entry(a,stk)) genv lenv (((String.cat "Left "(union2str u))::res), env1, env2, Entry(a,st))
                          | UnionR(u) -> helper rest (Entry(a,stk)) genv lenv (((String.cat "Right "(union2str u))::res), env1, env2, Entry(a,st))
                          | Clo(name, var, _, _, _) -> helper rest (Entry(a,stk)) genv lenv (((clo2str name var)::res), env1, env2, Entry(a,st))
                        )
                )

              | (_, _) -> (["\"Error\""], Empty, Empty, Empty)
            )
          | (Tuple(n))::rest -> 
            (
              let rec helper_tu stk res num (stk1, res1, tuple1, str)=
                match num with
                | 0 -> 
                  (
                    if String.length str = 0 then 
                      (stk1, res1, tuple1, "()")
                    else 
                      (stk1, res1, tuple1, String.cat (String.cat "(" (String.sub str 0 ((String.length str)-2)))  ")")
                  )
                | _ -> 
                  (
                      match (stk, res) with      
                      | (Entry(Int(n), stk'), h::res') -> helper_tu stk' res' (num-1) (stk', res', (Int(n))::tuple1, String.cat (String.cat h ", ") str)
                      | (Entry(String(s),stk'),h::res') -> helper_tu stk' res' (num-1) (stk', res', (String(s))::tuple1, (String.cat (String.cat h ", ") str))
                      | (Entry(Tuple(t),stk'), h::res') -> helper_tu  stk' res' (num-1) (stk', res', (Tuple(t))::tuple1, String.cat (String.cat h ", ") str)
                      | (Entry(UnionL(t),stk'), h::res') -> helper_tu  stk' res' (num-1) (stk', res', (UnionL(t)::tuple1), String.cat (String.cat h ", ") str)
                      | (Entry(UnionR(t),stk'), h::res') -> helper_tu  stk' res' (num-1) (stk', res', (UnionR(t)::tuple1), String.cat (String.cat h ", ") str)
                      | (Entry(Clo(a, b, c, d, e),stk'), h::res') -> helper_tu  stk' res' (num-1) (stk', res', (Clo(a, b, c, d, e)::tuple1), String.cat (String.cat h ", ") str)
                      | (_, _) -> (Empty, ["\"Error\""], [], "")
                  )
              in match helper_tu stk res n (Empty, [], [], "") with
              | (_, ["\"Error\""], _, _) -> (["\"Error\""], Empty, Empty, Empty)
              | (stk', res', tuple, tu_str) -> helper rest (Entry(Tuple(tuple), stk')) genv lenv (tu_str::res', env1, env2, Entry(Tuple(tuple), stk'))
            )
          | (Atom(LVariable(s)))::rest -> store_lvar helper rest s stk genv lenv (res, env1, env2, stk)
          | (Atom(GVariable(s)))::rest -> store_gvar helper rest s stk genv lenv (res, env1, env2, stk)
          | (Atom(Var(name)))::rest -> 
            (
              match var_exist name lenv with
              | (Int(n), true) -> helper rest (Entry(Int(n), stk)) genv lenv (((string_of_int n)::res), env1, env2, Entry(Int(n), stk))
              | (String(s), true) -> helper rest (Entry(String(s),stk)) genv lenv ((s::res), env1, env2, Entry(String(s),stk))
              | (Tuple(tu), true) -> helper rest (Entry(Tuple(tu),stk)) genv lenv (((tuple2str tu)::res), env1, env2, Entry(Tuple(tu),stk))
              | (UnionL(s), true) -> helper rest (Entry(UnionL(s),stk)) genv lenv (((String.cat "Left "(union2str s))::res), env1, env2, Entry(UnionL(s),stk))
              | (UnionR(s), true) -> helper rest (Entry(UnionR(s),stk)) genv lenv (((String.cat "Right " (union2str s))::res), env1, env2, Entry(UnionR(s),stk))
              | (Clo(name, var, prog, fenv, mut), true) -> 
                helper rest (Entry(Clo(name, var, prog, fenv, mut),stk)) genv lenv 
                (((clo2str name var)::res), env1, env2, Entry(Clo(name, var, prog, fenv, mut),stk))
              | (_, false) -> 
                (
                  match var_exist name genv with
                  | (Int(n), true) -> helper rest (Entry(Int(n), stk)) genv lenv (((string_of_int n)::res), env1, env2, Entry(Int(n), stk))
                  | (String(s), true) -> helper rest (Entry(String(s),stk)) genv lenv ((s::res), env1, env2, Entry(String(s),stk))
                  | (Tuple(tu), true) -> helper rest (Entry(Tuple(tu),stk)) genv lenv (((tuple2str tu)::res), env1, env2, Entry(Tuple(tu),stk))
                  | (UnionL(s), true) -> helper rest (Entry(UnionL(s),stk)) genv lenv (((String.cat "Left "(union2str s))::res), env1, env2, Entry(UnionL(s),stk))
                  | (UnionR(s), true) -> helper rest (Entry(UnionR(s),stk)) genv lenv (((String.cat "Right " (union2str s))::res), env1, env2, Entry(UnionR(s),stk))
                  | (_, _) -> (["\"Error\""], Empty, Empty, Empty)
                )
            )
          | (Atom(Symbol(s)))::rest -> 
          (
            match s with
            | "Quit" -> ("quit"::res, env1, env2, st)
            | "Return" -> ("return"::res, env1, env2, st)
            | "Pop" -> 
              (
                match stk with
                | Entry(_,re) -> helper rest re genv lenv ((get_rl res), env1, env2, re)
                | _ -> (["\"Error\""], Empty, Empty, Empty)
              )
            | "Add" -> renew_top2 helper (+) stk rest genv lenv (res, env1, env2, stk)
            | "Sub" -> renew_top2 helper (-) stk rest genv lenv (res, env1, env2, stk)
            | "Mul" -> renew_top2 helper ( * ) stk rest genv lenv (res, env1, env2, stk)
            | "Neg" -> renew_top1 helper (fun x -> -x) stk rest genv lenv (res, env1, env2, stk)
            | "Div" -> (
              match stk with
              | Entry(Int x, Entry(Int y, re)) -> (
                if y = 0 then (["\"Error\""], Empty, Empty, Empty)
                else 
                  helper rest (Entry(Int(x/y), re)) genv lenv ((string_of_int (x/y))::(get_rl2 res), env1, env2, Entry(Int(x/y), re))
              )
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
            | "Swap" -> (
              match (stk, res) with
              | (Entry(a, Entry(b, re)), x::y::res') -> helper rest (Entry(b, Entry(a, re))) genv lenv (y::x::res', env1, env2, Entry(b, Entry(a, re)))
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
            | "Concat" -> (
              match stk with
              | Entry(String x, Entry(String y, re)) -> 
                    let x' = String.cat "\"" (String.sub x 1 ((String.length x)-2)) in
                      let y'= String.cat (String.sub y 1 ((String.length y)-2)) "\"" in
                    helper rest (Entry(String(String.cat x' y'), re)) genv lenv ((String.cat x' y')::(get_rl2 res), genv, lenv, Entry(String(String.cat x' y'), re))
                    
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
            | "And" -> renew_top2_bool helper and_res stk rest genv lenv (res, env1, env2, stk)
            | "Or" -> renew_top2_bool helper or_res stk rest genv lenv (res, env1, env2, stk)
            | "Not" -> renew_top1_bool helper not_res stk rest genv lenv (res, env1, env2, stk)
            | "Equal" -> renew_top2 helper eq_res stk rest genv lenv (res, env1, env2, stk)
            | "Lte" -> renew_top2 helper lte_res stk rest genv lenv (res, env1, env2, stk)
            | "InjL" -> 
              (
                match (stk, res) with
                | (Entry(Int x, re), h::res') -> helper rest (Entry(UnionL(Int(x)), re)) genv lenv ((String.cat "Left " h)::res', env1, env2, Entry(UnionL(Int(x)), re))
                | (Entry(String s, re), h::res') -> helper rest (Entry(UnionL(String(s)), re)) genv lenv ((String.cat "Left " h)::res', env1, env2, Entry(UnionL(String(s)), re))
                | (Entry(UnionL u, re), h::res') -> helper rest (Entry(UnionL(UnionL(u)), re)) genv lenv ((String.cat "Left " h)::res', env1, env2, Entry(UnionL(UnionL(u)), re))
                | (Entry(UnionR u, re), h::res') -> helper rest (Entry(UnionL(UnionR(u)), re)) genv lenv ((String.cat "Left " h)::res', env1, env2, Entry(UnionL(UnionR(u)), re))
                | (Entry(Tuple t, re), h::res') -> helper rest (Entry(UnionL(Tuple(t)), re)) genv lenv ((String.cat "Left " h)::res', env1, env2, Entry(UnionL(Tuple(t)), re))
                | (Entry(Clo(a,b,c,d,e), re), h::res') -> helper rest (Entry(UnionR(Clo(a,b,c,d,e)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(Clo(a,b,c,d,e)), re))
                | _ -> (["\"Error\""], Empty, Empty, Empty)
              )
            | "InjR" -> 
              (
                match (stk, res) with
                | (Entry(Int x, re), h::res') -> helper rest (Entry(UnionR(Int(x)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(Int(x)), re))
                | (Entry(String s, re), h::res') -> helper rest (Entry(UnionR(String(s)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(String(s)), re))
                | (Entry(UnionL u, re), h::res') -> helper rest (Entry(UnionR(UnionL(u)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(UnionL(u)), re))
                | (Entry(UnionR u, re), h::res') -> helper rest (Entry(UnionR(UnionR(u)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(UnionR(u)), re))
                | (Entry(Tuple t, re), h::res') -> helper rest (Entry(UnionR(Tuple(t)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(Tuple(t)), re))
                | (Entry(Clo(a,b,c,d,e), re), h::res') -> helper rest (Entry(UnionR(Clo(a,b,c,d,e)), re)) genv lenv ((String.cat "Right " h)::res', env1, env2, Entry(UnionR(Clo(a,b,c,d,e)), re))
                | _ -> (["\"Error\""], Empty, Empty, Empty)
              )        
            | "Call" -> 
              (
                match stk with
                | Entry(Clo(name, var, prog, fenv, mut_ls), stk') ->
                  (
                    match stk' with
                    | Entry(va, stk'') -> 
                      (
                          (* let fun_lenv = get_muts mut_ls fenv (Entry((name, Clo(name, var, prog, fenv, mut_ls)), Entry((var, va), fenv))) in *)
                          (* let fun_lenv = get_muts mut_ls lenv (Entry((name, Clo(name, var, prog, fenv, mut_ls)), get_fun_env var va fenv)) in *)
                          let fun_lenv = create_fun_env (Clo(name, var, prog, fenv, mut_ls)) va fenv lenv Empty in
                              let inner_stk = helper prog Empty genv fun_lenv ([], env1, fun_lenv, Empty) in
                                match inner_stk with
                                | ("return"::h::t, genv', fenv', Entry(top, _)) ->
                                  (
                                      helper rest (Entry(top,stk'')) genv' (update_fun_env name lenv fenv' Empty) ((h::(get_rl2 res)), genv', update_fun_env name lenv fenv' Empty, Entry(top,stk''))
                                  ) 
                                | _ -> (["\"Error\""], Empty, Empty, Empty)            
                      )
                    | Empty -> (["\"Error\""], Empty, Empty, Empty)
                  )
                | _ -> (["\"Error\""], Empty, Empty, Empty)
              )
            | _ -> (["\"Error\""], Empty, Empty, Empty)  
          )              
          | (BeginEnd(sl))::rest -> 
            ( 
              match helper sl Empty genv lenv ([], env1, env2, Empty) with
              | ([],_, _, _) -> (["\"Error\""], Empty, Empty, Empty)
              | (h::t, env1', _, Entry(top, _))-> 
                (
                  if h = "quit" then (h::t,Empty, Empty, Empty)
                  else helper rest (Entry(top,stk)) env1' lenv ((h::res), env1', lenv, Entry(top,stk))
                ) 
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
          | (IfThenElse(sl1, sl2))::rest -> 
            (
              match (sl1, sl2) with
              | (IfThen s1, Else s2) -> 
                (
                  match stk with
                  | Entry(Int(1), stk') -> 
                    (
                      let (new_res, env1', env2', new_stk) = helper s1 stk' genv lenv (get_rl res, env1, env2, stk') in
                          helper rest new_stk env1' env2' (new_res, env1', env2', new_stk)
                    )
                  | Entry(Int(0), stk') -> 
                    (
                      let (new_res, env1', env2', new_stk) = helper s2 stk' genv lenv (get_rl res, env1, env2, stk') in
                        helper rest new_stk env1' env2' (new_res, env1', env2', new_stk)
                    )
                  | _ -> (["\"Error\""], Empty, Empty, Empty)  
                )
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
          | ((Case(sl1, sl2))::rest) -> 
            (
              match (sl1, sl2) with
              | (Left s1, Right s2) -> 
                (
                  match stk with
                  | Entry(UnionL(x), stk') ->
                    (
                      let (new_res, env1', env2', new_stk) = helper s1 (Entry(x,stk')) genv lenv ((get_left res)::(get_rl res), env1, env2, Entry(x,stk')) in
                        match new_res with
                        | ["\"Error\""] -> (["\"Error\""], Empty, Empty, Empty)
                        | _ -> helper rest new_stk env1' env2' (new_res, env1', env2', new_stk)
                    )
                  | Entry(UnionR(x), stk') ->
                    (
                      let (new_res, env1', env2', new_stk) = helper s2 (Entry(x,stk')) genv lenv ((get_right res)::(get_rl res), env1, env2, Entry(x,stk')) in
                        match new_res with
                        | ["\"Error\""] -> (["\"Error\""], Empty, Empty, Empty)
                        | _ ->helper rest new_stk env1' env2' (new_res, env1', env2', new_stk)
                    )
                  | _ -> (["\"Error\""], Empty, Empty, Empty)
                )
              | _ -> (["\"Error\""], Empty, Empty, Empty)
            )
          | _ -> (["\"Error\""], Empty, Empty, Empty) 
        in match (helper resl Empty Empty Empty ([], Empty, Empty, Empty)) with (log,_,_,_) -> 
          match log with 
          |"quit"::t -> t 
          | ["\"Error\""] -> ["\"Error\""]
          | _ -> [""]
        )
      | _ -> ["\"Error\""]
  )

let s="Push \"Nil\"
InjL
Global nil
Fun map ls
Fun rec f
Push ls
CaseLeft
Push nil
Return
Right
Get 0
Push map
Call
Push f
Swap
Call
Swap
Get 1
Swap
Pop
Push f
Call
Tuple 2
InjR
Return
End
End
Push rec
Return
End
Fun add_one x
Push 1
Push x
Add
Return
End
Push nil
Push 1
Tuple 2
InjR
Push 3
Tuple 2
InjR
Push 2
Tuple 2
InjR
Push 5
Tuple 2
InjR
Push 7
Tuple 2
InjR
Push add_one
Swap
Push map
Call
Call
Quit"

let get_res (src:string) = src |> string_to_token_stream |> parse |> eval
let ts = string_to_token_stream s
let pa = parse ts     
let res = get_res s
let write_file (content: string)(file_path: string) : unit =
  let fp = open_out file_path in
  Printf.fprintf fp "%s" content;
  close_out fp
let interpreter (src : string) (output_file_path: string)=
  let res_l = src |> string_to_token_stream |> parse |> eval |> reverse in
    let res = fold_left(fun acc s-> String.cat (String.cat s "\n") acc) "" res_l  in
  write_file res output_file_path