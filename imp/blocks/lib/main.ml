open Types
open Ast

(*funzione che valuta se è un numero naturale*)


let parse (s : string) : cmd =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast


exception NoRuleApplies

(* let rec eval_expr state expr = 
  match expr with
    True -> Bool true
  | False -> Bool false
  | Var x -> state x
  | Const n -> Nat n
  | Not e -> 
    (match eval_expr state e with
      Bool b -> Bool (not b)
      | _ -> raise (TypeError "Expected a boolean value"))
  | And(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Bool b1, Bool b2) -> Bool (b1 && b2)
      | _ -> raise (TypeError "Expected two boolean values"))
  | Or(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Bool b1, Bool b2) -> Bool (b1 || b2)
      | _ -> raise (TypeError "Expected two boolean values"))
  | Add(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Nat n1, Nat n2) -> Nat (n1 + n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Sub(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Nat n1, Nat n2) -> Nat (n1 - n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Mul(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Nat n1, Nat n2) -> Nat (n1 * n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Eq(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Nat n1, Nat n2) -> Bool (n1 = n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Leq(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Nat n1, Nat n2) -> Bool (n1 <= n2)
      | _ -> raise (TypeError "Expected two integer values")) *)

let rec eval_expr state expr = 
  match expr with
    True -> Bool true
  | False -> Bool false
  | Const n -> Int n
  | Not e -> 
    (match eval_expr state e with
      Bool b -> Bool (not b)
      | _ -> raise (TypeError "Expected a boolean value"))
  | And(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Bool b1, Bool b2) -> Bool (b1 && b2)
      | _ -> raise (TypeError "Expected two boolean values"))
  | Or(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Bool b1, Bool b2) -> Bool (b1 || b2)
      | _ -> raise (TypeError "Expected two boolean values"))
  | Add(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Int n1, Int n2) -> Int (n1 + n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Sub(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Int n1, Int n2) -> Int (n1 - n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Mul(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Int n1, Int n2) -> Int (n1 * n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Eq(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Int n1, Int n2) -> Bool (n1 = n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Leq(e1, e2) -> 
    (match (eval_expr state e1, eval_expr state e2) with
      (Int n1, Int n2) -> Bool (n1 <= n2)
      | _ -> raise (TypeError "Expected two integer values"))
  | Var ide -> 
    (let top_env = (topenv state) in
      let envval = (top_env ide) in
        match envval with 
          BVar loc -> (getmem state)(loc)
        | IVar loc -> (getmem state)(loc)
    )

let eval_decl (state : state) (decl_list : decl list) : state = 
  let env = (topenv state) in (* qui vado a prendere l'env possiede tutte le dichiarazioni precedenti *)
    let loc = (getloc state) in (* prima locazione disponibile (nella prima chiamata è 0)*)
    let (new_loc, new_env) = List.fold_left(fun (l, e) d -> 
      match d with 
        IntVar ide -> l + 1, (bind_env e ide (IVar l)) (* mettendo l partiamo da 0 fino a lunghezza(decl_list) *)
        | BoolVar ide -> l + 1, (bind_env e ide (BVar l)) 
    ) (loc, env) decl_list in 
    make_state ((new_env :: getenv state)) (getmem state) new_loc
  
(* vedere cosa fa d *)
let rec trace1 = function
  Cmd(c, st) ->
    (match c with
      Skip -> (St st) (* lo stato del programma rimane lo stesso *)
    | Assign(x, e) ->
      ( 
        (* valuto il valore di e *)
        let v = eval_expr st e in
          let top_env = (topenv st) in
          (* opttengo l'ultimo enviroment dalla lista di enviroment *)
            (* ottengo la locazione di memoria del identificatore x *)
            match (top_env x) with
              BVar loc -> St (setmem st (bind_mem (getmem st) loc v))
              | IVar loc -> St (setmem st (bind_mem (getmem st) loc v))) 
              (* 
                1) ottengo la memoria dallo stato
                2) aggiorno la memoria con il nuovo valore
                3) aggiorno lo stato con la nuova memoria
                4) restituisco lo stato aggiornato
              *)
    | Seq(c1, c2) ->
        (
          let conf' = trace1 (Cmd(c1, st)) in (* esecuzione primo comando della sequenza -> cmd1;cmd2 *)
            match conf' with
              Cmd(cmd', st') -> Cmd(Seq(cmd', c2), st') (* qui sta terminando l'esecuzione del primo cmd *)
            | St s -> Cmd(c2, s) (* qui inizia l'esecuzione del secondo comando, che seguirà lo stesso percorso del primo *)
        )
    | If(e, c1, c2) -> 
        (match (eval_expr st e) with
          Bool b -> 
          (if b = true 
            then Cmd(c1, st) (* se b == true  valuta il primo comando  *)
            else Cmd(c2, st) (* se b == false valuta il secondo comando *)
          )
          | _ -> raise (TypeError "Expected a boolean value") 
        )
    | While(e, c1) -> 
        (match (eval_expr st e) with
          Bool b ->
            (if b = true
              then Cmd(Seq(c1, c1), st) (* se b == true esegue il comando e poi si richiama ricorsivamente *)
              else St st (* se b == false termina l'esecuzione del while aggiornano lo stato del programma *)
            )
          | _ -> raise (TypeError "Expected a boolean value")
        )
    | Decl(dec_list, cmd) -> 
      let st' = (eval_decl st dec_list) in
        Cmd(Block(cmd), st')
    | Block cmd ->
      let result = trace1 (Cmd(cmd, st)) in
        match result with
        Cmd(c, st') -> Cmd(Block(c), st')
      | St s -> St (make_state (popenv s) (getmem s) (getloc s))
    )
  | St _ -> raise NoRuleApplies

let rec create_list n_steps acc f conf = 
  (* va avanti finche non arriva a 0 *)
  if n_steps < 0 
    then List.rev acc (* restituisce la lista di comandi al contrario *)
    else 
      try let conf' = f conf in (* se restituisce una configurazione va avanti nella creazione della lista *)
        create_list (n_steps - 1) (conf' :: acc) f conf'
      with _ -> List.rev acc (* se da un eccezzione allora si ferma perché il cmd non si può ridurre ulteriormente *)
      
let trace n_steps cmd = 
  (* cmd -> è il comando di partenza 
     bottom -> è lo stato 0 quello di partenza quindi senza valore *)
  let conf' = Cmd(cmd, state0) in
    create_list n_steps [] trace1 conf'
  

      

              