open Types
open Ast

(* funzioni d'appoggio *)
let return expr = fun st -> (st, expr)

  
type 'a t = state -> state * 'a
let set (st : state) : unit t = fun _ -> (st, ())
let get : state t = fun st -> (st, st)

let bind (e : 'a t) (next : 'a -> 'b t) : 'b t =
  fun st ->
   let st', a = e st in
   next a st'

let ( let$ ) = bind
    
(** [parse s], questo serve per creare l'albero di sinstassi astratta (AST) dalla stringa [s] che è il programma letto  *)
let parse (s : string) : prog =
  let lexbuf = Lexing.from_string s in (* qui lo mette in un formato analizzabile per il lexer *)
  let ast = Parser.prog Lexer.read lexbuf in (** qui abbiamo che [lexbuf] viene dato in pasto a [Lexer.read] che fa a richiamare la "rule" all'interno del lexer, per poi essere passato a [Parser.prog] che è una regola di produzione dentro il parser *)
  ast



exception NoRuleApplies

(* eval_decl: inizio *)
(** [eval_decl state decl_list] prende lo stato composto da [env list, memory, freeLoc] e lo aggiorna facendo la bind e l'allocazione in memoria di [decl_list], esempio decl_list: [int min; int x; int y;] *)
let eval_decl (state : state) (decl_list : decl list) : state = 
  
  let env = (topenv state) in (* qui vado a prendere l'env possiede tutte le dichiarazioni precedenti *)
    
    let loc = (getloc state) in (* prima locazione disponibile (nella prima chiamata è 0)*)
    
      let (new_loc, new_env) = List.fold_left(fun (l, e) d -> 
        match d with 
          | IntVar ide -> 
            l + 1, (bind_env e ide (IVar l)) (* mettendo l partiamo da 0 fino a lunghezza(decl_list) *)
          | Fun (nome_f, params, body, expr) -> 
            l + 1, (bind_env e nome_f (IFun (params, body, expr))) (* come facciamo sopra noi stiamo faciendo il bind tra il nome della funzione e tutti i suoi componenti *)
      ) (loc, env) decl_list in 
      make_state ((new_env :: getenv state)) (getmem state) new_loc

(* Descrizione righe 37 -> 42 
  data la dichiarazione-i gli associa una nuova locazione e con bind_env associa l'ide-i all'env che estende l'env precedente(estende inteso come prende le informazioni di quello precedente e aggiunge le nuove informazioni)

  bind_env (env) (ide) (loc): 
  Descrizione
    è una funzione che dati
    un environment (env), 
    un identificatore (ide),
    una locazione (loc),
    restituisce un nuovo environment new_env che
    estende env aggiungendo la nuova associazione tra ide e loc.
  Implementazione:
    se ide è in new_env, allora restituisce loc
    altrimenti chiama env, a cui new_env è associato, e cerca 
    in profondità. 
  Esempio
      bottom_env = fun x -> raise (UnboundVar x);;
      e0 = bind_env (bottom_env) ("foo") (0);;
      e1 = bind_env (bottom_env) ("bar") (1);;
      e2 = bind_env (bottom_env) ("baz") (2);;

      l'esecuzione di
      e2 ("foo");; 

    andrà a eseguire una serie di ricerche
      sempre più interne, sino a trovare la locazione
      oppure a lanciare un'eccezione:
  ("baz",("bar",("foo",(raise UnboundVar x)))
*)

(* eval_decl: fine *)

(* eval_expr: inizio *)
(** [eval_expr state expr] prende lo [state] così da poterlo aggiornare con l'eventuale valutazione di [expr] *)
let rec eval_expr state expr = 
  match expr with
  | True -> (fun state -> (state, True))
  | False -> return False
  | Const n -> return (Const n)
  | Var ide -> (* 
        con get prendiamo lo stato attuale
        con apply andiamo a recuperare il valore della variabile
        con return restituiamo il valore della variabile come costante(expr)
      *)
      let$ st = get in
      return (Const (apply st ide))
  (* Costrutto NOT *)
  | Not True -> return False 
  | Not False -> return True 
  | Not e ->
    let$ e1' = eval_expr state e in
    return (Not e1')

  (* Costrutto AND *)
  | And (False, _) -> return False 
  | And (True, e2) -> eval_expr state e2
  | And (e1, e2) ->
    let$ e1' = eval_expr state e1 in
    return (And (e1', e2))

  (* Costrutto OR *)
  | Or (True, _) -> return True
  | Or (False, e2) -> eval_expr state e2
  | Or (e1, e2) ->
    let$ e1' = eval_expr state e1 in
    return (Or (e1', e2))

  (* Costrutto AND *)
  | Add(Const n1, Const n2) -> return (Const (n1 + n2)) (* se sono entrambi delle costanti allora si somma senza problemi *)
  | Add ((Const _ as e1), e2) -> (* se sappiamo che solo il primo è una costante allora valutiamo il secondo e se è una costante allora facciamo la somma *)
    let$ e2' = eval_expr state e2 in
    return (Add (e1, e2'))
  | Add (e1, e2) -> (* se nessuno dei due è una costante allora valutiamo prima il primo valore se è una costante eseguira ricorsivamente il caso subito sopra *)
    let$ e1' = eval_expr state e1 in
    return (Add (e1', e2))

  (* Costrutto SUB *)
  | Sub(Const n1, Const n2) -> return (Const (n1 - n2)) (* se sono entrambi delle costanti allora si sottrae senza problemi *)
  | Sub ((Const _ as e1), e2) -> (* se sappiamo che solo il primo è una costante allora valutiamo il secondo e se è una costante allora facciamo la somma *)
    let$ e2' = eval_expr state e2 in
    return (Sub (e1, e2'))
  | Sub (e1, e2) -> (* se nessuno dei due è una costante allora valutiamo prima il primo valore se è una costante eseguira ricorsivamente il caso subito sopra *)
    let$ e1' = eval_expr state e1 in
    return (Sub (e1', e2))

  (* Costrutto MUL *)
  | Mul(Const n1, Const n2) -> return (Const (n1 * n2)) (* se sono entrambi delle costanti allora si moltiplica senza problemi *)
  | Mul ((Const _ as e1), e2) -> (* se sappiamo che solo il primo è una costante allora valutiamo il secondo e se è una costante allora facciamo la somma *)
    let$ e2' = eval_expr state e2 in
    return (Mul (e1, e2'))
  | Mul (e1, e2) -> (* se nessuno dei due è una costante allora valutiamo prima il primo valore se è una costante eseguira ricorsivamente il caso subito sopra *)
    let$ e1' = eval_expr state e1 in
    return (Mul (e1', e2))

  (* Costrutto EQ *)
  | Eq(Const n1, Const n2) -> return (if n1 = n2 then True else False) (* se sono entrambi delle costanti allora si confrontano senza problemi *)
  | Eq ((Const _ as e1), e2) -> (* se sappiamo che solo il primo è una costante allora valutiamo il secondo e se è una costante allora facciamo la somma *)
    let$ e2' = eval_expr state e2 in
    return (Eq (e1, e2'))
  | Eq (e1, e2) -> (* se nessuno dei due è una costante allora valutiamo prima il primo valore se è una costante eseguira ricorsivamente il caso subito sopra *)
    let$ e1' = eval_expr state e1 in
    return (Eq (e1', e2))

  (* Costrutto LEQ *)
  | Leq(Const n1, Const n2) -> return (if n1 <= n2 then True else False) (* se sono entrambi delle costanti allora si confrontano senza problemi *)
  | Leq ((Const _ as e1), e2) -> (* se sappiamo che solo il primo è una costante allora valutiamo il secondo e se è una costante allora facciamo la somma *)
    let$ e2' = eval_expr state e2 in
    return (Leq (e1, e2'))
  | Leq (e1, e2) -> (* se nessuno dei due è una costante allora valutiamo prima il primo valore se è una costante eseguira ricorsivamente il caso subito sopra *)
    let$ e1' = eval_expr state e1 in
    return (Leq (e1', e2))

  

  (* Costrutto CALL *)
  | Call (ide, Const n) ->( (* Prima chiamata della funzione *)
    let$ st = get in (* per ottenere lo stato corrente *)
    let param, body, ret = (apply_fun state ide) in
    let loc = (getloc state) in (* per ottenere l'ultima locazione disponibile, per poi venire allocata  *)
    let env' = (bind_env (topenv state) param (IVar loc)) in (* Associo il parametro della variabile a una locazione di memoria nell'ambiente *)
    let mem' = (bind_mem (getmem state) loc n) in (* Salvo il valore del parametro nella locazione di memoria *)
    (*aggiorno lo stack env con i nuovi identificatori a cui è associata una locazione di memoria
      mem' -> è la memoria aggiornata con il nuovo valore
      loc + 1 -> è la nuova locazione disponibile *)
    let$ _ = set (make_state (env' :: (getenv st)) mem' (loc + 1)) in (* punto in cui aggiorno effettivamente lo stato *)
    return (CallExec (body, ret)) (* mando avanti l'esecuzione della funzione *)
    )
  | Call (ide, e) -> (* Nel caso non siappiamo se 'e' è una costante(quindi un valore) lo valutiamo con eval_expr *)
    let$ e' = eval_expr state e in
    return (Call (ide, e'))

  (* Costrutto CALLEXEC *)
  | CallExec (c, e) ->
    (
      let$ st = get in (* Prendo lo stato attuale *)
      match trace1 (Cmd(c, st)) with (* Faccio uno step e vedo che valore ha *)

      | St st' -> (* Qui ha finito di eseguire il body della funzione *)
        let$ _ = set st' in (* Aggiorna lo stato *)
        return (CallRet e) (* Valuta il valore di ritorno *)

      | Cmd(c', st') -> (* Qui sta ancora eseguendo il body *)
        let$ _ = set st' in (* Aggiorna lo stato *)
        return (CallExec (c', e)) (* Manda avanti l'esecuzione del body *)
    )

  (* Costrutto CALLRET *)
  | CallRet (Const e) ->
    let$ st = get in (* ottengo lo stato attuale *)
    let$ _ = set (setenv st (popenv st)) in (* la funzione è finita quindi ne rimuovo l'env *)
    return (Const e) (* restituisco il valore di ritorno della funzione *)
  | CallRet e -> (* se 'e' non è una Const allora prima lo valutiamo *)
    let$ e1 = eval_expr state e in
    return (CallRet e1)
(* eval_expr: fine *)

(* trace1: inizio *)
(** [trace1 conf] trace1 permette di fare un passo nella small step valutando [conf]  *)
and trace1 = function
  Cmd(c, st) ->
    (match c with
      Skip -> (St st) (* lo stato del programma rimane lo stesso *)
      | Assign (x, e) -> 
        let eval_result = eval_expr st e in (* Qui ottengo la valutazione di 'e' nello stato st, e restituisce una funzione *)
        let result = eval_result st in (* Qui applichiamo la funzione per ottenere oltre che lo stato la valutazione del valore *)
        
        (match result with (* result è una coppia (stato, valore) *)
          | st', Const n -> (* Se l'espressione valutata è uguale ad una costante allora facciamo il bind di quel valore *)
            let st'' = bind_ivar st' x n in (* Qui associamo nella memoria la variabile 'x' con il valore n *)
            St st'' (* Qui restituiamo lo stato con la memoria aggiornata con la nuova variabile *)
        
          | st', e' -> Cmd (Assign (x, e'), st')) (* Se " e' " valutato non è una costante allora restituiamo il comando Assign con l'espressione valutata, 
          che verra evventualmente valutata se l'espressione risulta essere un 'Const' *)
    | Seq(c1, c2) ->(
          let conf' = trace1 (Cmd(c1, st)) in (* esecuzione primo comando della sequenza -> cmd1;cmd2 *)
            match conf' with
              Cmd(cmd', st') -> Cmd(Seq(cmd', c2), st') (* qui sta terminando l'esecuzione del primo cmd *)
            | St s' -> Cmd(c2, s') (* qui inizia l'esecuzione del secondo comando, che seguirà lo stesso percorso del primo *)
        )
    | If(e, c1, c2) -> (
        let eval_result = eval_expr st e in (* Qui valuto l'espressione che mi ritorna una funzione che prendendo lo stato ritorna il valore *)
        let result = eval_result st in (* Qui applico la funzione dandogli lo stato attuale e andando a prendere il valore *)
        match result with (* coppia: (<stato>, <valore_expr>) *)
        | (st', True) -> Cmd(c1, st') (* Se l'espressione è valutata 'True', allora esegui il then *)
        | (st', False) -> Cmd(c2, st') (* Se l'espressione è valutata 'False' allora esegui l'else *)
        | (st', e') -> Cmd(If(e', c1, c2), st') (* Se nessuno dei due casi allora prima valutiamo 'e' per tornare ai casi qui sopra *)
        )
    | While(e, body) -> 
      (*Qui ricreiamo il while tramite il costrutto if,
        dove se 'e' è True allora andrà avanti con il while,
        altrimenti si fermerà come un normale while *)
      Cmd (If (e, Seq (body, c), Skip), st) (* 'c' in questo caso è la chiamata ricorsiva del cmd: While(e, body) *)
      (*
        let eval_result = eval_expr st e in 
        let result = eval_result st in 
        match result with
        | st', True -> Cmd (Seq (cbody, c), st')
        | st', False -> St st'
        | st', e' -> Cmd (While (e', cbody), st'))

        ^^^ This code doesn't work because when it produces the sequence,
        the condition expression has been fully reduced!

        In questo caso questo approccio non funziona perché quando si produce la sequenza, la condizione viene valutata completamente alla prima iterazione,
        perché adesso la condizione al posto di essere "x <= 3" è diventata "False" o "True",
        quindi non si può più valutare per decidere se continuare o meno.

        Con questo trucco dell 'If' si ripropone sempre la stessa condizione passandola sia da valutare sia da riproporre all'iterazione successiva.
    *)  
  )
  | St _ -> raise NoRuleApplies
(* trace1: fine *)

(** [create_list n_steps acc f conf] crea una lista con [conf] che viene valutato costantemente grazie alla [trace1], [acc] è la lista dove vengono accumulati i comandi fino a che [n_steps] non è uguale a 0 *)
let rec create_list n_steps acc trace1 conf = 
  (* va avanti finche non arriva a 0 *)
  if n_steps < 0 
    then List.rev acc (* restituisce la lista di comandi *)
    else 
      try let conf' = trace1 conf in (* se restituisce una configurazione va avanti nella creazione della lista *)
        create_list (n_steps - 1) (conf' :: acc) trace1 conf'
      with _ -> List.rev acc (* se da un eccezione allora si ferma perché il cmd non si può ridurre ulteriormente *)
      
(** [trace n_steps (Prog (ds, c))] è la funzione che chiama la funzione ricorsiva [create_list] *)
let trace (n_steps: int) (Prog (ds, c) : prog) : conf list = 
  (* dentro blocks dovevamo valutare solo un cmd adesso invece dobbiamo valutare anche la 
    lista di dichiarazioni con eval_decl cosi da tenere lo stato coerente *)
  let state0 = eval_decl state0 ds in (* state0: stato di base non inizializzato, ds: lista di dichiarazioni *)
  let conf0 = Cmd (c, state0) in (* c: il comando da valutare, state0: lo stato0 aggiornato con le dichiarazioni *)
    create_list n_steps [] trace1 conf0 (* conf0 è l'interno programma *) 
  

      

              