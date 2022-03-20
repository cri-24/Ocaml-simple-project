type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide (*chiamata dell'identificatore*) | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp 
	| Estring of string 
	| EDict of (ide * exp) list 
	| ApplyOver of exp * exp 
	| Get of exp * ide
	| Set of exp * ide * exp 
	| Remove of exp * ide
	| Clear of exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else (applyenv r x);;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | StringV of string | RecFunVal of ide * evFun 
| DictVal of ( ide * evT )list and evFun = ide * exp * evT env ;;


(*ts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) ;;


(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Estring(s)->StringV(s)|
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
   	Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 |
            		_ -> failwith("non functional value")) |
            		
    EDict(lst)-> if (uniqueKey lst) then DictVal(evallist lst r)  
    			else failwith("error: duplicate key") |
    Get(d,id) -> let dval = eval d r in 
    			(match dval with 
    				DictVal(lst)->lookup id lst|
    				_-> failwith("non DictVal")) |
    Remove(d,id)-> let dval = eval d r in
					(match dval with
					DictVal(lst)->DictVal(remove id lst)|
					_-> failwith("non DictVal")) |
	Clear(d)->let dval = eval d r in
					(match dval with
					DictVal(lst)->DictVal([])|
					_-> failwith("non DictVal"))|
	Set(d,id,v) ->(match (eval d r) with
							DictVal(lst)-> DictVal(reverse (update id (eval v r) (reverse lst)))|
							_-> failwith("non DictVal")) |				   

	ApplyOver(f,d) -> let dval = eval d r in 
    								(match dval with (*Controllo che d sia un dizionario*)
    								DictVal(lst) -> DictVal(applyFunToDict (eval f r) lst)|
    								_-> failwith("non DictVal")) 

and applyFunToDict (f : evT) (lst: (ide * evT) list) : (ide * evT) list =
				(match (f,lst) with
				(f1,[ ])->[ ]
				|(FunVal(arg,body,r),((k,v)::rest)) -> let v1 = try eval body (bind r arg v) with exc -> v in (k,v1)::(applyFunToDict f rest)
				|(RecFunVal(g, (parForm, fBody, fDecEnv)),((k,v)::rest)) -> let v1 = try ( let rEnv = (bind fDecEnv g f) in
																		let aEnv = (bind rEnv parForm v) in eval fBody aEnv ) 
																			with exc -> v in (k,v1)::(applyFunToDict f rest)
				| _ -> failwith("non functional value"))	
							
and evallist (lst : (ide * exp) list) (r : evT env) : (ide * evT) list = match lst with
	[ ] -> [ ] |
	(k, v) :: rest -> (k, eval v r) ::(evallist rest r)


and member (k : ide) (lst : (ide * 'a) list) : bool=
	match lst with
	[ ]->false |
	(k1,v)::rest->if (k = k1) then true else (member k rest)
and lookup (k : ide) (lst : (ide * evT) list) : evT = match lst with
	[ ] -> Unbound |
	(k1, v):: rest -> if (k = k1) then v else (lookup k rest)
and remove (k : ide) (lst : (ide * evT) list) : (ide * evT) list = match lst with
	[ ]->[ ] |
	(k1,v)::rest -> if (k = k1) then rest else (k1,v)::(remove k rest)

and uniqueKey (lst: (ide * exp)list) : bool=
	match lst with
	[ ]->true |
	(k,v)::rest->if (member k rest) then false else (uniqueKey rest)
and  update (k : ide) (v: evT) (lst : (ide * evT) list) : (ide * evT) list=
    match lst with
	[ ]->[(k,v)] |
	(k1,v1)::rest-> if (k = k1) then (k1,v)::rest else (k1,v1)::(update k v rest)
and reverse (lst:(ide * evT) list) : (ide * evT)list = match lst with 
    []->[]  
    |(k,v)::rest->(reverse rest)@[(k,v)] 

;;

(* =============================  TESTS  ================= *)


let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;
eval e2 env0;;

(*TEST NUOVI SUL DIZIONARIO*)

(*EDict*)
let d1 = EDict [("'k1'",Eint 1);("'k2'",Eint 2);("'k3'",Eint 3)];;
eval d1 env0;;
(* d1 = [(k1,1);(k2,2);(k3,3)] *)

(*Get*)
let k1Val = Get(d1,"'k1'");;
eval k1Val env0;;
(* k1Val = 1 *)

(*Set*)
let d2 = Set(d1,"'k0'", Eint 0);; 
(* d2 = [('k0',0);('k1',1);('k2',2);('k3',3)]  *)
eval d2 env0;;
let d2 = Set(d1,"'k0'", Eint 1997);;   
(*caso in cui k0 è già presente e viene sostituito il valore 0 con 1997*)
(* d2 = [('k0',1997);('k1',1);('k2',2);('k3',3)]  *)
eval d2 env0;;
let d3 = Set(d2,"'nome'",Estring "'Giovanni'");;      
(* d3 = [('nome','Giovanni');('k0',1997);('k1',1);('k2',2);('k3',3)] *)
eval d3 env0;;
let d4 = Set(d3,"'matricola'",Eint 123456);;         
(* d4 = [('matricola',123456);('nome',Giovanni);('k0',1997);('k1',1);('k2',2);('k3',3)] *)
eval d4 env0;;
let d10 = Set(d3,"'dizionario'",EDict [("'eta1'" ,Eint 20);("'eta2'" ,Eint 21)]);;         
eval d10 env0;;
(*siccome Edict è un'exp, il dizionario può essere il secondo parametro di una coppia (ide*exp) nella lista*)
(* d10 = [[("'dizionario'", [("'eta1'", Int 20); ("'eta2'", Int 21)]);('matricola',123456);('nome',Giovanni);('k0',1997);('k1',1);('k2',2);('k3',3)] *)

(*Get*)
let nome = Get(d3,"'nome'");;
eval nome env0;;
let matricola = Get(d4,"'matricola'");;
eval matricola env0;;
(* matricola = 123456 *)
let etaVal = Get(d1,"'eta'");; (*UNBOUND VALUE*)
eval etaVal env0;;
(* error: unbound value etaVal *)

(*ApplyOver*)
let incr = Fun("x",Sum(Den "x",Eint 1));; (*Fun applicata solo agli interi*)
let d5 = ApplyOver(incr,d4);;
(* d5 = [('matricola',123457);('nome',Giovanni);('k0',1998);('k1',2);('k2',3);('k3',4)]*)
eval d5 env0;;

(*Clear*)
let d6 = Clear(d1);;
(* d5 = [] *)
(*d6 è vuoto, ma d1 non viene modificato*)
eval d6 env0;; 

(*Remove*)
let d7 = Remove(d1,"'nome'");;    
(*d1 rimane immutato perchè la chiave 'nome' non è presente nel dizionario*)
(* d7 = [('k1', 1); ('k2',2); ('k3',3)] *)
eval d7 env0;;

let d8 = Remove(d5,"'nome'");;    
eval d8 env0;;
(* d8 = [("'matricola'", 123457); ('k0', 1998); ('k1', 2);('k1',3);('k2',4);('k3',5);
  ("'k2'", 3); ("'k3'", 4) *)

