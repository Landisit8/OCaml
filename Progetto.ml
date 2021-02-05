type ide = string;;

(* Tipi di Insieme *)
type typeSet =
	| String
    | Int
    | Bool
	
(* Albero di Sintassi Astratta *)
type exp =
    | CstInt of int
    | CstTrue 
    | CstFalse
    | CstString of string
    | Den of ide
    | Sum of exp * exp
    | Sub of exp * exp
    | Times of exp * exp
    | Ifthenelse of exp * exp * exp
    | Eq of exp * exp
    | Let of ide * exp * exp
    | Fun of ide * exp
    | Letrec of ide * ide * exp * exp
    | Apply of exp * exp
	(* *)
	| Empty of string
	| IsEmpty of exp
	| Singleton of string * exp
	| Of of string * args
	| ExistsIn of exp * exp
	| Contains of exp * exp
	| Add of exp * exp
	| Remove of exp * exp
	| Union of exp * exp
	| Intersection of exp * exp
	| Difference of exp * exp
	| Max of exp
	| Min of exp
	| For_all of exp * exp
	| Exists of exp * exp
	| Filter of exp * exp
	| Map of exp * exp
and args =
	| Elem of exp * args
	| Nil;;

(* Definizione dell'Ambiente + Operazioni sull'Ambiente *)
type 'v env = (string * 'v) list;;

(* Valori che rappresentano tipi *)
type evT =
	| Int of int
	| Bool of bool
	| String of string
	| Set of string * evT list
	| Closure of ide * exp * evT env
	| RecClosure of ide * ide * exp * evT env
	| Unbound;;

let emptyEnv = [("", Unbound)];;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) =
    match s with
	| [] ->  Unbound
	| (j,v)::sl when j = i -> v
	| _::sl -> lookup sl i;;

(* Typechecker per gli Insiemi *)
let typecheck ((x:string),(y:evT)) =
    match x with	
		| "int" ->  
			(match y with 
                | Int(u) -> true
                | _ -> false)
		| "bool" -> 
			(match y with 
                | Bool(u) -> true
                | _ -> false)
		| "set" -> 
			(match y with
				| Set(l1,t1) -> true
				| _ -> false)
		| "string" -> 
			(match y with 
                | String(u) -> true
                | _ -> false)
		| _ -> failwith("typecheck: not a valid type");;
	
(* Operazioni sugli interi *)
let int_eq(x,y) =   
	match (typecheck("int",x), typecheck("int",y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool(v = w)
	| (_,_,_,_) -> failwith("run-time error ");;
       
let int_plus(x, y) = 
	match(typecheck("int",x), typecheck("int",y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v + w)
	| (_,_,_,_) -> failwith("run-time error ");;

let int_sub(x, y) = 
	match(typecheck("int",x), typecheck("int",y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v - w)
	| (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = 
	match(typecheck("int",x), typecheck("int",y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v * w)
	| (_,_,_,_) -> failwith("run-time error ");;
	
let typeof (v : evT)=
	match v with 
	|Int(x) -> "Int"
	|String(x) -> "String"
	|Bool(x) -> "Bool"
	|_ -> failwith("runtime-error");;
	
(*Lavorare su insiemi*)
let emptySet (t : string) = Set(t,[]);;

(*n3 se esiste*)	
let set_existsIn (v:evT) (set:evT) =
    match (typecheck("set",set), set) with
	| (true, Set(t,l)) -> 
		let rec search v l =
			(match l with
			| h::tail -> if h = v then true else search v tail
			| [] -> false)
		in search v l
	| (_,_) -> failwith("Not a valid type");;

(*n1 inserire*)
let set_add (v:evT) (set:evT) =
    match (set_existsIn v set, set) with
    | (true, Set(t,l)) -> Set(t,l)
    | (false, Set(t,l)) -> Set(t,v::l)
    | (_,_) -> failwith("Not a valid type");;
	
let set_singleton (t:string) (v:evT) = Set(t, [v]);;

(*n1 rimuovere*)
let rec deleteVal (v:evT) (l:evT list) =
	(match l with
	| h::tail -> if h <> v then h::(deleteVal v tail) else deleteVal v tail
	| [] -> []);;

let set_remove (v:evT) (set:evT) = 
    match (typecheck("set",set), set) with
    | (true, Set(t,l)) -> Set(t,deleteVal v l)
    | (_,_) -> failwith("Not a valid type");;

(*n2 vuoto*)
let set_isEmpty (set:evT) =
    match set with
	| Set(t,l) -> if l = [] then Bool(true) else Bool(false)
	| _ -> failwith("Not a valid type");;

(*n4 sottoinsieme*)
let rec contains l l1 t=
	(match l1 with
	| h::tail -> if set_existsIn h (Set(t,l)) then contains l tail t else false
	| [] -> true);;

let rec set_contains (set:evT) (set1:evT) =
	match (set, set1) with
	| (Set(t,l), Set(t1,l1)) -> contains l l1 t  
	| (_,_) -> failwith("not a valid type");;
	
(*n5 max & min*)
let rec maxInt (l , m) =
	match l with
	| h::tail ->
			(match h with
			|Int(v) -> if v > m then maxInt (tail , v) else maxInt (tail , m)
			| _ -> failwith("Maxi, not valid type"))
	| [] -> m;;
	
let set_max (set:evT) =
	match set with
	|Set(t,l) -> if t = "Int" then Int(maxInt (l , 0)) else failwith("setMax, Not a valid type")
	| _ -> failwith("setMax1, not valid type");;

let rec minInt (l , min) =
	match l with
	|  h::tail ->
			(match h with
			|Int(v) -> if v < min then minInt (tail , v) else minInt (tail , min)
			| _ -> failwith("minInt, not valid type"))
	| [] -> min;;
	
let set_min (set:evT) =
	match set with
	|Set(t,l) -> if t = "Int" then Int(minInt (l , 0)) else failwith("setMin, Not a valid type")
	| _ -> failwith("setMin, not valid type");;

(*Union*)
let rec deleteDuplicates (t:string) l lret =
    match l with
    | h::tail -> if set_existsIn h (Set(t,tail)) then deleteDuplicates t tail lret else deleteDuplicates t tail (h::lret)
    | [] -> lret;;

let set_union (set1:evT) (set2:evT) =
	match ( set1, set2) with
	| (Set(t1, l1), Set(t2,l2)) ->
		if t1=t2 then Set(t1, deleteDuplicates t1 (l1@l2) [])
		else failwith("Union: not valid type")
	| (_,_) -> failwith("union1, not a valid type");;
	
(*intersection*)
let rec elementsCom (t:string) l1 l2 lret =
    match l1 with
    | h::tail -> if set_existsIn h (Set(t,l2)) then elementsCom t tail l2 (h::lret) else elementsCom t tail l2 lret
    | [] -> lret;;
	
let set_intersection (set1:evT) (set2:evT) =
	match (set1, set2) with
	| (Set (t1,l1), Set(t2,l2)) ->
		if t1=t2 then Set(t1,elementsCom t1 l1 l2 [])
		else failwith("set_intersection, not a valid type")
	|(_,_) -> failwith("set_intersection1, not a valid type");;
	
(*Difference*)
let rec notElementsCom (t:string) l1 l2 lret =
    match l1 with
    | h::tail ->
        if set_existsIn h (Set(t,l2)) then notElementsCom t tail l2 lret
        else notElementsCom t tail l2 (h::lret)
    | [] -> lret;;

let set_difference (set1:evT) (set2:evT) = 
    match (set1, set2) with
    | (Set(t1,l1), Set(t2,l2)) ->
        if t1 = t2 then Set(t1, notElementsCom t1 l1 l2 [])
        else failwith("set_difference: not a valid type")
    | (_,_) -> failwith("set_difference1: not a valid type");;	

(* Interprete per la valutazione del tipo delle espressioni *)
let rec eval  (e:exp) (s:evT env) = match e with
	| CstInt(n) -> Int(n)
	| CstTrue -> Bool(true)
	| CstFalse -> Bool(false)
	| CstString(s) -> String(s)
	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	| Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                (match (typecheck("bool", g), g) with
			| (true, Bool(true)) -> eval e2 s
                        | (true, Bool(false)) -> eval e3 s
                	| (_, _) -> failwith ("nonboolean guard"))
	| Den(i) -> lookup s i
	| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
	| Fun(arg, ebody) -> Closure(arg,ebody,s)
	| Letrec(f, arg, fBody, letBody) -> 
		let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
			eval letBody benv
	| Apply(eF, eArg) ->
		let fclosure = eval eF s in 
         (match fclosure with 
           | Closure(arg, fbody, fDecEnv) ->
             let aVal = eval eArg s in
	      let aenv = bind fDecEnv arg aVal in 
                eval fbody aenv
           | RecClosure(f, arg, fbody, fDecEnv) ->
             let aVal = eval eArg s in
               let rEnv = bind fDecEnv f fclosure in
	          let aenv = bind rEnv arg aVal in 
                    eval fbody aenv
           | _ -> failwith("non functional value")) 
    | Empty(t) -> emptySet (t)
    | Singleton(t,v) -> set_singleton t (eval v s)
	| Add(v,set) -> set_add (eval v s) (eval set s)
	| Remove(v,set) -> set_remove (eval v s) (eval set s)
	| IsEmpty(set) -> set_isEmpty (eval set s)
    | ExistsIn(v,set) -> Bool(set_existsIn (eval v s) (eval set s))
	| Contains(set,set1) -> Bool(set_contains (eval set s) (eval set1 s))
	| Max(set) -> set_max (eval set s)
    | Min(set) -> set_min (eval set s)
	| Union(set1,set2) -> set_union (eval set1 s) (eval set2 s)
    | Intersection(set1,set2) -> set_intersection (eval set1 s) (eval set2 s)
    | Difference(set1,set2) -> set_difference (eval set1 s) (eval set2 s)
	| For_all(f, e) -> for_all((eval f s), (eval e s))
	| Exists(f, e) -> exists((eval f s), (eval e s))
	| Filter(f, e) -> filter((eval f s), (eval e s))
	| Map(f, e) -> map((eval f s), (eval e s)) 
	| Of (t, args) -> let rec setGenerator v l =
						match v with
						|Elem(x, Nil) -> if typeof(eval x s) = t then ((eval x s)::l) 
							else failwith("Error")
						|Elem(x, Elem(y,z)) -> if typeof (eval x s) = t then setGenerator (Elem(y,z)) ((eval x s)::l)
						else failwith("error")
						|Nil -> l
		in let listVar = setGenerator args [] 
		in Set (t, listVar)	
		
and	for_all (pred,set) =
		match (pred,set) with
		|(Closure(arg,fbody,fDecEnv),Set(t,l)) -> 
			let rec auxForAll(var,body, env, l, ris) =
			match l with
			| x::xs -> 
				let envVar = bind env var x in 
				let ris = eval fbody envVar in 
				if ris = Bool(true) then auxForAll(var,body,env,xs,ris) 
				else Bool(false)
			|[]->ris
			in auxForAll(arg,fbody,emptyEnv,l,(Bool(false)))
		|(_,_) -> failwith("runtime-error")
		
and	exists (pred,set) =
		match (pred,set) with
		|(Closure(arg,fbody,fDecEnv),Set(t,l)) -> 
			let rec auxExists(var,body, env, l, ris) =
			match l with
			| x::xs -> 
				let envVar = bind env var x in 
				let ris = eval fbody envVar in 
				if ris = Bool(false) then auxExists(var,body,env,xs,ris) 
				else Bool(true)
			|[]->ris
			in auxExists(arg,fbody,emptyEnv,l,(Bool(false)))
		|(_,_) -> failwith("runtime-error")
		
and	filter (pred,set) =
		match (pred,set) with
		|(Closure(arg,fbody,fDecEnv),Set(t,l)) -> 
			let rec auxFilter(var,body, env, l, ris_set, t) =
			match l with
			| x::xs -> 
				let envVar = bind env var x in 
				let ris = eval fbody envVar in 
				if ris = Bool(true) then auxFilter(var,body,env,xs,(x::ris_set),t) 
				else auxFilter(var,body,env,xs,ris_set,t)
			|[]->Set(t,ris_set)
			in auxFilter(arg,fbody,emptyEnv,l,[],t)
		|(_,_) -> failwith("runtime-error") 

and	map (func,set) =
		match (func,set) with
		|(Closure(arg,fbody,fDecEnv),Set(t,l)) -> 
			let rec auxMap(var,body, env, l, ris_set, t) =
			match l with
			| x::xs -> 
				let envVar = bind env var x in 
				auxMap(var,body,env,xs, (eval fbody envVar::ris_set),t)
			|[]->Set("Bool",ris_set)
			in auxMap(arg,fbody,emptyEnv,l,[],t)
		|(_,_) -> failwith("runtime-error")
		
(**************************************** TEST CASE****************************************)		
(* Creazione degli Insiemi *)
let env = emptyEnv;;
let setInt = Of("Int", Elem(CstInt(5),Elem(CstInt(2),Elem(CstInt(4),Elem(CstInt(6),Nil)))));; (*{ 5,2,4,6 }*)
let setInt2 = Of("Int", Elem(CstInt(1),Elem(CstInt(2),Nil)));; (*{ 1,2 }*)
let setStr = Singleton("String", CstString("Programmazione"));; (*{ "Programmazione" }*)
print_string " -  setInt " ; eval setInt env;;
print_string " -  setInt2 " ; eval setInt2 env;;
print_string " -  setStr " ; eval setStr env;;

(* Operazioni di aggiunta/rimozione elementi *)
let setInt1 = Add(CstInt(8), Remove(CstInt(2), Add(CstInt(3), setInt)));; (*{ 5,4,6,8,3 }*)
let setStr = Add(CstString("II"), setStr);; (*{ "II" }*)
print_string " -  setInt1 = Add(CstInt(8), Remove(CstInt(2), Add(CstInt(3), setInt))) " ; eval setInt1 env;; (*{ 5,4,6,8,3 }*)
print_string " -  setStr = Add(CstString(II), setStr) " ; eval setStr env;; (*{ "Programmazione II" }*)

(* Operazioni di controllo *)
print_string " -  IsEmpty(setInt) " ; eval (IsEmpty(setInt)) env;; (*{ False }*)
print_string " -  ExistsIn(CstInt(1), setInt1) " ; eval (ExistsIn(CstInt(1), setInt1)) env;; (*{ "False" }*)
print_string " -  ExistsIn(CstInt(8), setInt1) " ; eval (ExistsIn(CstInt(8), setInt1)) env;; (*{ "True" }*)
print_string " -  Contains(setInt1, setInt2) " ; eval (Contains(setInt1, setInt2)) env;; (*{ "False" }*)

(* Operazioni su Insiemi *)
let setI = Intersection(setInt1, setInt2);; (*{ }*)
let setU = Union(setInt1, setInt2);; (*{ 5,4,6,8,3,1,2 }*)
let setD = Difference(setInt1, setInt2);; (*{ 5,4,6,8,3 }*)
print_string " -  Intersection(setInt1, setInt2) " ; eval setI env;;
print_string " -  Union(setInt1, setInt2) " ; eval setU env;;
print_string " -  Difference(setInt1, setInt2) " ; eval setD env;;

(* Ricerca di Max e Min in un Insieme *)
print_string " -  Max(setInt) " ; eval (Max(setInt)) env;; (*{ 8 }*)
print_string " -  Min(setInt) " ; eval (Min(setInt)) env;; (*{ 3 }*)
print_string " -  Max(setI) " ; eval (Max(setI)) env;;
print_string " -  Min(setI) " ; eval (Min(setI)) env;;

(* Operazioni Funzionali *)
let pred_is4 = Fun("x", Ifthenelse(Eq(Den("x"),CstInt(4)),
                                CstTrue,
                                CstFalse));;
let fBitMap_4 = Fun("x", Times(Den("x"), CstInt(4)));;

print_string " -  For_all(pred_is4, setInt1) " ; eval (For_all(pred_is4, setInt1)) env;;
print_string " -  Exists(pred_is4, setInt1) " ; eval (Exists(pred_is4, setInt1)) env;;
print_string " -  Filter(pred_is4, setInt1) " ; eval (Filter(pred_is4, setInt1)) env;;
print_string " -  Map(fBitMap_4, setInt1) " ; eval (Map(fBitMap_4, setInt1)) env;;

print_string " -  For_all(pred_is4, setI) " ; eval (For_all(pred_is4, setI)) env;;
print_string " -  Exists(pred_is4, setI) " ; eval (Exists(pred_is4, setI)) env;;
print_string " -  Filter(pred_is4, setI) " ; eval (Filter(pred_is4, setI)) env;;
print_string " -  Map(fBitMap_4, setI) " ; eval (Map(fBitMap_4, setI)) env;;
