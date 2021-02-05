type ide = string;;

(* Valori che rappresentano tipi *)
type tval = 
	| TInt
	| TBool
	| TString
	| TSet of tval
	| TFun of tval * tval
	| TUnbound;;
	
(* Typechecker per gli Insiemi *)
let setTypeCheck t =
	match t with
	| TInt -> t
	| TBool -> t
	| TString -> t
	| _ -> failwith ("typeSwitch: not a valid type");;
	
(* Albero di Sintassi Astratta *)
type texp =
	| CstInt of int
	| CstTrue
	| CstFalse
	| CstString of string
	| Den of ide
	| Sum of texp * texp
	| Sub of texp * texp
	| Times of texp * texp
	| Ifthenelse of texp * texp * texp
	| Eq of texp * texp
	| Let of ide * texp * texp
	| Fun of ide * tval * texp
	| Letrec of ide * ide * tval * tval * texp * texp
	| Apply of texp * texp
	(*| Empty of tval*)
	| Singleton of tval * texp
	| Of of tval * args
	| IsEmpty of texp
	| ExistsIn of texp * texp
	| Contains of texp * texp
	| Add of texp * texp
	| Remove of texp * texp
	| Union of texp * texp
	| Intersection of texp * texp
	| Difference of texp * texp
	| Max of texp
	| Min of texp
	| For_all of texp * texp
	| Exists of texp * texp
	| Filter of texp * texp
	| Map of texp * texp
and args =
	| Elem of texp * args
	| Nil;;
	
type 't tenv = (string * 't) list;;

(* Operazioni sull'ambiente *)
let emptyEnv = [("", TUnbound)];;

let bind (s:tval tenv) (i:string) (x:tval) = (i,x) :: s;;

let rec lookup (s:tval tenv) (i:string) =
    match s with
    | [] ->  TUnbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;
	
(* Interprete per la valutazione del tipo delle espressioni *)
let rec teval (e:texp) (s:tval tenv) =
    match e with
    | CstInt(n) -> TInt
    | CstTrue -> TBool
    | CstFalse -> TBool
    | CstString(x) -> TString
    | Den(i) -> lookup s i
    | Eq(e1,e2) -> 
		if(teval e1 s) = (teval e2 s) then TBool 
		else failwith("Eq:not a valid type")
    | Times(e1,e2) ->
		(match ((teval e1 s),(teval e2 s)) with
        | (TInt, TInt) -> TInt
        | (_,_) -> failwith("Times:not a valid type"))		
	| Sum(e1,e2) ->
		(match ((teval e1 s),(teval e2 s)) with
        | (TInt, TInt) -> TInt
        | (_,_) -> failwith("Sum:not a valid type"))		
	| Sub(e1,e2) ->
        (match ((teval e1 s),(teval e2 s)) with
        | (TInt, TInt) -> TInt
        | (_,_) -> failwith("Sub:not a valid type"))
    | Ifthenelse(e1,e2,e3) ->
        (match ((teval e1 s), ((teval e2 s)=(teval e3 s))) with
        | (TBool, true) -> teval e2 s
        | (_,_) -> failwith("Ifthenelse:non boolean guard or expressions of different types"))
    | Let(i, e, ebody) -> teval ebody (bind s i (teval e s))
    | Fun(arg, t, ebody) -> let tenv1 = bind s arg t in
							let t1 = teval ebody tenv1 in TFun(t,t1)
    | Letrec(f, arg, t, rType, fBody, lBody) ->
        let fEnv = bind s f (TFun(t,rType)) in
        let aEnv = bind fEnv arg t in
        let t = teval fBody aEnv in
        if t = (teval lBody aEnv) then t else failwith("Letrec:not a valid type")
    | Apply(eF, eArg) -> let f = teval eF s in
						(match f with	
						TFun(t,t1)	->	if ((teval eArg s) = t1)
										then t1 else failwith("error")
							|_ -> failwith("error") )
        
    | Singleton(t,v) ->
        if (teval v s) = setTypeCheck t
        then TSet(t)
        else failwith("Singleton:not a valid type")
    | Of(t,argL) -> 
        let t' = setTypeCheck t in
        let rec checkList args =
            (match args with
            | Elem(v,argL) -> if (teval v s) = t' then checkList argL else failwith("Of:not a valid type")
            | Nil -> TSet(t'))
        in checkList argL
    | Max(set) ->
		(match teval set s with
        | TSet(TInt) -> TInt
        | _ -> failwith("MaxOf:not a valid type"))
	| Min(set) ->
        (match teval set s with
        | TSet(TInt) -> TInt
        | _ -> failwith("MinOf:not a valid type"))
    | IsEmpty(set) ->
        (match teval set s with
        | TSet(TInt) | TSet(TBool) | TSet(TString) -> TBool
        | _ -> failwith("IsEmpty:not a valid type"))
    | ExistsIn(v,set) ->
        (match (teval v s, teval set s) with
        | (t, TSet(t')) -> if t = t' then TBool else failwith("ExistsIn:not a valid type")
        | (_,_) -> failwith("ExistsIn:not a valid type"))
    | Contains(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) -> if t1 = t2 then TBool else failwith("ExistsIn:not a valid type")
        | (_,_) -> failwith("Contains:not a valid type"))
    | Add(v,set) ->
		(match (teval v s, teval set s) with	
        | (t, TSet(t')) -> if t = t' then TSet(t) else failwith("Add:not a valid type")
        | (_,_) -> failwith("Add:not a valid type"))	
	| Remove(v,set) ->
        (match (teval v s, teval set s) with
        | (t, TSet(t')) -> if t = t' then TSet(t) else failwith("Remove:not a valid type")
        | (_,_) -> failwith("Remove:not a valid type"))
    | Union(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) ->
            if t1 = t2 then TSet(t1)
            else failwith("Union:not a valid type")
        | (_,_) -> failwith("Union:not a valid type"))	
	| Intersection(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) ->
            if t1 = t2 then TSet(t1)
            else failwith("Intersection:not a valid type")
        | (_,_) -> failwith("Intersection:not a valid type"))	
	| Difference(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) ->
            if t1 = t2 then TSet(t1)
            else failwith("Difference:not a valid type")
        | (_,_) -> failwith("Difference:not a valid type"))
    | For_all(pred,set) ->
        (match (teval pred s, teval set s) with
        | (TFun(t1,t2), TSet(t)) ->
            if (t = t1) && (t2 = TBool) then TBool
            else failwith("Filter/Exists/For_all:not a valid type")
        | (_,_) -> failwith("For_all:not a valid type"))	
	| Exists(pred,set) ->
        (match (teval pred s, teval set s) with
        | (TFun(t1,t2), TSet(t)) ->
            if (t = t1) && (t2 = TBool) then TBool
            else failwith("Filter/Exists/For_all:not a valid type")
        | (_,_) -> failwith("Exists:not a valid type"))	
	| Filter(pred,set) ->
        (match (teval pred s, teval set s) with
        | (TFun(t1,t2), TSet(t)) ->
            if (t = t1) && (t2 = TBool) then TBool
            else failwith("Filter/Exists/For_all:not a valid type")
        | (_,_) -> failwith("Filter:not a valid type"))
    | Map(func,set) -> 
        (match (teval func s, teval set s) with
        | (TFun(t1,t2), TSet(t)) -> if t = t1 then t2 else failwith("Map:not a valid type")
        | (_,_) -> failwith("Map:not a valid type"));;

(**************************************** TEST CASE****************************************)		
(* Creazione degli Insiemi *)
let env = emptyEnv;;
let setInt = Of(TInt, Elem(CstInt(5),Elem(CstInt(2),Elem(CstInt(4),Elem(CstInt(6),Nil)))));; (*{ 5,2,4,6 }*)
let setInt2 = Of(TInt, Elem(CstInt(1),Elem(CstInt(2),Nil)));; (*{ 1,2 }*)
let setStr = Singleton(TString, CstString("Programmazione"));; (*{ "Programmazione" }*)
print_string " -  setInt " ; teval setInt env;;
print_string " -  setInt2 " ; teval setInt2 env;;
print_string " -  setStr " ; teval setStr env;;

(* Operazioni di aggiunta/rimozione elementi *)
let setInt1 = Add(CstInt(8), Remove(CstInt(2), Add(CstInt(3), setInt)));; (*{ 5,4,6,8,3 }*)
let setStr = Add(CstString("II"), setStr);; (*{ "II" }*)
print_string " -  setInt1 = Add(CstInt(8), Remove(CstInt(2), Add(CstInt(3), setInt))) " ; teval setInt1 env;; (*{ 5,4,6,8,3 }*)
print_string " -  setStr = Add(CstString("II"), setStr) " ; teval setStr env;; (*{ "Programmazione II" }*)

(* Operazioni di controllo *)
print_string " -  IsEmpty(setInt) " ; teval (IsEmpty(setInt)) env;; (*{ False }*)
print_string " -  ExistsIn(CstInt(1), setInt1) " ; teval (ExistsIn(CstInt(1), setInt1)) env;; (*{ "False" }*)
print_string " -  ExistsIn(CstInt(8), setInt1) " ; teval (ExistsIn(CstInt(8), setInt1)) env;; (*{ "True" }*)
print_string " -  Contains(setInt1, setInt2) " ; teval (Contains(setInt1, setInt2)) env;; (*{ "False" }*)

(* Operazioni su Insiemi *)
let setI = Intersection(setInt1, setInt2);; (*{ }*)
let setU = Union(setInt1, setInt2);; (*{ 5,4,6,8,3,1,2 }*)
let setD = Difference(setInt1, setInt2);; (*{ 5,4,6,8,3 }*)
print_string " -  Intersection(setInt1, setInt2) " ; teval setI env;;
print_string " -  Union(setInt1, setInt2) " ; teval setU env;;
print_string " -  Difference(setInt1, setInt2) " ; teval setD env;;

(* Ricerca di Max e Min in un Insieme *)
print_string " -  Max(setInt) " ; teval (Max(setInt)) env;; (*{ 8 }*)
print_string " -  Min(setInt) " ; teval (Min(setInt)) env;; (*{ 3 }*)
print_string " -  Max(setI) " ; teval (Max(setI)) env;;
print_string " -  Min(setI) " ; teval (Min(setI)) env;;

(* Operazioni Funzionali *)
let pred_is2 = Fun("x", TInt, Ifthenelse(Eq(Den("x"),CstInt(4)),
                                CstTrue,
                                CstFalse));;
let fBitMap_2 = Fun("x", TInt, Times(Den("x"), CstInt(4)));;

print_string " -  For_all(pred_is2, setInt1) " ; teval (For_all(pred_is2, setInt1)) env;;
print_string " -  Exists(pred_is2, setInt1) " ; teval (Exists(pred_is2, setInt1)) env;;
print_string " -  Filter(pred_is2, setInt1) " ; teval (Filter(pred_is2, setInt1)) env;;
print_string " -  Map(fBitMap_2, setInt1) " ; teval (Map(fBitMap_2, setInt1)) env;;

print_string " -  For_all(pred_is2, setI) " ; teval (For_all(pred_is2, setI)) env;;
print_string " -  Exists(pred_is2, setI) " ; teval (Exists(pred_is2, setI)) env;;
print_string " -  Filter(pred_is2, setI) " ; teval (Filter(pred_is2, setI)) env;;
print_string " -  Map(fBitMap_2, setI) " ; teval (Map(fBitMap_2, setI)) env;;