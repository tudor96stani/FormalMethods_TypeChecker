type tPrim = Tint | Tfloat | Tbool| Tvoid 
and
typ = Tprim of tPrim 
      | Tclass of string 
      | Tbot 
and
vall = Vnull 
      | Int of int 
      | Float of float 
      | Bool of bool 
      | Vvoid 
and
blkExp = Bvar of typ*string * exp 
        | Bnvar of exp 
and
varList = exp list
and
exp = Value of vall 
      |Var of string 
      | Vfld of string*string 
      | AsgnV of string*exp
      | AsgnF of string*string*exp 
      | Blk of blkExp
      | Seq of exp*exp
      | If of string*blkExp*blkExp 
      | AddInt of exp*exp
      | MulInt of exp*exp 
      | DiffInt of exp*exp
      | DivInt of exp*exp
      | AddFlt of exp*exp
      | MulFlt of exp*exp
      | DiffFlt of exp*exp
      | DivFlt of exp*exp
      | LglAnd of exp*exp
      | LglOr of exp*exp
      | LglNeg of exp
      | NewObj of string*varList
      | MethInv of string*string*varList
      | WhileExp of string*exp
      | Less of exp*exp
      | LessEq of exp*exp
      | Eq of exp*exp
      | NEq of exp*exp
      | GrEq of exp*exp
      | Gr of exp*exp
      | Cast of string*string
      | InstOf of string*string 
and
mthDecl =(typ*string*fPrmList*blkExp) 
and
fldDecl = typ * string 
and
fPrmList = fPrm list 
and
fPrm = typ*string 
and
mthDeclList = mthDecl list 
and
fldDeclList = fldDecl list 
and
classDecl = (string*string*fldDeclList*mthDeclList) 
and
progr= (string*classDecl) list;;

(* Custom exceptions *)
exception VariableNotDefined of string;;
exception IncompatibleTypes of string;;
exception ClassNotDefined of string;;
exception TypingException of string;;

(*Course example
let () = 
  let _ = If ("m",(Bnvar 
            (AsgnV ("z", (AddInt (Var "z",(Value (Int 1))))))), 
            (Bnvar (AsgnV ("z",(Value (Int 2)) )))
          ) in print_string "abc\n"
*)

(*Class A declaration*)
(*let generateAst = *)
  let a = ("A","Object",[(Tprim (Tint)),"f1"],
    [(Tprim (Tint)),"m1",[((Tprim (Tint)),"a");((Tprim (Tint)),"b")],
      Bvar ((Tprim (Tint)),"c",
        Seq (AsgnV ("c", AddInt(Var ("a"),Var ("b"))), Seq (AsgnF ("this","f1",
                                                            AddInt (Vfld ("this","c"), Var ("c"))), Var ("c")))
    )
    ]) 
    let b = ("B","A",[(Tclass ("A")),"f2"],
              [ (*Method declaration: string (return type) + parameter list + expression*)
                (Tclass ("A")),
                "m2",
                [(Tclass ("A")),"x";(Tclass ("A")),"y"],
                Bvar  
                  ( 
                    (Tclass ("A")), "z",
                    Seq 
                      (Blk 
                        (
                          Bvar 
                          (
                            (Tprim (Tint)), "n", 
                              Seq 
                              (
                                AsgnV ("n",
                                        DiffInt (MethInv ("x","m1",[Value (Int 1); Value (Int 2)]), MethInv ("y","m1",[Value (Int 2); Value (Int 1)]))
                                      ), 
                                Blk 
                                (
                                  Bvar 
                                  (
                                    (Tprim (Tbool)), "m", 
                                    Seq 
                                    (
                                      AsgnV ("m",Gr (DiffInt (Vfld ("x","f1"),Vfld ("y","f1")),Var ("n"))),
                                      If ("m", Bnvar (AsgnV ("z",NewObj ("A",[Var ("m")] )) ), Bnvar (AsgnV ("z",NewObj ("A",[Var ("n")]))))
                                    )
                                  ) 
                                )
                              )
                            )
                          ), 
                        Seq (AsgnF ("this","f2",Var ("z")), Var ("z"))
                      )
                  )
                ] 
              ) 
          
          let main = ("Main","Object",[],
          [(Tprim (Tvoid)),"main",[],
            Bvar(
              (Tclass ("B")), "o1",
              Seq(AsgnV ("o1",NewObj ("B",[Value (Int 0); Value (Vnull)])),
                  Blk (
                    Bvar(
                      (Tclass ("A")), "o2",
                      Seq(AsgnV ("o2",NewObj ("A",[Value (Int 2)])),
                      Blk (
                        Bvar(
                        (Tclass ("A")), "o3",
                          Seq(AsgnV ("o3",NewObj ("A",[Value (Int 3)])),
                              AsgnV ("o2", MethInv ("o1","m2",[Var ("o2"); Var ("o3")]))
                      )
                    )

              )
            )
                    )
                  )
              )
            )
          
          ]);; (*in print_endline "abc"*)

(*Helper functions *)
let print_bool b = match b with |true -> "true" | false -> "false";;

let print_type = function 
	| Tprim (Tint) -> "Tprim (Tint)"
	| Tprim (Tfloat) -> "Tprim (Tfloat)"
	| Tprim (Tbool) -> "Tprim (Tbool)"
	| Tprim (Tvoid) -> "Tprim (Tvoid)"
	| Tbot -> "Tbot"
	| Tclass (cn) -> "Tclass (" ^ cn ^ ")"


(* Check if string cn is the name of a class in prog *)
let rec isClassInProgram prog cn = match prog with 
	| [] -> false
	| h::t -> (
		match h with (n,cl) -> 
			if n=cn
			then true
			else (isClassInProgram t cn)
      );;
      
(* Check if string c1:string a subclass of c2:string in prog *)
let rec isSubclass prog c1 c2 = match prog with
  | [] -> false
  | h::t -> (
    match h with (n,cl) ->
      if n=c1
      then ( match cl with (_,p,_,_) -> p=c2 )
      else (isSubclass t c1 c2)
  );;

(* Check if t1:typ is subtype of t2:typ in prog *)
let subtype prog t1 t2 = match t1,t2 with
	| Tprim(Tint),Tprim(Tint) -> true
	| Tprim(Tfloat),Tprim(Tfloat) -> true
	| Tprim(Tvoid),Tprim(Tvoid) -> true
  | Tprim(Tbool),Tprim(Tbool) -> true
  | Tbot,Tbot -> true
	| Tbot,Tclass(cn) -> (isClassInProgram prog cn)
  | Tclass(cn),Tclass("Object") -> (isClassInProgram prog cn)
  | Tclass(c1),Tclass(c2) when c1=c2 ->  (isClassInProgram prog c1) && (isClassInProgram prog c2)
  | Tclass(c1),Tclass(c2) -> (isClassInProgram prog c1) && (isClassInProgram prog c2) && (isSubclass prog c1 c2)
  
	| _,_ -> false

(* Get the p:string the name of the parent class of cn:string in prog *)
let rec parent prog cn = match prog with 
  | [] -> ""
  | h::t -> (
    match h with (n,cl) -> 
      if n=cn
      then ( match cl with (_,p,_,_) -> p)
      else (parent t cn)
      );;
    
(* Get the list of (typ*string) fields of class cn:string in prog *)
(* Helper method for getting fields *)
let rec getFieldList prog cn = match prog with 
  | [] -> []
  | h::t -> (
    match h with (n,cl) -> 
      if n=cn
      then ( match cl with (_,_,f,_) -> f)
      else (getFieldList t cn)
    );;

(*Least common ancestor:Tclass (x) - the last common element l1:typ list, l2:typ list, considering the starting points a1:string, a2:string *)
let rec lca l1 l2 a1 a2 = match l1,l2 with
  | [],[] -> Tclass("Object")
  | [h],h1::t1 | h1::t1,[h] -> if h <> h1 then Tclass(a1) else Tclass(h)
  | h1::t1,h2::t2 -> if h1 <> h2 then Tclass(a1) else lca t1 t2 h1 h2
  | _,_ -> raise (IncompatibleTypes "The two types have no common ancestor")

(* Get a list of strings representing all ancestors of cn:string from Object *)
let rec getAncestorList prog cn = match cn with
  | "Object" -> ["Object"]
  | cn ->  List.append (getAncestorList prog (parent prog cn)) [cn]


(* Compute a list of (typ*string) fields of class cn:string concatenated with all the fields of its parents' fields *)
(* Main method for getting fields *)
let rec fieldList prog cn = match cn with
  | "Object" -> []
  | i -> List.append (fieldList prog (parent prog i)) (getFieldList prog i)

(* Get the type of variable v:string from the env:(string*typ) list *)
let rec getTypeFromEnv env v = match env with
  | [] -> raise (VariableNotDefined v)
  | (n,tp)::t when n=v -> tp
  | _::t -> getTypeFromEnv t v

(* Get the type of field fl:string for fList:(typ*string) list *)
let rec getFieldType fList fl = match fList with 
  | [] -> raise (VariableNotDefined fl)
  | (tp,n)::t when fl=n -> tp
  | _::t -> getFieldType t fl

(* Compare l1:(typ*string) list with l2:exp list to make sure that l1 is a subtype of l2 elementwise *)
let rec compareFields prog env l1 l2 = match l1,l2 with
  | [],[] -> true
  | (t,n)::t1,(e)::t2 -> let typeOfE = typeCheckExp prog env e in
	if (subtype prog t typeOfE) 
	then true && (compareFields prog env t1 t2)
	else 
	(
		Printf.printf "%s\n" ("Types " ^ (print_type t) ^ " and " ^ (print_type typeOfE) ^ " are not compatible."); 
		false
	)
  | _,_ -> false
and
(* Type check exp:exp from prog considering the environment env:(string*typ) list *)
typeCheckExp prog env exp = match exp with
  | Value (Vnull) -> Tbot
  | Value (Int(v)) -> Tprim(Tint)
  | Value (Float(v)) -> Tprim(Tfloat)
  | Value (Bool(v)) -> Tprim(Tbool)
  | Value (Vvoid) -> Tprim(Tvoid)
  | Var (vn) -> getTypeFromEnv env vn
  | Vfld (cn,f) -> if (isClassInProgram prog cn) then (getFieldType (fieldList prog cn) f) else raise (VariableNotDefined f)
  | AsgnV (vn,e) -> (
      let typeOfVn = (typeCheckExp prog env (Var (vn))) and typeOfE = (typeCheckExp prog env e) in
        if subtype prog typeOfVn typeOfE
          then  Tprim(Tvoid)
          else raise (IncompatibleTypes ("Type " ^ (print_type typeOfVn) ^ " is not compatible with type " ^ (print_type typeOfE)))
      )
  | AsgnF (cn,fn,e) -> if (isClassInProgram prog cn) 
      then let typeOfFn = (getFieldType (fieldList prog cn) fn) and typeOfE = (typeCheckExp prog env e) in
          if subtype prog typeOfFn typeOfE
          then  Tprim(Tvoid)
          else raise (IncompatibleTypes ("Type " ^ (print_type typeOfFn) ^ " is not compatible with type " ^ (print_type typeOfE)))
      else raise (VariableNotDefined (cn ^ "." ^ fn))
  | Blk (Bvar (tp,v,exp)) -> typeCheckExp prog ((v,tp)::env) exp 
  | Blk (Bnvar (exp)) -> typeCheckExp prog env exp
  | Seq (e1,e2) -> let _ = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in typeE2 
  | AddInt (e1,e2) | MulInt (e1,e2) | DiffInt (e1,e2) | DivInt (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
    if (subtype prog typeE1 (Tprim (Tint))) && (subtype prog typeE2 (Tprim (Tint)))
      then (Tprim (Tint))
      else raise (IncompatibleTypes ("Expected Int,Int. Found " ^ (print_type typeE1) ^ "," ^ (print_type typeE2)))
  | AddFlt (e1,e2) | MulFlt (e1,e2) | DiffFlt (e1,e2) | DivFlt (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
      if (subtype prog typeE1 (Tprim (Tfloat))) && (subtype prog typeE2 (Tprim (Tfloat)))
        then (Tprim (Tfloat))
        else raise (IncompatibleTypes ("Expected Float,Float. Found " ^ (print_type typeE1) ^ "," ^ (print_type typeE2)) )
  | LglAnd (e1,e2) | LglOr (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
      if (subtype prog typeE1 (Tprim (Tbool))) && (subtype prog typeE2 (Tprim (Tbool)))
      then (Tprim (Tbool))
      else raise (IncompatibleTypes ("Expected Bool, Bool. Found " ^ (print_type typeE1) ^ "," ^ (print_type typeE2)))
  | LglNeg (e) -> let te = typeCheckExp prog env e in 
      if (subtype prog te (Tprim (Tbool))) 
      then (Tprim (Tbool))
      else raise (IncompatibleTypes ("Logical Not cannot be applied to type " ^ (print_type te)))
  | Less(e1,e2) | LessEq(e1,e2) | Eq (e1,e2) | NEq (e1,e2) | GrEq (e1,e2) | Gr (e1,e2) ->
    let t1 = (typeCheckExp prog env e1) and t2 = (typeCheckExp prog env e2) in
    if ((subtype prog t1 t2) 
      && (subtype prog t2 t1)
       && (
        match t1,t2 with
        | Tclass (c1),Tclass (c2) -> (not (isClassInProgram prog c1)) && (not (isClassInProgram prog c2))
        | Tclass (c), _ -> not (isClassInProgram prog c) 
        | _, Tclass (c) ->  not (isClassInProgram prog c) 
        | _ -> true
      )) then (Tprim (Tbool))
      else raise (IncompatibleTypes ("Cannot apply boolean expression to types " ^ (print_type t1) ^ " and " ^ (print_type t2)))
  | If (v,e1,e2) -> 
    let tv= (subtype prog (typeCheckExp prog env (Var (v))) (Tprim (Tbool))) and te1 = (typeCheckExp prog env (Blk (e1)))
       and te2 = (typeCheckExp prog env (Blk (e2))) in 
       if tv 
       then 
       (
          match te1,te2 with 
          | Tprim (Tint),Tprim (Tint) -> Tprim (Tint)
          | Tprim (Tfloat),Tprim (Tfloat) -> Tprim (Tfloat)
          | Tprim (Tbool),Tprim (Tbool) -> Tprim (Tbool)
          | Tprim (Tvoid),Tprim (Tvoid) -> Tprim (Tint)
          | Tbot, Tbot -> Tbot
          | Tclass (c1), Tclass(c2) -> lca (getAncestorList prog c1) (getAncestorList prog c2) "Object" "Object"
          | _,_ -> raise (IncompatibleTypes ("Both branches must return the same type or subtypes of the same type. " ^ (print_type te1) ^ " and " ^ (print_type te2) ^ " are not compatible"))
       )
       else raise (IncompatibleTypes (v ^ " must be of type bool"))
    | Cast (cn,v) -> let t = (typeCheckExp prog env (Var (v))) in
        if (isClassInProgram prog cn) && ((subtype prog (Tclass(cn)) t) || (subtype prog t (Tclass (cn)))) 
        then Tclass(cn)
        else raise (IncompatibleTypes ("Cannot cast from " ^ (print_type t) ^ " to Tclass(" ^ cn ^ "). Types not compatible"))
    | InstOf (v,cn) -> let t = (typeCheckExp prog env (Var (v))) in
        if (isClassInProgram prog cn) && ((subtype prog (Tclass(cn)) t) || (subtype prog t (Tclass (cn)))) 
        then Tprim (Tbool)
        else raise (IncompatibleTypes ("Types Tclass" ^ cn ^ " and " ^ (print_type t) ^ " are not compatible. Cannot apply InstanceOf"))
    | NewObj (cn,vl) ->
        if (isClassInProgram prog cn)
        then
        (
          let fldlst = fieldList prog cn in
            if compareFields prog env fldlst vl
            then Tclass(cn)
            else raise (IncompatibleTypes ("Constructor of class " ^ cn ^ " did not receive the correct parameter types"))
        )
        else raise (ClassNotDefined ("Class " ^ cn ^ " is not defined in the program"))
    | WhileExp (v,e) -> 
      let tv= (subtype prog (typeCheckExp prog env (Var (v))) (Tprim (Tbool))) and _ = (typeCheckExp prog env e) in
        if tv 
        then Tprim (Tvoid) 
        else raise (IncompatibleTypes (v ^ " must be of type bool"))
    | _ -> raise (TypingException "Expression is not well typed")  


let ast = [("A",a);("B",b);("Main",main)]  
(* let () = let ast = [("A",a);("B",b);("Main",main)] in 
	Printf.printf "%s\n\n" (print_bool (subtype ast (Tclass ("A")) (Tclass ("Object") ))) *)

let () = 
	let typeOfExpression = typeCheckExp ast ["m",Tprim (Tbool);"z",Tclass ("A")] (If ("m", Bnvar (AsgnV ("z",NewObj ("A",[Var ("m")] )) ), Bnvar (AsgnV ("z",NewObj ("A",[Var ("n")])))))  in 
		Printf.printf "%s\n" (print_type typeOfExpression); Printf.printf "\nOK\n\n"
