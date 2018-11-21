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
      | WhileExp of string*string
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
exception VariableNotDefined of string;;
exception IncompatibleTypes of string;;
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

let print_bool b = match b with |true -> "true" | false -> "false";;

let rec isClassInProgram prog cn = match prog with 
	| [] -> false
	| h::t -> (
		match h with (n,cl) -> 
			if n=cn
			then true
			else (isClassInProgram t cn)
      );;
      
let rec isSubclass prog c1 c2 = match prog with
  | [] -> false
  | h::t -> (
    match h with (n,cl) ->
      if n=c1
      then ( match cl with (_,p,_,_) -> p=c2 )
      else (isSubclass t c1 c2)
  );;

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

let rec parent prog cn = match prog with 
  | [] -> ""
  | h::t -> (
    match h with (n,cl) -> 
      if n=cn
      then ( match cl with (_,p,_,_) -> p)
      else (parent t cn)
      );;
    
let rec getFieldList prog cn = match prog with 
  | [] -> []
  | h::t -> (
    match h with (n,cl) -> 
      if n=cn
      then ( match cl with (_,_,f,_) -> f)
      else (getFieldList t cn)
    );;


let rec fieldList prog cn = match cn with
  | "Object" -> []
  | i -> List.append (fieldList prog (parent prog i)) (getFieldList prog i)

let rec getTypeFromEnv env v = match env with
  | [] -> raise (VariableNotDefined v)
  | (n,tp)::t when n=v -> tp
  | _::t -> getTypeFromEnv t v

let rec getFieldType fList fl = match fList with 
  | [] -> raise (VariableNotDefined fl)
  | (tp,n)::t when fl=n -> tp
  | _::t -> getFieldType t fl

let rec typeCheckExp prog env exp = match exp with
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
          else raise (IncompatibleTypes "BAGAM AICI CEVA")
      )
  | AsgnF (cn,fn,e) -> if (isClassInProgram prog cn) 
      then let typeOfFn = (getFieldType (fieldList prog cn) fn) and typeOfE = (typeCheckExp prog env e) in
          if subtype prog typeOfFn typeOfE
          then  Tprim(Tvoid)
          else raise (IncompatibleTypes "BAGAM AICI CEVA")
      else raise (VariableNotDefined fn)
  | Blk (Bvar (tp,v,exp)) -> typeCheckExp prog ((v,tp)::env) exp 
  | Blk (Bnvar (exp)) -> typeCheckExp prog env exp
  | Seq (e1,e2) -> let _ = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in typeE2 
  | AddInt (e1,e2) | MulInt (e1,e2) | DiffInt (e1,e2) | DivInt (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
    if (subtype prog typeE1 (Tprim (Tint))) && (subtype prog typeE2 (Tprim (Tint)))
      then (Tprim (Tint))
      else raise (IncompatibleTypes "BAGAM AICI CEVA")
  | AddFlt (e1,e2) | MulFlt (e1,e2) | DiffFlt (e1,e2) | DivFlt (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
      if (subtype prog typeE1 (Tprim (Tfloat))) && (subtype prog typeE2 (Tprim (Tfloat)))
        then (Tprim (Tfloat))
        else raise (IncompatibleTypes "BAGAM AICI CEVA")
  | LglAnd (e1,e2) | LglOr (e1,e2) -> let typeE1 = (typeCheckExp prog env e1) and typeE2 = (typeCheckExp prog env e2) in
      if (subtype prog typeE1 (Tprim (Tbool))) && (subtype prog typeE2 (Tprim (Tbool)))
      then (Tprim (Tbool))
      else raise (IncompatibleTypes "BAGAM AICI CEVA")
  | LglNeg (e) -> let te = typeCheckExp prog env e in 
      if (subtype prog te (Tprim (Tbool))) 
      then (Tprim (Tbool))
      else raise (IncompatibleTypes "BAGAM AICI CEVA")
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
      else raise (IncompatibleTypes "BAGAM AICI CEVA")
  | _ -> raise (VariableNotDefined "ABC")


let ast = [("A",a);("B",b);("Main",main)]
(* let () = let ast = [("A",a);("B",b);("Main",main)] in 
	Printf.printf "%s\n\n" (print_bool (subtype ast (Tclass ("A")) (Tclass ("Object") ))) 

let () = 
	Printf.printf "%s\n\n" (fieldList ast "B") *)