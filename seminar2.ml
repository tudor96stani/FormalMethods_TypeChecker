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

(* let () = let ast = [("A",a);("B",b);("Main",main)] in 
	Printf.printf "%s\n\n" (print_bool (subtype ast (Tclass ("A")) (Tclass ("Object") ))) 

let () = let ast = [("A",a);("B",b);("Main",main)] in 
	Printf.printf "%s\n\n" (fieldList ast "B") *)