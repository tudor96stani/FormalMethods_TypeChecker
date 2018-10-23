type tPrim = Tint | Tfloat | Tbool| Tvoid 
and
typ = Tprim of tPrim 
      | Tclass of string 
      | Tbot 
and
fldDecl = typ * string 
and
fPrmList = fPrm list 
and
fPrm = (typ*string) 
and
vall = Vnull 
      | Int of int 
      | Float of float 
      | Bool of bool | Vvoid 
and
blkExp = Bvar of typ*string * exp 
        | Bnvar of exp 
and
varList = string list
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
let () = 
  let _ = ("A","Object",[(Tprim (Tint)),"f1"],
    [(Tprim (Tint)),"m1",[((Tprim (Tint)),"a"),((Tprim (Tint)),"b")],
      Bvar ((Tprim (Tint)),"c",
        Seq (AsgnV ("c", AddInt(Var ("a"),Var ("b"))), Seq (AsgnF ("this","f1",
                                                            AddInt (Vfld ("this","c"), Var ("c"))), Var ("c")))
    )
    ]) in print_newline ()