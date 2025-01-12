open Tds
open Ast
open Type
open Code
open Tam

type t1 = Ast.AstPlacement.programme
type t2 = string


let rec analyse_code_affectable a en_ecriture= 
  match a with 
  | AstType.Ident info ->  
    begin  
    match info_ast_to_info info with 
      | InfoVar(_, tid, addr, reg) ->
        let t = 
        begin 
          match tid with 
          | Pointeur(t) -> getTaille t
          | _ -> 0
        end in  
        if  en_ecriture then store (getTaille tid) addr reg,t else load (getTaille tid) addr reg,t
      | _ -> failwith "Erreur Interne"
    end
  | AstType.Deref a -> let (code, taille) = analyse_code_affectable a en_ecriture in (code ^ 
    if en_ecriture then storei taille else loadi taille),1

let rec analyse_code_expression e = 
  match e with 
  | AstType.AppelFonction(info, le) -> 
    ( List.fold_right (fun elt tr ->(analyse_code_expression elt) ^ tr) le "" ) ^
    begin match info_ast_to_info info with 
      | InfoFun(nom, _, _) -> call "SB" nom 
      | _ -> failwith "Erreur interne"
    end 

  | AstType.Affectable a -> 
    let (c,_) = analyse_code_affectable a false in c
  | AstType.Unaire(op, e1) ->  
    (analyse_code_expression e1) ^ 
    begin 
      match op with 
        | Numerateur -> pop 0 1
        | Denominateur-> pop 1 1 
    end 
  | AstType.Binaire(op, e1, e2) ->  
    let ne1 = analyse_code_expression e1 in 
    let ne2 = analyse_code_expression e2 in
    ne1 ^ ne2 ^
    begin 
      match op with 
        | PlusInt -> subr "IAdd"
        | PlusRat -> call "SB" "RAdd"
        | MultInt -> subr "IMul"
        | MultRat -> call "SB" "RMul"
        | EquInt -> subr "IEq"
        | Inf -> subr "ILss"
        | EquBool -> subr "IEq"
        | Fraction -> call "SB" "norm"
    end 
  | AstType.Booleen b -> if b then loadl_int 1 else loadl_int 0

  | AstType.Entier i -> loadl_int i

  | AstType.Null -> ""

  | AstType.New t -> (loadl_int (getTaille t))^(subr "MAlloc")

  | AstType.Address info -> 
    begin  
      match info_ast_to_info info with 
        | InfoVar(_, _, addr, reg) -> loada addr reg
        | _ -> failwith "Erreur Interne"
      end

let rec analyse_code_instruction i =
  match i with 
  | AstPlacement.Declaration(info, e) -> 
    let ne = analyse_code_expression e in
    begin   
      match info_ast_to_info info with 
      | InfoVar(_, tid, addr, reg) -> (push (getTaille tid)) ^ ne ^ (store (getTaille tid) addr reg)
      | _ -> failwith "Erreur Interne"
    end  
  
  | AstPlacement.Affectation(a, e) -> 
    let (code,_) = analyse_code_affectable a true in
    ( analyse_code_expression e ) ^ code
    
  | AstPlacement.Conditionnelle (c, t, e) -> 
    let etiquetteE = getEtiquette() in 
    let etiquetteFin = getEtiquette() in 
    ( analyse_code_expression c ) ^ 
    ( jumpif 0 etiquetteE ) ^ 
    ( analyse_code_bloc t ) ^
    ( jump etiquetteFin ) ^ 
    label etiquetteE ^ 
    ( analyse_code_bloc e) ^
    label etiquetteFin
    
  | AstPlacement.TantQue(c, b) -> 
    let etiquetteDebut = getEtiquette() in 
    let etiquetteFin = getEtiquette() in 
    label etiquetteDebut ^
    ( analyse_code_expression c ) ^ 
    ( jumpif 0 etiquetteFin ) ^ 
    ( analyse_code_bloc b ) ^
    ( jump etiquetteDebut ) ^ 
    label etiquetteFin
  | AstPlacement.Retour(e, tailleRet, tailleParam) -> 
( analyse_code_expression e ) ^ ( return tailleRet tailleParam)  

  | AstPlacement.AffichageInt e -> (analyse_code_expression e) ^ subr "IOut"
  | AstPlacement.AffichageRat e -> (analyse_code_expression e) ^ call "SB" "ROut"
  | AstPlacement.AffichageBool e -> (analyse_code_expression e) ^ subr "BOut"

  | AstPlacement.Empty -> ""




 
and analyse_code_bloc (li,taille) = 
  let nli = List.fold_right (fun elt tr ->(analyse_code_instruction elt) ^ tr) li "" in 
  nli ^ pop 0 taille


let analyse_code_variable (Ast.AstPlacement.Variable(info,e)) = 
  let ne = analyse_code_expression e in
    begin   
      match info_ast_to_info info with 
      | InfoVar(_, tid, addr, reg) -> (push (getTaille tid)) ^ ne ^ (store (getTaille tid) addr reg)
      | _ -> failwith "Erreur Interne"
    end 

let analyse_code_fonction (Ast.AstPlacement.Fonction(info, _, (li, _))) = 
  begin 
    match info_ast_to_info info with 
    | InfoFun(nom, _ , _) -> label nom 
    | _ -> failwith "Erreur Interne"
  end ^ 
  ( analyse_code_bloc (li,0)) ^ 
  halt

let analyser (Ast.AstPlacement.Programme (variables,fonctions, prog)) = 
let codeVariables = List.fold_right (fun elt tr -> (analyse_code_variable elt) ^ tr ) variables "" in 
let codeFonctions = List.fold_right (fun elt tr -> (analyse_code_fonction elt) ^ tr ) fonctions "" in 
let lMain = label "main" in
getEntete() ^ codeVariables ^ codeFonctions ^ lMain ^(analyse_code_bloc prog) ^ halt