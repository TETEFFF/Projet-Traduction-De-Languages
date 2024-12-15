(* Module de la passe de gestion des identifiants *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme



let rec analyse_type_expression e = 
  match e with 
  | AstTds.AppelFonction(info, le) -> 
    begin 
      let lte = List.map analyse_type_expression le in 
      let nte = List.map (fun (ex, _) -> ex) lte in
      let ntl = List.map (fun (_, t) -> t) lte in 
      match info_ast_to_info info with
      | InfoFun(_, t, tl) -> 
        if (est_compatible_list tl ntl) then 
          AstType.AppelFonction(info, nte),t   
        else raise (TypesParametresInattendus(ntl, tl))
      | _ -> failwith "Erreur Interne"
    end 

  | AstTds.Ident info -> 
    begin
    match info_ast_to_info info with
      | InfoVar(_,tid,_,_) -> 
        AstType.Ident(info),tid
      | _ -> failwith "Erreur Interne"
    end 
  | AstTds.Unaire(op, e1) -> 
    begin 
    let (ne, te) = analyse_type_expression e1 in 
      match te with 
      | Rat -> 
        begin 
          match op with 
          | Numerateur -> AstType.Unaire(AstType.Numerateur, ne),Int
          | Denominateur -> AstType.Unaire(AstType.Denominateur, ne),Int
        end
      | _ -> raise (TypeInattendu(te, Rat))
    end
  | AstTds.Binaire(op, e1, e2) -> 
    begin
    let (ne1, t1) = analyse_type_expression e1 in 
    let (ne2, t2) = analyse_type_expression e2 in 
    match op,t1,t2 with 
     | Plus, Int, Int -> AstType.Binaire(PlusInt, ne1, ne2),Int
     | Plus, Rat, Rat -> AstType.Binaire(PlusRat, ne1, ne2),Rat
     | Mult, Int, Int -> AstType.Binaire(MultInt, ne1, ne2),Int
     | Mult, Rat, Rat -> AstType.Binaire(MultRat, ne1, ne2),Rat
     | Fraction, Int, Int -> AstType.Binaire(Fraction, ne1, ne2),Rat
     | Equ, Int, Int -> AstType.Binaire(EquInt, ne1, ne2),Bool
     | Equ, Bool, Bool -> AstType.Binaire(EquBool, ne1, ne2),Bool
     | Inf, Int, Int -> AstType.Binaire(Inf, ne1, ne2),Bool
     | _ -> raise (TypeBinaireInattendu(op, t1, t2))
    end
  | AstTds.Booleen b -> AstType.Booleen b, Bool

  | AstTds.Entier i -> AstType.Entier i,Int


let rec analyse_type_instruction i =
  match i with 
  | AstTds.Declaration(t, info, e) -> 
    let (ne, te) = analyse_type_expression e in 
      if est_compatible t te then 
        begin
        modifier_type_variable t info ; 
        AstType.Declaration (info, ne)
        end
      else raise (TypeInattendu (te,t))

  | AstTds.Affectation(info, e) -> 
    begin
    let (ne, te) = analyse_type_expression e in
      match (info_ast_to_info info) with
      | InfoVar(_,tid,_,_) ->  
        if est_compatible te tid then AstType.Affectation(info, ne)
        else raise (TypeInattendu (te,tid))
      | _ -> failwith "Erreur Interne"
    end

  | AstTds.Affichage e -> 
    begin 
    let (ne, te) = analyse_type_expression e in
      match te with 
        | Int -> AstType.AffichageInt ne 
        | Bool -> AstType.AffichageBool ne 
        | Rat -> AstType.AffichageRat ne 
        | _ -> failwith "Erreur Interne" 

    end
  | AstTds.Conditionnelle (c, t, e) -> 
    begin 
    let (ne, te) = analyse_type_expression c in
    match te with 
    | Bool -> let nbt = analyse_type_bloc t in 
              let nbe = analyse_type_bloc e in 
                AstType.Conditionnelle (ne, nbt, nbe)
    | _ -> raise(TypeInattendu(te, Bool)) 
    end

  | AstTds.TantQue(c, b) -> 
    begin 
      let (ne, te) = analyse_type_expression c in
      match te with 
      | Bool -> let nb = analyse_type_bloc b in 
                  AstType.TantQue (ne, nb)
      | _ -> raise(TypeInattendu(te, Bool)) 
      end

  | AstTds.Retour(e, ia) -> 
    begin
      let (ne, te) = analyse_type_expression e in
        match (info_ast_to_info ia) with
        | InfoFun(_,tfc,_) ->  
          if est_compatible te tfc then AstType.Retour(ne, ia)
          else raise (TypeInattendu (te,tfc))
        | _ -> failwith "Erreur Interne"
        end

  | AstTds.Empty -> AstType.Empty



and analyse_type_bloc li = List.map analyse_type_instruction li


let analyse_type_fonction (AstTds.Fonction(t,info,lp,li))= 
    modifier_type_fonction t (List.map (fun (t,_) -> t) lp) info;
    let _ = List.map (fun (t,i) -> modifier_type_variable t i) lp in
    let nli = analyse_type_bloc li in 
    AstType.Fonction(info,(List.map (fun (_,i) -> i) lp),nli)

let analyse_type_fonctions lf = 
  List.map analyse_type_fonction lf 

let analyser (AstTds.Programme (fonctions, prog)) = 
  let nfs = analyse_type_fonctions fonctions in 
  let np = analyse_type_bloc prog in 
  AstType.Programme(nfs, np)