(* Module de la passe de gestion des identifiants *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


let rec analyse_placement_instruction i depl depl_stat reg=
  match i with 
  | AstType.VarStatLocale(info,e) ->
    begin
    match info_ast_to_info info with 
    | InfoVar(_,tid,_,_) -> 
      modifier_adresse_variable depl "SB" info;
      AstPlacement.VarStatLocale(info,e),getTaille(tid),getTaille(tid)
      | _ -> failwith "Erreur Interne"
    end
  | AstType.Declaration(info, e) -> 
    begin 
    match info_ast_to_info info with 
      | InfoVar(_,tid,_,_) -> 
        begin
          (*
          print_string (string_of_int depl);
          print_newline ();
          *)
        modifier_adresse_variable depl reg info;
        AstPlacement.Declaration(info,e),getTaille(tid),0
        end
      | _ -> failwith "Erreur Interne"
    end
  | AstType.Affectation(a, e) -> AstPlacement.Affectation(a,e),0,0
    
  | AstType.Conditionnelle (c, t, e) -> 
    let (nt1, nt2, _) = analyse_placement_bloc t depl depl_stat reg in 
    let (ne1, ne2, _) = analyse_placement_bloc e depl depl_stat reg in 
    AstPlacement.Conditionnelle(c, (nt1,nt2), (ne1,ne2)),0,0
    

  | AstType.TantQue(c, b) -> 
    let (nb1, nb2, _) = analyse_placement_bloc b depl depl_stat reg in 
    AstPlacement.TantQue(c, (nb1,nb2)),0,0
    
  | AstType.Retour(e, ia) -> 
    begin 
    match info_ast_to_info ia with 
    | InfoFun(_, t, tparam) -> let somme = List.fold_right (fun el tp -> tp + getTaille(el)) tparam 0  in 
      AstPlacement.Retour(e, getTaille t, somme),0,0
    | _ -> failwith "Erreur Interne"
    end
  | AstType.AffichageInt e -> AstPlacement.AffichageInt e,0,0
  | AstType.AffichageRat e -> AstPlacement.AffichageRat e,0,0
  | AstType.AffichageBool e -> AstPlacement.AffichageBool e,0,0

  | AstType.Empty -> AstPlacement.Empty,0,0



and analyse_placement_bloc li depl depl_stat reg = 
  begin 
    match li with 
    | [] -> [],0,0
    | i::q -> let (ni, ti, ts) = analyse_placement_instruction i depl depl_stat reg in 
              let (nli, tb, tsb) = analyse_placement_bloc q (ti+depl) (depl_stat + ts) reg in 
              (ni::nli, ti + tb, ts + tsb)

  end

let analyse_placement_variable depl (AstType.Variable(info, e)) = 
  match info_ast_to_info info with 
      | InfoVar(_,tid,_,_) -> 
        begin
        modifier_adresse_variable depl "SB" info;
        AstPlacement.Variable(info,e),getTaille(tid)
        end
      | _ -> failwith "Erreur Interne"


let analyse_placement_fonction depl_s (AstType.Fonction(info, lp, li)) = 
  let rec analyse_placement_parametres lp = 
    match lp with 
      | [] -> 0
      | i::q -> begin
                let tailleq = analyse_placement_parametres q in 
                let taillei = 
                  begin 
                    match info_ast_to_info i with 
                      | InfoVar(_, ti, _,_) -> getTaille ti
                      | _ -> failwith "Erreur Interne"
                  end 
                in 
                (*
                print_string (string_of_int (-tailleq - taillei));
                print_newline ();
                *)
                modifier_adresse_variable (-tailleq - taillei) "LB" i;
                (tailleq + taillei )
              end
              
  in let _ =  analyse_placement_parametres lp in   
  let nb = analyse_placement_bloc li 3 depl_s "LB" in 
  let (nli,tb,depl_stat) = nb in
  AstPlacement.Fonction(info, lp, (nli,tb)),depl_stat

  let analyse_placement_variables variables =
    let rec aux variables depl = 
    match variables with 
    | [] -> [],0
    | v::q -> let (nv,ta) = analyse_placement_variable depl v in 
              let (lv,acc) = aux q (depl + ta) in
           nv::lv,(acc+ta)
    in aux variables 0

    let analyse_placement_fonctions fonctions depl_init =
      let rec aux fonctions depl = 
      match fonctions with 
      | [] -> [],0
      | v::q -> let (nf,ta) = analyse_placement_fonction depl v in 
                let (lf,acc) = aux q (depl + ta) in
             nf::lf,(acc+ta)
      in aux fonctions depl_init
    
let analyser (AstType.Programme (variables, fonctions, prog)) = 
  let (nvs, depl) = analyse_placement_variables variables in 
  let (nfs, depl1) = analyse_placement_fonctions fonctions depl in 
  let (nli, tb,_) = analyse_placement_bloc prog depl1 0 "SB" in 
  AstPlacement.Programme(nvs,nfs, (nli,tb))