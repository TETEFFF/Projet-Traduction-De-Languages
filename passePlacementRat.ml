(* Module de la passe de gestion des identifiants *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


let rec analyse_placement_instruction i depl reg=
  match i with 
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
        AstPlacement.Declaration(info,e),getTaille(tid)
        end
      | _ -> failwith "Erreur Interne"
    end
  | AstType.Affectation(ia, e) -> AstPlacement.Affectation(ia,e),0
    
  | AstType.Conditionnelle (c, t, e) -> 
    let nt = analyse_placement_bloc t depl reg in 
    let ne = analyse_placement_bloc e depl reg in 
    AstPlacement.Conditionnelle(c, nt, ne),0
    

  | AstType.TantQue(c, b) -> 
    let nb = analyse_placement_bloc b depl reg in 
    AstPlacement.TantQue(c, nb),0
    
  | AstType.Retour(e, ia) -> 
    begin 
    match info_ast_to_info ia with 
    | InfoFun(_, t, tparam) -> let somme = List.fold_right (fun el tp -> tp + getTaille(el)) tparam 0  in 
      AstPlacement.Retour(e, getTaille t, somme),0
    | _ -> failwith "Erreur Interne"
    end
  | AstType.AffichageInt e -> AstPlacement.AffichageInt e,0
  | AstType.AffichageRat e -> AstPlacement.AffichageRat e,0
  | AstType.AffichageBool e -> AstPlacement.AffichageBool e,0

  | AstType.Empty -> AstPlacement.Empty,0



and analyse_placement_bloc li depl reg = 
  begin 
    match li with 
    | [] -> [],0
    | i::q -> let (ni, ti) = analyse_placement_instruction i depl reg in 
              let (nli, tb) = analyse_placement_bloc q (ti+depl) reg in 
              (ni::nli, ti + tb)

  end
let analyse_placement_fonction (AstType.Fonction(info, lp, li)) = 
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
  let nb = analyse_placement_bloc li 3 "LB" in 
  AstPlacement.Fonction(info, lp, nb)
    
let analyser (AstType.Programme (fonctions, prog)) = 
  let nfs = List.map analyse_placement_fonction fonctions in 
  let np = analyse_placement_bloc prog 0 "SB" in 
  AstPlacement.Programme(nfs, np)