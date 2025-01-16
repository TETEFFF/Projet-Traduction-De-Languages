(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme




(* analyse_tds_affectable : tds -> AstSyntax.affectable -> bool -> AstTds.Affectable*bool*int                                                 *)
(* Paramètre tds : la table des symboles courante                                                                                             *)
(* Paramètre e : l'affectable à analyser                                                                                                      *)
(* Paramètre en_ecriture : booleen qui indique si l'affectable est en ecriture (à gauche d'une affectation) ou en lecture                     *)
(* Retourne une triplet : Le premier élément: issu de la transformation de l'affectable en type AstTds.Affectable après analyse               *)
(*                        de la bonne utilisation des identifiants. Le deuxième                                                               *)
(*                      : Le deuxième élément : Booleen qui indique si l'affectable correspond à une constante                                *)
(*                      : Le troisième élément : Entier qui vaut la valeur de la constante si l'affectable correspond à une constante, 0 sinon*)
(* Erreur si mauvaise utilisation des identifiants                                                                                            *)


let rec analyse_tds_affectable tds a en_ecriture = 
  match a with 
  | Ast.AstSyntax.Deref a -> 
    let na,_,_ = analyse_tds_affectable tds a en_ecriture in 
      AstTds.Deref(na),false,0
  | Ast.AstSyntax.Ident id -> 
    begin 
      match chercherGlobalement tds id with 
      | None -> raise (IdentifiantNonDeclare id)
      | Some ia -> 
        begin 
          match info_ast_to_info ia with 
          | InfoFun (n,_,_) -> raise (MauvaiseUtilisationIdentifiant n)
          | InfoVar _ -> Ast.AstTds.Ident(ia),false,0
          | InfoConst (n, v)-> if en_ecriture then raise( MauvaiseUtilisationIdentifiant n)
          else (Ast.AstTds.Ident(ia)),true,v  
        end 
    end 

(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e = 
  match e with
  | Ast.AstSyntax.AppelFonction (id , le) ->
    begin 
      match chercherGlobalement tds id with
      | None -> raise (IdentifiantNonDeclare id)
      | Some info -> 
                    match info_ast_to_info info with
                    | InfoFun _ -> let ne = List.map (analyse_tds_expression tds) le in 
                                   Ast.AstTds.AppelFonction(info, ne)
                    | _ -> raise (MauvaiseUtilisationIdentifiant id)
    end
  | Ast.AstSyntax.Affectable a ->
    let na,est_const,v = analyse_tds_affectable tds a false in if est_const then AstTds.Entier v else Ast.AstTds.Affectable na 

  | Ast.AstSyntax.Binaire (b,e1,e2) ->  Ast.AstTds.Binaire (b,analyse_tds_expression tds e1,analyse_tds_expression tds e2)

  | Ast.AstSyntax.Unaire(op,e1) ->  Ast.AstTds.Unaire(op,analyse_tds_expression tds e1)

  | Ast.AstSyntax.Booleen b -> Ast.AstTds.Booleen b

  | Ast.AstSyntax.Entier i ->  Ast.AstTds.Entier i

  | Ast.AstSyntax.Address id -> 
    begin 
      match chercherGlobalement tds id with 
      | None -> raise (IdentifiantNonDeclare id )
      | Some ia -> 
        begin 
          match info_ast_to_info ia with
          | InfoVar _ -> Ast.AstTds.Address ia 
          | _ -> failwith "Erreur Interne"
        end 
    end 
  
  | Ast.AstSyntax.New t -> Ast.AstTds.New t 

  | Ast.AstSyntax.Null -> Ast.AstTds.Null

(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia i =
  match i with
  | AstSyntax.VarStatLocale (t, n, e)-> 
      begin
      match chercherLocalement tds n with
      | None ->
          let ne = analyse_tds_expression tds e in
          let info = InfoVar (n,Undefined, 0, "") in
          let ia = info_to_info_ast info in
          ajouter tds n ia;
          AstTds.VarStatLocale (t, ia, ne)
      | Some _ ->
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
            et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Declaration (t, ia, ne)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
            il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Affectation (a,e) -> 
    let na,_,_ = analyse_tds_affectable tds a true in
    let ne = analyse_tds_expression tds e in 
    AstTds.Affectation (na,ne)
      
  | AstSyntax.Constante (n,v) ->
      begin
        match chercherLocalement tds n with
        | None ->
          (* L'identifiant n'est pas trouvé dans la tds locale,
             il n'a donc pas été déclaré dans le bloc courant *)
          (* Ajout dans la tds de la constante *)
          ajouter tds n (info_to_info_ast (InfoConst (n,v)));
          (* Suppression du noeud de déclaration des constantes devenu inutile *)
          AstTds.Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale,
          il a donc déjà été déclaré dans le bloc courant *)
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e ->
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      AstTds.Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds oia t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds oia e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      AstTds.Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds oia b in
      (* Renvoie la nouvelle structure de la boucle *)
      AstTds.TantQue (nc, bast)
  | AstSyntax.Retour (e) ->
      begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
        (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : erreur *)
      | None -> raise RetourDansMain
        (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e in
        AstTds.Retour (ne,ia)
      end


(* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si le bloc li est dans le programme principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds oia li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc.
     Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc oia) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli


let analyse_tds_variable maintds (AstSyntax.Variable(t,n,e)) =
  match chercherLocalement maintds n with
  | None ->
      let ne = analyse_tds_expression maintds e in
      let info = InfoVar (n,Undefined, 0, "") in
      let ia = info_to_info_ast info in
      ajouter maintds n ia;
      AstTds.Variable (t, ia, ne)
  | Some _ ->
      raise (DoubleDeclaration n) 


(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  = 
match chercherGlobalement maintds n with
    | None ->
          let tds = creerTDSFille maintds in
          let nlp = List.map (fun (ty , str) -> 
            match chercherLocalement tds str with 
              | None -> 
              let vinfo = InfoVar (str,Undefined, 0, "") in 
              let vinfo_ptr = info_to_info_ast vinfo in 
              ajouter tds str vinfo_ptr; 
              (ty, vinfo_ptr)
              | _ -> raise (DoubleDeclaration str)
            ) lp in 
          let info = InfoFun(n,t, List.map (fun (ty, _)-> ty) lp) in 
          let info_ptr = info_to_info_ast info in
          ajouter maintds n info_ptr; 
          let nli = analyse_tds_bloc tds (Some info_ptr) li in  
          AstTds.Fonction(t, info_ptr, nlp, nli)
         
    | _ -> raise (DoubleDeclaration n)



(*ajouter maintds strer : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (variables,fonctions,prog)) =
  let tds = creerTDSMere () in
  let nv = List.map (analyse_tds_variable tds) variables in
  let nf = List.map (analyse_tds_fonction tds) fonctions in
  let nb = analyse_tds_bloc tds None prog in
  AstTds.Programme (nv,nf,nb)
