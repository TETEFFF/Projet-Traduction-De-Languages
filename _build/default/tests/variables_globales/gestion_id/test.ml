open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/variables_globales/gestion_id/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

(* Déclaration d'une seule variable globale valide *)
let%test_unit "declarationVarGlobale" =
let _ = compiler (pathFichiersRat ^ "declarationVarGlobale.rat") in ()

(* Double declaration *)
(* Erreur de double declaration *)
let%test_unit "doubleDeclarationVarGlobale" = 
  try 
    let _ = compiler (pathFichiersRat^"doubleDeclarationVarGlobale.rat")
    in raise ErreurNonDetectee
  with
  | DoubleDeclaration("x") -> ()

(* Conflit de nom var globale et var definit dans le bloc *)
let%test_unit "conflitDeclarationVarGlobale" = 
let _ = compiler (pathFichiersRat^"conflitDeclarationVarGlobale.rat") in ()

(* Utilisation d'une variable globale dans une fonction *)
let%test_unit "useVariableGlobaleFct" =
let _ = compiler (pathFichiersRat ^ "useVariableGlobaleFct.rat") in ()


(* Fonction utilisant une variable globale et un paramètre *)
let%test_unit "useVarGlobaleetParam" =
let _ = compiler (pathFichiersRat ^ "useVarGlobaleetParam.rat") in ()


(* Utilisation de 2 variables globales*)
let%test_unit "usetwoVarGlobale" =
let _ = compiler (pathFichiersRat ^ "usetwoVarGlobale.rat") in ()

(* declaration d une variable x avec 2 types differents*)
let%test_unit "doubleDecVarGlobal" =
  try 
    let _ = compiler (pathFichiersRat^"doubleDecVarGlobal.rat")
    in raise ErreurNonDetectee
  with
  | DoubleDeclaration("x") -> ()

(* declaration d'une variable globale a partir d'une variable definit au bloc*)
let%test_unit "test4" =
  try
    let _ = compiler (pathFichiersRat ^ "test4.rat") 
    in raise ErreurNonDetectee
  with 
  | IdentifiantNonDeclare "z" -> ()

(* declaration dans if/else*)
  let%test_unit "doubleDecVarGlobale_if_else" =
    let _ = compiler (pathFichiersRat^"doubleDeclIF.rat") in ()

(* declaration dans while*)
  let%test_unit "doubleDecVarGlobale_while" =
    let _ = compiler (pathFichiersRat^"doubleDeclWhile.rat") in ()

(* Fichiers de tests de la génération de code -> doivent passer la TDS *)
open Unix
open Filename

let rec test d p_tam = 
  try 
    let file = readdir d in
    if (check_suffix file ".rat") 
    then
    (
     try
       let _ = compiler  (p_tam^file) in (); 
     with e -> print_string (p_tam^file); print_newline(); raise e;
    )
    else ();
    test d p_tam
  with End_of_file -> ()

let%test_unit "all_tam" =
  let p_tam = "../../../../../tests/tam/avec_fonction/fichiersRat/" in
  let d = opendir p_tam in
  test d p_tam