open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/pointeurs/gestion_id/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

let%test_unit "affectationAdresseVariable"= 
  let _ = compiler (pathFichiersRat^"affectationAdresseVariable.rat") in ()

let%test_unit "declarationNewPointeur"= 
  let _ = compiler (pathFichiersRat^"declarationNewPointeur.rat") in ()

let%test_unit "declarationPointeur"= 
  let _ = compiler (pathFichiersRat^"declarationPointeur.rat") in ()

let%test_unit "pointeurParamFonction"= 
  let _ = compiler (pathFichiersRat^"pointeurParamFonction.rat") in ()


let%test_unit "dereferencementSansDeclaration"= 
try 
  let _ = compiler (pathFichiersRat^"dereferencementSansDeclaration.rat")
  in raise ErreurNonDetectee
with
| IdentifiantNonDeclare("p") -> ()

let%test_unit "doubleDeclarationPointeur"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationPointeur.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("p") -> ()

let%test_unit "doubleDeclarationParamPointeur1"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationParamPointeur1.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("a") -> ()

let%test_unit "doubleDeclarationParamPointeur2"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationParamPointeur2.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("a") -> ()

let%test_unit "doubleDeclarationPointeur1"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationPointeur1.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()

let%test_unit "doubleDeclarationPointeur2"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationPointeur2.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()

let%test_unit "doubleDeclarationPointeur3"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationPointeur3.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()

let%test_unit "doubleDeclarationPointeur4"= 
try 
  let _ = compiler (pathFichiersRat^"doubleDeclarationPointeur4.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()

let%test_unit "usePointeurNotDeclared"= 
try 
  let _ = compiler (pathFichiersRat^"usePointeurNotDeclared.rat")
  in raise ErreurNonDetectee
with
| IdentifiantNonDeclare("p") -> ()



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