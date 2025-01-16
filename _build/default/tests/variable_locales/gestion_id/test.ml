open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/variable_locales/gestion_id/fichiersRat/"

(**********)
(*  TESTS *)
(**********)


(* Déclaration d'une seule variable statique valide *)
let%test_unit "declarationVarStatique" =
let _ = compiler (pathFichiersRat ^ "declarationVarStatique.rat") in ()

(* Double declaration variables statiques*)
let%test_unit "doubleDeclVarStatique" = 
  try 
    let _ = compiler (pathFichiersRat^"doubleDeclVarStatique.rat")
    in raise ErreurNonDetectee
  with
  | DoubleDeclaration("x") -> ()

(* Double declaration variable statique et variable local*)
let%test_unit "doubleDeclVarStatiqueVarLocal" = 
try
  let _ = compiler (pathFichiersRat^"doubleDeclVarStatiqueVarLocal.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()

(* Double declaration variable statique dans if/else*)
let%test_unit "doubleDeclIF" =  
  let _ = compiler (pathFichiersRat^"doubleDeclIF.rat") in ()

(* Double declaration variable statique dans while*)
let%test_unit "doubleDeclWhile" =  
  let _ = compiler (pathFichiersRat^"doubleDeclWhile.rat")in ()

(* Déclaration d'une seule variable statique valide *)
let%test_unit "varStatiqueFonction" =
let _ = compiler (pathFichiersRat ^ "varStatiqueFonction.rat") in ()

let%test_unit "usetwoVarLocales" =
let _ = compiler (pathFichiersRat ^ "usetwoVarLocales.rat") in ()

let%test_unit "doubleDecVarStatique2" = 
try 
  let _ = compiler (pathFichiersRat^"doubleDecVarStatique2.rat")
  in raise ErreurNonDetectee
with
| DoubleDeclaration("x") -> ()


let%test_unit "useVariableStatFct" = 
try 
  let _ = compiler (pathFichiersRat^"useVariableStatFct.rat")
  in raise ErreurNonDetectee
with
| IdentifiantNonDeclare("x") -> ()

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