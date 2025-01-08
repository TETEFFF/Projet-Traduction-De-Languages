open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/type/sans_fonction/fichiersRat/"

(**********)
(*  TESTS *)
(**********)


let%test_unit "testDeclaration1"= 
  let _ = compiler (pathFichiersRat^"testDeclaration1.rat") in ()

let%test_unit "testDeclaration2"= 
  let _ = compiler (pathFichiersRat^"testDeclaration2.rat") in ()

let%test_unit "testDeclaration3"= 
  let _ = compiler (pathFichiersRat^"testDeclaration3.rat") in ()

let%test_unit "testDeclaration4"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration4.rat")
    in  raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Int) -> ()

let%test_unit "testDeclaration5"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Rat) -> ()

let%test_unit "testDeclaration6"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testDeclaration7"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration7.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testDeclaration8"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration8.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Int) -> ()

let%test_unit "testDeclaration9"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclaration9.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testAffectation1"= 
  let _ = compiler (pathFichiersRat^"testAffectation1.rat") in ()

let%test_unit "testAffectation2"= 
  let _ = compiler (pathFichiersRat^"testAffectation2.rat") in ()

let%test_unit "testAffectation3"= 
  let _ = compiler (pathFichiersRat^"testAffectation3.rat") in ()

let%test_unit "testAffectation4"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation4.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testAffectation5"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Int) -> ()

let%test_unit "testAffectation6"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Rat) -> ()

let%test_unit "testAffectation7"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation7.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Int) -> ()

let%test_unit "testAffectation8"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation8.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testAffectation9"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectation9.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testConditionnelle1"= 
  let _ = compiler (pathFichiersRat^"testConditionnelle1.rat") in ()

let%test_unit "testConditionnelle2"= 
  try 
    let _ = compiler (pathFichiersRat^"testConditionnelle2.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testConditionnelle3"= 
  try 
    let _ = compiler (pathFichiersRat^"testConditionnelle3.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testConditionnelle4"= 
  let _ = compiler (pathFichiersRat^"testConditionnelle4.rat") in ()

let%test_unit "testConditionnelle5"= 
  try 
    let _ = compiler (pathFichiersRat^"testConditionnelle5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testConditionnelle6"= 
  try 
    let _ = compiler (pathFichiersRat^"testConditionnelle6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testRepetition1"= 
  let _ = compiler (pathFichiersRat^"testRepetition1.rat") in ()

let%test_unit "testRepetition2"= 
  try 
    let _ = compiler (pathFichiersRat^"testRepetition2.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testRepetition3"= 
  try 
    let _ = compiler (pathFichiersRat^"testRepetition3.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testRepetition4"= 
  let _ = compiler (pathFichiersRat^"testRepetition4.rat") in ()

let%test_unit "testRepetition5"= 
  try 
    let _ = compiler (pathFichiersRat^"testRepetition5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testRepetition6"= 
  try 
    let _ = compiler (pathFichiersRat^"testRepetition6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testPrint1"= 
  let _ = compiler (pathFichiersRat^"testPrint1.rat") in ()

let%test_unit "testPrint2"= 
  let _ = compiler (pathFichiersRat^"testPrint2.rat") in ()

let%test_unit "testPrint3"= 
  let _ = compiler (pathFichiersRat^"testPrint3.rat") in ()

let%test_unit "testRationnel1"= 
  let _ = compiler (pathFichiersRat^"testRationnel1.rat") in ()

let%test_unit "testRationnel2"= 
  let _ = compiler (pathFichiersRat^"testRationnel2.rat") in ()

let%test_unit "testRationnel3"= 
  try 
    let _ = compiler (pathFichiersRat^"testRationnel3.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(_,Int,Rat) -> ()

let%test_unit "testRationnel4"= 
  try 
    let _ = compiler (pathFichiersRat^"testRationnel4.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(_,Bool,Int) -> ()

let%test_unit "testRationnel5"= 
  try 
    let _ = compiler (pathFichiersRat^"testRationnel5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Int) -> ()

let%test_unit "testNumerateur1"= 
  let _ = compiler (pathFichiersRat^"testNumerateur1.rat") in ()

let%test_unit "testNumerateur2"= 
  let _ = compiler (pathFichiersRat^"testNumerateur2.rat") in ()

let%test_unit "testNumerateur3"= 
  try 
    let _ = compiler (pathFichiersRat^"testNumerateur3.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Rat) -> ()

let%test_unit "testNumerateur4"= 
  try 
    let _ = compiler (pathFichiersRat^"testNumerateur4.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testNumerateur5"= 
  try 
    let _ = compiler (pathFichiersRat^"testNumerateur5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testDenominateur1"= 
  let _ = compiler (pathFichiersRat^"testDenominateur1.rat") in ()

let%test_unit "testDenominateur2"= 
  let _ = compiler (pathFichiersRat^"testDenominateur2.rat") in ()

let%test_unit "testDenominateur3"= 
  try 
    let _ = compiler (pathFichiersRat^"testDenominateur3.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Rat) -> ()

let%test_unit "testDenominateur4"= 
  try 
    let _ = compiler (pathFichiersRat^"testDenominateur4.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testDenominateur5"= 
  try 
    let _ = compiler (pathFichiersRat^"testDenominateur5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testIdent1"= 
  let _ = compiler (pathFichiersRat^"testIdent1.rat") in ()

let%test_unit "testIdent2"= 
  let _ = compiler (pathFichiersRat^"testIdent2.rat") in ()

let%test_unit "testIdent3"= 
  let _ = compiler (pathFichiersRat^"testIdent3.rat") in ()

let%test_unit "testIdent4"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent4.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Int) -> ()

let%test_unit "testIdent5"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent5.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat,Bool) -> ()

let%test_unit "testIdent6"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testIdent7"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent7.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testIdent8"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent8.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Rat) -> ()

let%test_unit "testIdent9"= 
  try 
    let _ = compiler (pathFichiersRat^"testIdent9.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Int) -> ()

let%test_unit "testOperation1"= 
  let _ = compiler (pathFichiersRat^"testOperation1.rat") in ()

let%test_unit "testOperation2"= 
  let _ = compiler (pathFichiersRat^"testOperation2.rat") in ()

let%test_unit "testOperation3"= 
  try 
    let _ = compiler (pathFichiersRat^"testOperation3.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(Plus, Bool, Bool) -> ()

let%test_unit "testOperation4"= 
  try 
    let _ = compiler (pathFichiersRat^"testOperation4.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(Equ, Rat, Rat) -> ()

let%test_unit "testOperation5"= 
  let _ = compiler (pathFichiersRat^"testOperation5.rat") in ()

let%test_unit "testOperation6"= 
  let _ = compiler (pathFichiersRat^"testOperation6.rat") in ()

let%test_unit "testOperation7"= 
  let _ = compiler (pathFichiersRat^"testOperation7.rat") in ()

let%test_unit "testOperation8"= 
  let _ = compiler (pathFichiersRat^"testOperation8.rat") in ()

let%test_unit "testOperation9"= 
  try 
    let _ = compiler (pathFichiersRat^"testOperation9.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(Mult, Bool, Bool) -> ()

let%test_unit "testOperation10"= 
  try 
    let _ = compiler (pathFichiersRat^"testOperation10.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(Inf, Rat, Rat) -> ()

let%test_unit "testOperation11"= 
  try 
    let _ = compiler (pathFichiersRat^"testOperation11.rat")
    in raise ErreurNonDetectee
  with
  | TypeBinaireInattendu(Inf, Bool, Bool) -> ()

let%test_unit "testOperation12"= 
  let _ = compiler (pathFichiersRat^"testOperation12.rat") in ()

let%test_unit "testAffectationPointeur1"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur1.rat") in ()

let%test_unit "testAffectationPointeur2"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur2.rat") in ()

let%test_unit "testAffectationPointeur3"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur3.rat") in ()

let%test_unit "testAffectationPointeur4"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur4.rat") in ()

let%test_unit "testAffectationPointeur5"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur5.rat") in ()

let%test_unit "testAffectationPointeur6"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur6.rat") in ()

  let%test_unit "testAffectationPointeur7"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur7.rat") in ()

  let%test_unit "testAffectationPointeur8"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur8.rat") in ()

  let%test_unit "testAffectationPointeur9"= 
  let _ = compiler (pathFichiersRat^"testAffectationPointeur9.rat") in ()

  let%test_unit "testAffectationPointeur10"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur10.rat")
    in raise ErreurNonDetectee
  with
  | DerefNonPointeur(Int) -> ()

  let%test_unit "testAffectationPointeur11"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur11.rat")
    in raise ErreurNonDetectee
  with
  | DerefNonPointeur(Rat) -> ()

  let%test_unit "testAffectationPointeur12"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur12.rat")
    in raise ErreurNonDetectee
  with
  | DerefNonPointeur(Bool) -> ()

  let%test_unit "testAffectationPointeur13"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur13.rat")
    in raise ErreurNonDetectee
  with
  | DerefNonPointeur(Int) -> ()

  let%test_unit "testAffectationPointeur15"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur15.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat, Int) -> ()

  let%test_unit "testAffectationPointeur16"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur16.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool, Int) -> ()

  let%test_unit "testAffectationPointeur17"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur17.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Int) -> ()

  let%test_unit "testAffectationPointeur18"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur18.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int, Rat) -> ()

  let%test_unit "testAffectationPointeur19"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur19.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool, Rat) -> ()

  let%test_unit "testAffectationPointeur20"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur20.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Rat) -> ()

  let%test_unit "testAffectationPointeur21"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur21.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int, Bool) -> ()

  let%test_unit "testAffectationPointeur22"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur22.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Rat, Bool) -> ()

  let%test_unit "testAffectationPointeur23"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur23.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Bool) -> ()

  let%test_unit "testAffectationPointeur24"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur24.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Int) -> ()

  let%test_unit "testAffectationPointeur25"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur25.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Rat) -> ()

  let%test_unit "testAffectationPointeur26"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur26.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Bool) -> ()

  let%test_unit "testAffectationPointeur27"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur27.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Int) -> ()

  let%test_unit "testAffectationPointeur28"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur28.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Rat) -> ()

  let%test_unit "testAffectationPointeur29"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur29.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Bool) -> ()

  let%test_unit "testAffectationPointeur30"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur30.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Pointeur(Int)), Pointeur(Int)) -> ()

  let%test_unit "testAffectationPointeur31"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur31.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Rat)) -> ()

  let%test_unit "testAffectationPointeur32"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur32.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Bool)) -> ()

  let%test_unit "testAffectationPointeur33"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur33.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Pointeur(Int))) -> ()

  let%test_unit "testAffectationPointeur34"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur34.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Pointeur(Int)) -> ()

  let%test_unit "testAffectationPointeur35"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur35.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Pointeur(Rat)) -> ()

  let%test_unit "testAffectationPointeur36"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur36.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool),Pointeur(Pointeur(Bool))) -> ()

  let%test_unit "testAffectationPointeur37"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur37.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Pointeur(Int)) -> ()

  let%test_unit "testAffectationPointeur38"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur38.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Pointeur(Bool)) -> ()

  let%test_unit "testAffectationPointeur39"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur39.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Pointeur(Pointeur(Int))) -> ()

  let%test_unit "testAffectationPointeur40"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur40.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Int) -> ()

  let%test_unit "testAffectationPointeur41"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur41.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Rat) -> ()

  let%test_unit "testAffectationPointeur42"= 
  try 
    let _ = compiler (pathFichiersRat^"testAffectationPointeur42.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Bool) -> ()

  let%test_unit "testDeclarationPointeur1"= 
  let _ = compiler (pathFichiersRat^"testDeclarationPointeur1.rat") in ()

  let%test_unit "testDeclarationPointeur2"= 
  let _ = compiler (pathFichiersRat^"testDeclarationPointeur2.rat") in ()

  let%test_unit "testDeclarationPointeur3"= 
  let _ = compiler (pathFichiersRat^"testDeclarationPointeur3.rat") in ()

  let%test_unit "testDeclarationPointeur4"= 
  let _ = compiler (pathFichiersRat^"testDeclarationPointeur4.rat") in ()

  let%test_unit "testDeclarationPointeur5"= 
  let _ = compiler (pathFichiersRat^"testDeclarationPointeur5.rat") in ()

  let%test_unit "testDeclarationPointeur6"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur6.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Pointeur(Int)) -> ()

  let%test_unit "testDeclarationPointeur7"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur7.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Pointeur(Int)) -> ()

  let%test_unit "testDeclarationPointeur8"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur8.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Pointeur(Int)), Pointeur(Int)) -> ()

  let%test_unit "testDeclarationPointeur9"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur9.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Rat)) -> ()

  let%test_unit "testDeclarationPointeur10"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur10.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Pointeur(Rat)) -> ()

  let%test_unit "testDeclarationPointeur11"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur11.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Pointeur(Rat)), Pointeur(Rat)) -> ()

  let%test_unit "testDeclarationPointeur12"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur12.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Bool)) -> ()

  let%test_unit "testDeclarationPointeur13"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur13.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Pointeur(Bool)) -> ()

  let%test_unit "testDeclarationPointeur14"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur14.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Pointeur(Bool)), Pointeur(Bool)) -> ()

  let%test_unit "testDeclarationPointeur15"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur15.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Pointeur(Pointeur(Int))) -> ()

  let%test_unit "testDeclarationPointeur16"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur16.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Int), Int) -> ()

  let%test_unit "testDeclarationPointeur17"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur17.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Rat), Rat) -> ()

  let%test_unit "testDeclarationPointeur18"= 
  try 
    let _ = compiler (pathFichiersRat^"testDeclarationPointeur18.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Pointeur(Bool), Bool) -> ()

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
  let p_tam = "../../../../../tests/tam/sans_fonction/fichiersRat/" in
  let d = opendir p_tam in
  test d p_tam