open Rat
open Compilateur
open Passe

(* Return la liste des adresses des variables d'un programme RAT *)
let getListeDep ratfile =
  let input = open_in ratfile in
  let filebuf = Lexing.from_channel input in
  try
  let ast = Parser.main Lexer.token filebuf in
  let past = CompilateurRat.calculer_placement ast in
  let listeAdresses = VerifPlacement.analyser past in
  listeAdresses
  with
  | Lexer.Error _ as e ->
      report_error ratfile filebuf "lexical error (unexpected character).";
      raise e
  | Parser.Error as e->
      report_error ratfile filebuf "syntax error.";
      raise e

(* teste si dans le fichier fichier, dans la fonction fonction (main pour programme principal)
la occ occurence de la variable var a l'adresse dep[registre]
*)
let test fichier fonction (var,occ) (dep,registre) = 
  let l = getListeDep fichier in
  let lmain = List.assoc fonction l in
  let rec aux i lmain = 
    if i=1 
    then
      let (d,r) = List.assoc var lmain in
      (d=dep && r=registre)
    else 
      aux (i-1) (List.remove_assoc var lmain)
  in aux occ lmain

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/pointeurs/placement/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

  let%test "test1_p_1" = 
  test (pathFichiersRat^"test1.rat")  "main" ("p",1)  (3, "SB")

  let%test "test1_p_2" = 
  test (pathFichiersRat^"test1.rat")  "main" ("p",2)  (7, "SB")

  let%test "test1_f_p_1" = 
  test (pathFichiersRat^"test1.rat")  "f" ("p",1)  (6, "LB")

  let%test "test1_f_p_2" = 
  test (pathFichiersRat^"test1.rat")  "f" ("p",2)  (10, "LB")

  let%test "test2_f_a" = 
  test (pathFichiersRat^"test2.rat")  "f" ("a",1)  (-1, "LB")

  let%test "test3_f_b" = 
  test (pathFichiersRat^"test3.rat")  "f" ("b",1)  (-4, "LB")
    
let%test "test3_f_r" = 
  test (pathFichiersRat^"test3.rat")  "f" ("r",1)  (-3, "LB")
    
let%test "test3_f_i" = 
  test (pathFichiersRat^"test3.rat")  "f" ("i",1)  (-1, "LB")

let%test "test4_x" = 
  test (pathFichiersRat^"test4.rat")  "main" ("x",1)  (0,"SB")

let%test "test4_y" = 
  test (pathFichiersRat^"test4.rat")  "main" ("y",1) (1,"SB")

let%test "test4_z" = 
  test (pathFichiersRat^"test4.rat")  "main" ("z",1)  (2 ,"SB")

  let%test "test5_pi_1" = 
  test (pathFichiersRat^"test5.rat")  "main" ("pi",1)  (3, "SB")

let%test "test5_p_1" = 
  test (pathFichiersRat^"test5.rat")  "main" ("p",1)  (7, "SB")

let%test "test5_p_2" = 
  test (pathFichiersRat^"test5.rat")  "main" ("p",2)  (4, "SB")