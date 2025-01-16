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

let pathFichiersRat = "../../../../../tests/variables_globales/placement/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

  let%test "test1_varGlob_1" = 
  test (pathFichiersRat^"test1.rat")  "variable" ("y",1)  (0, "SB")

  let%test "test1_x_1" = 
  test (pathFichiersRat^"test1.rat")  "main" ("x",1)  (1, "SB")

  let%test "test2_x_1" = 
  test (pathFichiersRat^"test2.rat")  "var" ("x",1)  (0, "SB")

  let%test "test2_y_1" = 
  test (pathFichiersRat^"test2.rat")  "var" ("y",1)  (1, "SB")

  let%test "test2_z_1" = 
  test (pathFichiersRat^"test2.rat")  "var" ("z",1)  (2, "SB")

  let%test "test2_t_1" = 
  test (pathFichiersRat^"test2.rat")  "main" ("t",1)  (3, "SB")

  let%test "test3_x_1" = 
  test (pathFichiersRat^"test3.rat")  "var" ("x",1)  (0, "SB")
  
  let%test "test3_y_1" = 
  test (pathFichiersRat^"test3.rat")  "var" ("y",1)  (1, "SB")
  
  let%test "test3_z_1" = 
  test (pathFichiersRat^"test3.rat")  "main" ("z",1)  (2, "SB")

  let%test "test4_x_1" = 
  test (pathFichiersRat^"test4.rat")  "var" ("x",1)  (0, "SB")
  
  let%test "test4_y_1" = 
  test (pathFichiersRat^"test4.rat")  "var" ("y",1)  (2, "SB")

  let%test "test4_z_1" = 
  test (pathFichiersRat^"test4.rat")  "main" ("z",1)  (4, "SB")

  let%test "test5_x_1" = 
  test (pathFichiersRat^"test5.rat")  "var" ("x",1)  (0, "SB")

  let%test "test5_y_1" = 
  test (pathFichiersRat^"test5.rat")  "var" ("y",1)  (1, "SB")

  let%test "test5_z_1" = 
  test (pathFichiersRat^"test5.rat")  "var" ("z",1)  (3, "SB")

  let%test "test6_x_1" = 
  test (pathFichiersRat^"test6.rat")  "var" ("x",1)  (0, "SB")

  let%test "test6_y_1" = 
  test (pathFichiersRat^"test6.rat")  "main" ("y",1)  (1, "SB")

  let%test "test6_z_1" = 
  test (pathFichiersRat^"test6.rat")  "main" ("z",1)  (3, "SB")

  let%test "test6_y_2" = 
  test (pathFichiersRat^"test6.rat")  "main" ("y",2)  (1, "SB")

  let%test "test6_z_2" = 
  test (pathFichiersRat^"test6.rat")  "main" ("z",2)  (3, "SB")

  let%test "test6_x1_1" = 
  test (pathFichiersRat^"test6.rat")  "main" ("x1",1)  (1, "SB")

  let%test "test7_x_1" = 
  test (pathFichiersRat^"test7.rat")  "var" ("x",1)  (0, "SB")

  let%test "test7_y_1" = 
  test (pathFichiersRat^"test7.rat")  "main" ("y",1)  (1, "SB")

  let%test "test7_z_1" = 
  test (pathFichiersRat^"test7.rat")  "main" ("z",1)  (3, "SB")

  let%test "test7_x1_1" = 
  test (pathFichiersRat^"test7.rat")  "main" ("x1",1)  (1, "SB")

  let%test "test7_z1_1" = 
  test (pathFichiersRat^"test7.rat")  "main" ("z1",1)  (3, "SB")

  let%test "test9_x_1" = 
  test (pathFichiersRat^"test9.rat")  "var" ("x",1)  (0, "SB")

  let%test "test9_a_1" = 
  test (pathFichiersRat^"test9.rat")  "f" ("a",1)  (-1, "LB")

  let%test "test9_y_1" = 
  test (pathFichiersRat^"test9.rat")  "f" ("y",1)  (3, "LB")













