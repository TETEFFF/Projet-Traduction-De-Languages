open Rat
open Compilateur

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../../../../tests/runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)


(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/pointeurs/tam/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

let%expect_test "test1" =
  runtam (pathFichiersRat^"test1.rat");
  [%expect{| 2 |}]

let%expect_test "test2" =
  runtam (pathFichiersRat^"test2.rat");
  [%expect{| [4/7] |}]

let%expect_test "test3" =
  runtam (pathFichiersRat^"test3.rat");
  [%expect{| true |}]

let%expect_test "test3" =
  runtam (pathFichiersRat^"test3.rat");
  [%expect{| true |}]

let%expect_test "test4" =
  runtam (pathFichiersRat^"test4.rat");
  [%expect{| 18 |}]

let%expect_test "test5" =
  runtam (pathFichiersRat^"test5.rat");
  [%expect{| [9/4][27/14][27/16][3/2] |}]

let%expect_test "test6" =
  runtam (pathFichiersRat^"test6.rat");
  [%expect{| 1 |}]

let%expect_test "test7" =
  runtam (pathFichiersRat^"test7.rat");
  [%expect{| 10 |}]

let%expect_test "test8" =
  runtam (pathFichiersRat^"test8.rat");
  [%expect{| 28 |}]
