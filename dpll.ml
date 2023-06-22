open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* fonctions auxiliares *)
(* vérifie si la liste l contient la négation du littéral x *)
let rec neg_exists x l = match l with
  | [] -> false
  | h::t -> if (h = -x) then true else neg_exists x t

(* vérifie si la liste l contient le littéral x *)
let rec exists x l = match l with
  | [] -> false
  | h::t -> if (h = x) then true else exists x t

(* supprime le littéral el de la liste *)
let rec listSans el = function
  | [] -> []
  | x :: l -> if el <> x then x :: listSans el l else listSans el l


(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
(* Fonction recursive qui permet de parcourir les clauses*)
  let rec simplifie_tmp clause res =
    match clause with
      | [] -> res
      | h::t ->
        (* s'il existe au moins un élément de la liste qui satisfait x = l,
           avec x un littéral de la liste clauses et l le littéral à mettre
           à vrai, alors ne rien rajouter au résultat (res) *)
        if (exists l h) then simplifie_tmp t res
        (* si la clause contient la négation de l, alors ajouter au resultat 
           tous les éléments qui ne sont pas la négation de l *)
        else if (neg_exists l h) then simplifie_tmp t (listSans (-l) h :: res)
        (* si l n'appartient pas à la clause alors ajouter la clause au
           résultat sans la modifier *)
        else simplifie_tmp t (h :: res)
  in simplifie_tmp (List.rev clauses) []


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *)
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme [])*)
(* let () = print_modele (solveur_split coloriage [])*)

(* solveur dpll récursif *)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let unitaire clauses =
  let rec recherche l =
    match l with
    (* si la clause est vide ou que toute les clauses ont été parcourue,
       lève une erreur *)
    | [] -> raise Not_found
    | h :: t ->
      (* si une clause contenant qu'un seul littéral est trouvée,
         retourne le littéral, sinon continue la recherche dans
         les autres clauses *)
      match h with
      | [x] -> x
      | _ -> recherche t
  in recherche clauses

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  (* transforme list list en list contenant tous les littéraux de
     la formule propositionnelle *)
  let oneDimClause = List.flatten clauses in
  (* vérifie si clauses contient un littéral x sans sa négation *)
  let rec tmp_pur clause =
    (* parcourt de la liste de clauses :
      - si la clause est vide ou que toute les clauses ont été parcourues,
        lève une erreur;
      - si oneDimClause ne contient pas la négation du littéral h,
        alors retourne h, sinon continue la vérification sur t, le reste
        de la liste *)
    match clause with
    | [] -> raise(Failure "pas de littéral pur")
    | h::t -> if neg_exists h oneDimClause then tmp_pur t else h
in tmp_pur oneDimClause

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* si la liste des clauses est vide ou que toute les clauses ont
     été parcourues, retourner la liste interpretation *)
  if clauses = [] then Some interpretation
  (* s'il y a une clause vide, alors retourner None c-à-d non satisfiable *)
  else if exists [] clauses then None
  else
    (* si une clause ne contient qu'un seul littéral l, alors appeler
       récursivement la méthode solveur_dpll_rec sur les clauses
       simplifiées avec l et ajoute l à la liste d'interprétation *)
    try (let elem_unit = unitaire clauses in
    solveur_dpll_rec (simplifie elem_unit clauses) (elem_unit::interpretation)) with
      Not_found ->
        (* s'il n'y a pas de clause unitaire, chercher si une clause
           contient un littéral l pur, si oui, alors appeler
           récursivement la méthode solveur_dpll_rec sur les clauses 
           simplifiées avec l et ajoute l à la liste d'interprétation *)
        try (let elem_pur = pur clauses in
        solveur_dpll_rec (simplifie elem_pur clauses) (elem_pur::interpretation)) with
          pas_de_litteral_pur ->
              (* s'il n'y a ni clause unitaire ni littéral pur,
                 choisir un littéral, ici, le premier élément de la première clause *)
              let head = List.hd (List.hd clauses) in
              (* appeler solveur_dpll_rec en simplifiant les clauses avec le littéral
                 choisi et l'ajoute dans la liste d'interprétation*)
              let partieGauche = (solveur_dpll_rec (simplifie head clauses) (head::interpretation)) in
              (*  si la formule propositionnelle n'est pas satisfiable (renvoie None) avec
                  l'interprétation du littéral choisi, alors appeler solveur_dpll_rec
                  en simplifiant les clauses avec la négation du littéral choisi *)
              if partieGauche <> None then partieGauche
              else solveur_dpll_rec (simplifie (-head) clauses) ((-head)::interpretation)

(* tests *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
