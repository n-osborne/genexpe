open Genexpe
open QCheck

module Spec = struct
  type cmd = Incr | Read | Decr
  type state = int
  type sut = int ref

  let init_state = 0
  let precond c s = match c with Incr -> true | Read -> true | Decr -> s > 0

  let cmd_gens =
    QCheck.make
      ~print:(function Incr -> "Incr" | Read -> "Read" | Decr -> "Decr")
      (Gen.oneof (List.map Gen.return [ Incr; Read; Decr ]))

  let next_state c s = match c with Incr -> s + 1 | Read -> s | Decr -> s - 1
end

module M = Make (Spec)

let prop (seq, p0, p1) =
  let rec go_seq state = function
    | [] -> Some state
    | x :: xs -> (
        match Spec.precond x state with
        | false -> None
        | true ->
            let state = Spec.next_state x state in
            go_seq state xs)
  in
  let rec go_par state p0 p1 =
    match (p0, p1) with
    | [], [] -> true
    | pg, [] | [], pg -> Option.is_some (go_seq state pg)
    | x :: xs, y :: ys ->
        Spec.precond x state && Spec.precond y state
        && go_par (Spec.next_state x state) xs (y :: ys)
        && go_par (Spec.next_state y state) (x :: xs) ys
  in
  match go_seq Spec.init_state seq with
  | None -> false
  | Some spawn_state -> go_par spawn_state p0 p1

let arb =
  let occ cstr (a, b, c) =
    List.fold_left (fun i c -> if c = cstr then i + 1 else i) 0 (a @ b @ c)
  in
  M.arb_pg 5 10
  |> add_stat ("length p0", fun (_, p0, p1) -> List.length p0 + List.length p1)
  |> add_stat ("occ Decr", occ Spec.Decr)
  |> add_stat ("occ Decr", occ Spec.Read)
  |> add_stat ("occ Decr", occ Spec.Incr)

let test = Test.make ~name:"genexpe" ~count:10000 arb prop
let _ = QCheck_runner.run_tests ~verbose:true [ test ]
