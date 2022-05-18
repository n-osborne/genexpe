open Genexpe
open QCheck

module Spec : Spec = struct
  type cmd = Incr | Read | Decr
  type state = int
  type sut = int ref

  let init_state = 0
  let precond c s = match c with Incr -> true | Read -> true | Decr -> s > 0
  let cmd_gens = List.map Gen.return [ Incr; Read; Decr ]
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

let arb_cmds n m = QCheck.make (M.gen_pg n m)
let test = Test.make ~name:"genexpe" ~count:1000 (arb_cmds 5 10) prop
let () = QCheck_runner.run_tests_main [ test ]
