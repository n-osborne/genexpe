open QCheck

module type Spec = sig
  type cmd
  (** the type of commands *)

  type state
  (** The type of the model's state *)

  type sut
  (** The type if the system under test *)

  val init_state : state
  (** The model's initial state *)

  val next_state : cmd -> state -> state
  (** Move the internal state machine to the next state*)

  val precond : cmd -> state -> bool
  (** [precond c s] expresses preconditions for command [c]. This is useful,
      e.g., to prevent the shrinker from breaking invariants when minimizing
      counterexamples. *)

  val cmd_gens : cmd Gen.t list
  (** The list of the command generators *)
end

module Make (Spec : Spec) : sig
  val gen_pg :
    int -> int -> (Spec.cmd list * Spec.cmd list * Spec.cmd list) Gen.t
  (** [gen_pg seq_len par_len] generates a triplet of list of commands.

      - The first one is the sequential prefix.
      - The two last ones are two conccurrent processes. *)
end = struct
  let run_pg state cmds = List.fold_right Spec.next_state cmds state

  (** [specialize p g] returns a generator that generate only one value but a
      value such that [p v] is true

      [g] must be the more general possible *)
  let specialize (p : 'a -> bool) (g : 'a Gen.t) : 'a option Gen.t =
    let rec aux fuel =
      if fuel = 0 then Gen.return None
      else
        let open Gen in
        g >>= fun c -> if p c then return (Some c) else aux (fuel - 1)
    in
    aux 10 (* XXX todo: find a good value for the fuel here *)

  let next_cmd (p : Spec.cmd -> bool) : Spec.cmd option Gen.t =
    (* maybe if the [oneof] is in specialize the result would be better *)
    specialize p (Gen.oneof Spec.cmd_gens)

  (** [valid_seq state pg] checks whether the sequential [pg] is valid
      precondition-wise when starting from [state] *)
  let rec valid_seq state : Spec.cmd list -> bool = function
    | [] -> true
    | c :: cmds ->
        Spec.precond c state && valid_seq (Spec.next_state c state) cmds

  (** [valid_last_cmd state cmd process] checks whether [cmd] is a valid last
      command in a process running conccurently with [process]. That is:

      - whenever [cmd] is run, the current state respects its precondition
      - whenever [cmd] is run, it does not break the preconditions of the
        commands that still has to be run in [process] *)
  let rec valid_last_cmd state cmd : Spec.cmd list -> bool = function
    | [] -> Spec.precond cmd state
    | x :: xs ->
        valid_seq state (cmd :: x :: xs)
        && valid_last_cmd (Spec.next_state x state) cmd xs

  (** [valid_par state p0 p1 cmd] checks that preconditions are respected in all
      the interleavings if we add [cmd] at the end of [p0]

      - precondition: all the interleavings of [p0] and [p1] are correct
        precondition-wise *)
  let rec valid_par (state : Spec.state) (p0 : Spec.cmd list)
      (p1 : Spec.cmd list) (cmd : Spec.cmd) : bool =
    match (p0, p1) with
    | [], ys ->
        (* now we can run cmd whenever we want *) valid_last_cmd state cmd ys
    | xs, [] ->
        (* now we should run all p0 before running cmd *)
        run_pg state xs |> Spec.precond cmd
    | x :: xs, y :: ys ->
        (* check both conccurrent steps *)
        (* XXX maybe maintain a set of state * p0 * p1? *)
        valid_par (Spec.next_state x state) xs (y :: ys) cmd
        && valid_par (Spec.next_state y state) (x :: xs) ys cmd

  let gen_par len (spawn_state : Spec.state) :
      (Spec.cmd list * Spec.cmd list) Gen.t =
    let open Gen in
    let rec aux len g0 g1 =
      if len = 0 then pair g0 g1
      else
        g0 >>= fun p0 ->
        g1 >>= fun p1 ->
        let p = valid_par spawn_state p0 p1 in
        let open Gen in
        next_cmd p >>= function
        | None ->
            pair g0 g1 (* XXX here we could have some local backtracking *)
        | Some c ->
            let g0 = return (p0 @ [ c ]) in
            aux (len - 1) g1 g0
    in
    aux len (return []) (return [])

  let gen_seq (len : int) : Spec.cmd list Gen.t =
    let rec aux len state =
      let open Gen in
      if len = 0 then return []
      else
        next_cmd (fun c -> Spec.precond c state) >>= function
        | None -> return []
        | Some c ->
            aux (len - 1) (Spec.next_state c state) >>= fun cmds ->
            return (c :: cmds)
    in
    aux len Spec.init_state

  let gen_pg seq_len par_len =
    let open Gen in
    gen_seq seq_len >>= fun pref ->
    run_pg Spec.init_state pref |> gen_par par_len >>= fun (p0, p1) ->
    triple (return pref) (return p0) (return p1)
end
