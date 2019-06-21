module type KERNEL =  
  sig
    type form =
      | Variable of string 
      | Lambda of form * form 

    type thm = private Provable of form list * form 

    val v : string -> form
    val (/) : form -> form -> form

    val is_proved_by : form -> thm -> bool

    val assume : form -> thm
    val intro_rule : form -> thm -> thm
    val elim_rule : thm -> thm -> thm

    exception KernelException of string

  end;;

module Kernel : KERNEL = struct
  type form =
    | Variable of string 
    | Lambda of form * form 

  type thm = Provable of form list * form 

  exception KernelException of string

  (* handier constructors for the formula *)
  let v s  = Variable (s)

  let (/) arg  body  = Lambda (arg, body)

  let is_proved_by conclusion (Provable(_,thesis) : thm) = thesis = conclusion 

  let assume f = Provable ([f], f)

  let intro_rule f (Provable (assumptions,conclusion) : thm) = 
       let remove_assumption = (fun x  -> x <> f : form -> bool)  in
       Provable((List.filter remove_assumption assumptions), (f / conclusion))
  
  let elim_rule (Provable(gamma, a2b) : thm) (Provable(delta, a) : thm) =
       match a2b with
       | Lambda (origin,dest) ->
           if origin = a
           then Provable(List.append gamma delta, dest)
           else raise (KernelException "cannot use elim_rule; head does not match")
       | _ -> raise (KernelException "left side is not an implication")
  
end;;

open Kernel;;

let rec string_of_form f =
     match f with
     | Variable(v) -> v
     | Lambda(v,b) -> "(" ^ String.concat " => " (List.map string_of_form [v; b]) ^ ")"

let print_form : Format.formatter -> form -> unit = fun _ -> fun f -> (print_string (string_of_form f))

let string_of_thm (Provable(gamma, formula) : thm) =
     let environment = List.map string_of_form gamma  in
       let assumptions_string = String.concat ", " environment  in
         let conclusion_string = string_of_form formula  in
           assumptions_string ^ (" |- " ^ conclusion_string)

let print_thm : Format.formatter -> thm -> unit = fun _ -> fun t -> (print_string (string_of_thm t))

module type GOAL =
        sig
        exception QED
        type goal = Goal of form list * form 
        type justification = thm list -> thm
        type goalstate = (goal list * justification)
        type tactic = goal -> goalstate
        end;;

module Goal : GOAL = struct
        exception QED
        type goal = Goal of form list * form 
        type justification = thm list -> thm
        type goalstate = (goal list * justification)
        type tactic = goal -> goalstate
end;;

open Goal;;


let string_of_goal (Goal(gamma, formula) : goal) =
     let environment = List.map string_of_form gamma  in
       let assumptions_string = String.concat ", " environment  in
         let conclusion_string = string_of_form formula  in
           assumptions_string ^ (" |? " ^ conclusion_string)

let print_goal : Format.formatter -> goal -> unit = fun _ -> fun g -> (print_string (string_of_goal g))
  
let history = (ref [] : goalstate list ref) 
let current_state () = List.hd (!history) 

let p () = 
     match current_state () with
     | exception Failure _ -> failwith "no goal set, use `g` to start a proof"
     | ([],_) -> raise QED
     | (goals,_) -> List.hd goals
  
let g (to_prove : form) =
     let newGoal = Goal([], to_prove) in
     match current_state () with
      | exception Failure _ -> history := [([newGoal], ((fun x  -> List.hd x)))]
      | (goals,justification) ->
          let updated_goals = List.append [newGoal] goals in
          let new_state = updated_goals, justification in
          history := List.append [new_state] (!history)
  
let assumption (Goal (assumptions,formula) : goal) =
     if List.mem formula assumptions
     then ([], (fun _  -> assume formula))
     else failwith "goal not in assumptions"
  
let intro_tac (Goal (assumptions,formula) : goal) = 
     match formula with
     | Variable _ -> failwith "cannot use on variable goal"
     | Lambda(a,b) ->
         let t = Goal((List.append assumptions [a]), b) in
         let intro_just thms =
           match List.find (is_proved_by b) thms with
           | interesting -> intro_rule a interesting
           | exception Not_found  ->
               failwith "failed intro tactic"
            in
            ([t], intro_just)

let elim_tac (f : form) (Goal(assumptions, conclusion) : goal) =
        let prove_this_implication = Goal(assumptions, f / conclusion) in
        let find_this_implication = is_proved_by (f / conclusion) in
        let prove_this_assumption = Goal(assumptions, f) in
        let find_this_assumption = is_proved_by f in
        let new_justification = fun thms ->
                match List.find find_this_implication thms,
                    List.find find_this_assumption thms with
                      | thm_implication, thm_assumption -> elim_rule thm_implication thm_assumption
                      | exception Not_found -> failwith "failed elim tactic" in
        ([prove_this_implication; prove_this_assumption], new_justification)


let rec take l n =
  if n = 0 then ([], l)
  else
    (match l with
     | [] -> failwith "not enough elements to take"
     | x::xs -> let (a,b) = take xs (n - 1)  in ((x :: a), b))
  
let by (tac : tactic) ((goals,goals_just) : goalstate) : goalstate =
  match goals with
  | head::rest ->
      let (head_requirements,head_justification) = tac head  in
      let split_at = List.length head_requirements  in
      let result_requirements = head_requirements @ rest  in
      let result_justification thms =
        let (head_goals,remaining_goals) = take thms split_at  in
        let head_theorem = head_justification head_goals  in
        goals_just ([head_theorem] @ remaining_goals)  in
          (result_requirements, result_justification)
  | [] -> failwith "please state a goal" 

(* some automation *)

(* I though it would be easy for a hundred monkeys to prove something such
 * as (A => C) => A => C but it must be too hard *)
let monkeys : int ref = ref(0)

let rec do_the_monkey_dance (g : goal) : goalstate =
        if !monkeys = 0 then
                failwith "No more monkeys, gotta buy some more"
        else
        let tactic_of_the_day : tactic =
                let Goal(assumptions, _) = g in
                  match Random.int(2) with
                    | 0 -> assumption
                    | 1 -> intro_tac
                    | _ -> let len = List.length assumptions in (elim_tac (List.nth assumptions (Random.int(len))))
         in
           try tactic_of_the_day g with
           | Failure _ ->
                           monkeys := !monkeys - 1;
                           do_the_monkey_dance g

(* A higly trained team of monkeys at your command *)
let hundred_monkeys_tac (g : goal) : goalstate =
        monkeys := 100;
        Random.self_init();
        do_the_monkey_dance g

(* As many monkeys as we need *)
(* turns out that a thousand monkeys is all you need to prove (A => C) => A => C*)
let monkeys_tac (bound : int) (g : goal) : goalstate =
        monkeys := bound;
        Random.self_init();
        do_the_monkey_dance g

(* look for implications in the assumptions that would prove the 
 * current one *)
let rec implies_formula to_prove given : bool = 
        match given with
        | Lambda(_, b) -> (to_prove = b) || (implies_formula to_prove b)
        | _ -> false

let rec suggest_elim (f : form) (c : form) : string =
        match f with
          | Lambda(a,b) -> 
             if b == c then
               "use `elim_tac` with " ^ (string_of_form a)
             else (suggest_elim b c)
          | _ -> failwith (string_of_form f) ^ " cannot be used in elimination"

let hint () =
    match current_state() with
     | ([], _) -> print_string "just run the `top_thm` you are done";
     | (g::_, _) ->
        let Goal(assumptions, conclusion) = g in
          if List.mem conclusion assumptions then
                  print_endline "use `assumption` tactic"
          else
            match List.filter (implies_formula conclusion) assumptions, conclusion with
             | [] , Lambda(_,_) -> print_endline "use `intro_tac` tactic"
             | xs , _ ->  List.iter (fun e -> print_endline (suggest_elim e conclusion)) xs
            
let e (t : tactic) =
  match !history with
    | current_goal::rest -> history := (by t current_goal) :: current_goal :: rest; p()
    | _ -> failwith "set a current goal before doing stuff";;

let b () =
  match !history with
    | _ :: prev :: rest -> history := prev :: rest; p()
    | _ -> p();;

let top_thm () : thm =
  match current_state() with
    | ([], justification) -> justification([])
    | _ -> failwith "there are things left to prove"

let rec find_elim (f : form) (conclusion : form) : form =
  match f with
    | Lambda(a,b) -> if b = conclusion then a else (find_elim b conclusion)
    | _ -> failwith ((string_of_form f) ^ " cannot be used in elimination")

let auto_tac (g : goal) : goalstate =
    match current_state() with
     | ([], _) -> raise QED
     | _ ->
        let Goal(assumptions, conclusion) = g in
          if List.mem conclusion assumptions then (assumption g)
          else
            match List.filter (implies_formula conclusion) assumptions, conclusion with
             | [] , Lambda(_,_) -> (intro_tac g)
             | x::_ , _ ->  (elim_tac (find_elim x conclusion) g)
             | _ -> failwith "`auto_tac` failed miserably"

(* cannot prove (A -> B -> C) -> (A -> B) -> A -> C)
 * but can prove (A -> C) -> A -> C *)
let rec auto () : unit =
  match !history with
    | [] -> failwith "no more things to prove"
    | current_goal::rest ->
                    match current_goal with
                      | (_::_, _) -> history := (by auto_tac current_goal) :: current_goal :: rest; auto();
                      | ([],_) -> failwith "nothing to prove in the current goal"
