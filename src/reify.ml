open Constr
open EConstr
open Names

(* pick an element in an hashtbl *)
let hashtbl_pick t = Hashtbl.fold (fun i x -> function None -> Some (i,x) | acc -> acc) t None

(* raise an error in Coq *)
let error s = Printf.kprintf (fun s -> CErrors.user_err (Pp.str s)) ("[ATBR reification] "^^s)

(* resolving a typeclass [cls] in a goal [gl] *)
let tc_find env sigma cls = Typeclasses.resolve_one_typeclass env sigma cls

(* creating a name a reference to that name *)
let fresh_name n env =
  let vname = Tactics.fresh_id_in_env Names.Id.Set.empty (Names.Id.of_string n) env in
    vname, mkVar vname 
    
(* access to Coq constants *)
let get_const dir s = 
  lazy (EConstr.of_constr (UnivGen.constr_of_global (Coqlib.find_reference "ATBR.reification" dir s)))

(* make an application using a lazy value *)
let force_app f = fun x -> mkApp (Lazy.force f,x)

(* creating OCaml functions from Coq ones *)
let get_fun_1 d s = let v = get_const d s in fun x -> force_app v [|x|]
let get_fun_2 d s = let v = get_const d s in fun x y -> force_app v [|x;y|]
let get_fun_3 d s = let v = get_const d s in fun x y z -> force_app v [|x;y;z|]
let get_fun_4 d s = let v = get_const d s in fun x y z t -> force_app v [|x;y;z;t|]
let get_fun_5 d s = let v = get_const d s in fun x y z t u -> force_app v [|x;y;z;t;u|]



(* Coq constants *)
module Coq = struct
  (* binary positive numbers *)
  let positive_path = ["Coq" ; "Numbers"; "BinNums"]
  let positive = get_const positive_path "positive"
  let xH = get_const positive_path "xH"
  let xI = get_fun_1 positive_path "xI"
  let xO = get_fun_1 positive_path "xO"
  
  (* a coq positive from an ocaml int *)
  let rec pos_of_int = function
    | 0 -> failwith "[ATBR reification] pos_of_int applied to 0"
    | 1 -> Lazy.force xH 
    | n -> (if n mod 2 = 0 then xO else xI) (pos_of_int (n/2))
end


(* record to factorise code for the various reification function we define *)
type ops = {
  (* classes projections to be reified *)
  c_plus: constr Lazy.t option;
  c_dot:  constr Lazy.t option;
  c_star: constr Lazy.t option;
  c_conv: constr Lazy.t option;
  c_one:  constr Lazy.t option;
  c_zero: constr Lazy.t option;
  (* corresponding syntactic constructors *)
  r_plus: constr Lazy.t;
  r_dot:  constr Lazy.t;
  r_star: constr Lazy.t;
  r_conv: constr Lazy.t;
  r_one:  constr Lazy.t;
  r_zero: constr Lazy.t;
  r_var:  constr Lazy.t;
  (* type of terms *)
  r_x:  constr Lazy.t;
  (* evaluation function (eval gl gph env a b x) *)
  eval: Environ.env -> Evd.evar_map -> constr -> constr -> constr -> constr -> constr -> constr;
  (* name (for error messages) *)
  name: string;
}


(* ATBR.Classes Coq module *)
module Classes = struct
  let path = ["ATBR"; "Classes"]
  let t     = get_fun_1 path "T"
  let x     = get_fun_3 path "X"
  let equal = get_const path "equal"
  let leq   = get_const path "leq"
  let plus  = get_const path "plus"
  let dot   = get_const path "dot"
  let star  = get_const path "star"
  let conv  = get_const path "conv"
  let zero  = get_const path "zero"
  let one   = get_const path "one"	
  let monoid_ops      = get_const path "Monoid_Ops"
  let semilattice_ops = get_const path "SemiLattice_Ops"
  let kleene_op       = get_const path "Star_Op"
  let converse_op     = get_const path "Converse_Op"
  let ops = {
    c_plus = Some plus;
    c_dot  = Some dot;
    c_star = Some star;
    c_conv = Some conv;
    c_zero = Some zero;
    c_one  = Some one; 
    r_plus = plus;
    r_dot  = dot;
    r_star = star;
    r_conv = conv;
    r_zero = zero;
    r_one  = one; 
    r_var  = one;			(* ici, on pourrait mettre une identité... *)
    r_x    = one;	
    eval = (fun env sigma gph e a b x -> x);
    name = "id reification (please report)" }

  (* ugly hack to optimise calls to [Typeclasses.resolve_one_typeclass]: 
     record encountered operations and resort to typeclass resolution only 
     if no operation was encountered *)
  let get r o s = fun env sigma gph -> 
    try match !r with 
      | None -> let x = snd (tc_find env sigma (force_app o [|gph|])) in r:=Some x; x
      | Some x -> x
    with Not_found -> error "could not find an instance of %s on the given graph" s
  let mo  = ref None
  let slo = ref None
  let co  = ref None
  let ko  = ref None
  let get_mo  = get mo  monoid_ops      "Monoid_Ops"
  let get_slo = get slo semilattice_ops "SemiLattice_Ops"
  let get_co  = get co  converse_op     "Converse_Op"
  let get_ko  = get ko  kleene_op       "Star_Op"
  let reset_ops() = mo := None; slo := None; co := None; ko := None
end  


(* ATBR.Reification Coq module *)
module Reification = struct
  let path = ["ATBR"; "Reification"]
  let sigma       = get_fun_1 path "sigma"
  let sigma_empty = get_fun_1 path "sigma_empty"
  let sigma_add   = get_fun_4 path "sigma_add"
  let sigma_get   = get_fun_3 path "sigma_get"
  let pack_type   = get_fun_2 path "Pack"
  let pack        = get_fun_5 path "pack"
  let env_type    = get_fun_1 path "Env"
  let env         = get_fun_3 path "env"
  let typ         = get_fun_3 path "typ"
  module KA = struct
    let path = path @ ["KA"]
    let eval = get_const path "eval"
    let ops = { 
	Classes.ops with
	  c_conv = None;
	  r_plus = get_const path "plus";
	  r_dot  = get_const path "dot";
	  r_star = get_const path "star";
	  r_zero = get_const path "zero";
	  r_one  = get_const path "one";	
	  r_var  = get_const path "var";	
	  r_x    = get_const path "X";	
	  eval   = (fun env sigma g e a b x -> force_app eval 
		      [|g;e;Classes.get_mo env sigma g;Classes.get_slo env sigma g;Classes.get_ko env sigma g;a;b;x|]);
	  name = "kleene" }
  end
  module Semiring = struct
    let path = path @ ["Semiring"]
    let eval = get_const path "eval"
    let ops = { 
	KA.ops with
	  c_star = None;
	  r_plus = get_const path "plus";
	  r_dot  = get_const path "dot";
	  r_zero = get_const path "zero";
	  r_one  = get_const path "one";	
	  r_var  = get_const path "var";	
	  r_x    = get_const path "X";	
	  eval = (fun env sigma g e a b x -> force_app eval 
		    [|g;e;Classes.get_mo env sigma g;Classes.get_slo env sigma g;a;b;x|]);
	  name = "semiring" }
  end
end 

module Tbl : sig
  type t
  (* create an empty table *)
  val create: unit -> t
  (* [insert gl t x y] adds the association [x->y] to [t] and returns 
     the corresponding (coq) index ; [gl] is the current goal, used 
     to compare terms *)
  val insert: Environ.env -> Evd.evar_map -> t -> constr -> constr Lazy.t -> constr
  (* [to_env t typ def] returns (coq) environment corresponding to [t], 
     yielding elements of type [typ], with [def] as default value *)
  val to_env: t -> constr -> constr -> constr
end = struct
  type t = ((constr*constr*constr) list * int) ref

  let create () = ref([],1)

  let rec find env sigma x = function
    | [] -> raise Not_found
    | (x',i,_)::q -> if Reductionops.is_conv env sigma x x' then i else find env sigma x q

  let insert env sigma t x y =
    let l,i = !t in
      try find env sigma x l
      with Not_found -> 
	let j = Coq.pos_of_int i in
	  t := ((x,j,Lazy.force y)::l,i+1); j
    
  let to_env t typ def = match fst !t with
    | [] -> mkLambda (Anonymous,Lazy.force Coq.positive,def)
    | [_,_,x] -> mkLambda (Anonymous,Lazy.force Coq.positive,x)
    | (_,_,x)::q ->
	Reification.sigma_get typ x
	  (List.fold_left
	     (fun acc (_,i,x) -> Reification.sigma_add typ i x acc
	     ) (Reification.sigma_empty typ) q
	  )
end

(* is a constr [c] an operation to be reified ? *)
let is sigma c = function None -> false | Some x -> EConstr.eq_constr sigma c (Lazy.force x)

let retype c = 
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma, ty = Typing.type_of env sigma c in
  Proofview.Unsafe.tclEVARS sigma
  end

(* main entry point *)
let reify_goal ops =
  Proofview.Goal.enter begin fun gl ->

  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in

  (* variables for referring to the environments *)
  let tenv_name,tenv_ref = fresh_name "t" env in
  let env_name,env_ref = fresh_name "e" env in 

  (* table associating indices to encountered types *)
  let tenv = Tbl.create() in 			
  let insert_type t = Tbl.insert env sigma tenv t (lazy t) in

  (* table associating indices to encountered atoms *)
  let tenv' = Tbl.create() in
  let insert_atom gph x s t = Tbl.insert env sigma tenv' x (lazy (Reification.pack gph tenv_ref s t x)) in

  (* clear recorded operations *)
  let () = Classes.reset_ops () in

  match kind sigma (Termops.strip_outer_cast sigma concl) with
    | App(c,ca) ->
	(* we look for an (in)equation *)
	let rel,shift =
	  if EConstr.eq_constr sigma c (Lazy.force Classes.equal) then mkApp (c,[|ca.(0)|]), 0
	  else if EConstr.eq_constr sigma c (Lazy.force Classes.leq) then mkApp (c,[|ca.(0);ca.(1)|]), 1
	  else error "unrecognised goal"
	in
	let gph = ca.(0) in	      (* graph *)
	let src' = ca.(shift+1) in    (* domain of the (in)equation *)
	let src = insert_type src' in	
	let tgt' = ca.(shift+2) in    (* codomain of the (in)equation *)
	let tgt = insert_type tgt' in
	let pck = Reification.pack_type gph tenv_ref in (* type of packed elements *)
	let typ = Classes.t gph in	                (* type of types *)

	(* reification of a term [e], with domain [s] and codomain [t] *)
	let rec reify s t e = 
	  match kind sigma (Termops.strip_outer_cast sigma e) with
	    | App(c,ca) when is sigma c ops.c_plus -> 
		Classes.slo := Some ca.(1);
		force_app ops.r_plus [|gph;env_ref;s;t;reify s t ca.(4);reify s t ca.(5)|]
	    | App(c,ca) when is sigma c ops.c_dot -> 
		Classes.mo := Some ca.(1);
		let r = insert_type ca.(3) in 
		  force_app ops.r_dot [|gph;env_ref;s;r;t;reify s r ca.(5);reify r t ca.(6)|]
	    | App(c,ca) when is sigma c ops.c_star -> (* invariant: s=t *)
		Classes.ko := Some ca.(1);
		force_app ops.r_star [|gph;env_ref;s;reify s t ca.(3)|]
	    | App(c,ca) when is sigma c ops.c_conv -> 
		Classes.co := Some ca.(1);
		force_app ops.r_conv [|gph;env_ref;s;t;reify t s ca.(3)|]
	    | App(c,ca) when is sigma c ops.c_one -> (* invariant: s=t *)
		Classes.mo := Some ca.(1);
		force_app ops.r_one [|gph;env_ref;s|]
	    | App(c,ca) when is sigma c ops.c_zero-> 
		Classes.slo := Some ca.(1);
		force_app ops.r_zero [|gph;env_ref;s;t|]
	    | _ -> 
		let i = insert_atom gph e s t in
		  force_app ops.r_var [|gph;env_ref;i|]
	in

   	(* reification of left and right members *)
	let lv,(ln,lr) = reify src tgt ca.(shift+3), fresh_name "l" env in
	let rv,(rn,rr) = reify src tgt ca.(shift+4), fresh_name "r" env in
	  
	(* apply "eval" around the reified terms *)
	let l = ops.eval env sigma gph env_ref src tgt lr in
	let r = ops.eval env sigma gph env_ref src tgt rr in
	let x = force_app ops.r_x [|gph;env_ref;src;tgt|] in

	(* default value for the environment*)
	let def =
	  if ops.c_one <> None then 
	    (* if we have a [one], use it *)
	    Reification.pack gph tenv_ref src src
	      (force_app Classes.ops.r_one [|gph;Classes.get_mo env sigma gph;src'|])
	  else if ops.c_zero <> None then
	    (* if we have a [zero], use it *)
	    Reification.pack gph tenv_ref src tgt 
	      (force_app Classes.ops.r_zero [|gph;Classes.get_slo env sigma gph;src';tgt'|])
	  else 			
	    (* if the environment is empty, use the left-hand side of the equqtion *)
	    (* nb: this branch is never used currently, since we always have either a one, or a zero *)
	    Reification.pack gph tenv_ref src tgt ca.(shift+3)
	in
	  
   	(* construction of coq' types index *)
	let tenv = Tbl.to_env tenv typ src' in
	  
   	(* construction of coq' reification environment *)
	let tenv' = Reification.env gph tenv_ref (Tbl.to_env tenv' pck def) in

	(* reified goal conclusion: add the relation over the two evaluated members *)
	let reified = 
	  mkNamedLetIn tenv_name tenv (mkArrow (Lazy.force Coq.positive) typ) (
	    mkNamedLetIn env_name tenv' (Reification.env_type gph) (
	      mkNamedLetIn ln lv x (
		mkNamedLetIn rn rv x (
		  (mkApp (rel, [|Reification.typ gph env_ref src; Reification.typ gph env_ref tgt;l;r|]))))))
	in
	  (try 
	     Tacticals.New.tclTHEN (retype reified)
	       (Tactics.convert_concl reified DEFAULTcast)
	   with e -> Feedback.msg_warning (Printer.pr_leconstr_env env sigma reified); raise e)
	    
    | _ -> error "unrecognised goal"
  end
