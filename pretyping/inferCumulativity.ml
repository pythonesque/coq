(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Reduction
open Declarations
open Constr
open Univ
open Util

(** Throughout this module we modify a map [variances] from local
   universes to [Variance.t]. It starts as a trivial mapping to
   [Irrelevant] and every time we encounter a local universe we
   restrict it accordingly. *)

let infer_level_eq u variances =
  if LMap.mem u variances
  then LMap.set u Variance.Invariant variances
  else variances


(* optimised for the case where there are no universe substitutions...
   NOTE: the reason this must be done separately is that Esubst.subs
         cannot handle universe substitutions mixed with regular
         argument substitutions.  It might otherwise be possible to
         make this more efficient. *)
let get_univ subst stk =
  let open CClosure in
  let rec strip_rec subst = function
    | Zuniv u :: s -> assert false (* strip_rec (u::subst) s *)
    | _ :: s -> strip_rec subst s
    | [] -> subst in
  let subst' = strip_rec [] stk in
  List.fold_left (fun subst u ->
                  (match subst with
                   | [] -> u
                   | u'::_ -> Univ.subst_instance_instance u' u)::subst)
                 subst subst'

(* Idea: since the set of universes we care about makes more sense top down,
 *       we will just collect the substs lists bottom-up, construct
 *       substitutions top-down, and then resume analysis bottom-up again.
 *       During the top-down phase, we forget any bindings that don't map to
 *       values in variances (we just don't care about them) and mark the
 *       ones that do as invariant.  In fact, since invariance is final, we
 *       can overapproximate and use a single context for each set of
 *       arguments (the rationale being: once we see a variable in context,
 *       it's not going to become *more* invariant).  That said: this kind
 *       of reasoning is tricky.  We should probably just faithfully track
 *       substs as we do elsewhere.
 *)
(* let infer_level_eq_inv u variances =
  (* Normally: look up the level in variances that is the value of this
   * entry for the instance attached to the constr *)
  (* Here: we have some variances with values for certain keys, Level(k).
     We want to update the variances by mapping Level(k) to u', where
     in the instance, index k points to u'.  So we map Level(k) to u'.
     Otherwise, we check whether variances previously contained a mapping...
     ah, this is too hard.  Let's extract the substitutions early and then
     apply them lazily on the fly.  Then we know the final substitutions at
     all times. *)
   (*
      * given the value of an entry in the instance attached to some
     constr whose body has computed variances (in this context), we want
     to find out which keys in variances correspond to this -index-.
     Essentially, variances with key -index- should now *)
  (* We want to find the value in variances that is a key in the array *)
  if LMap.mem u variances
  then LMap.set u Variance.Invariant variances
  else variances *)

let infer_level_leq u variances =
  match LMap.find u variances with
  | exception Not_found -> variances
  | varu -> LMap.set u (Variance.sup varu Variance.Covariant) variances

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u)

(* let infer_generic_variance_eq variances u =
  (* observation : variances will be a subset of entries in the array *)
  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u)
  LMap.fold (fun vark varv -> ) variances ()

    let ff _ m accu = Map.fold f m accu in
    Int.Map.fold ff s accu

    val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t

  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u) *)

let variance_pb cv_pb var =
  let open Variance in
  match cv_pb, var with
  | _, Irrelevant -> Irrelevant
  | _, Invariant -> Invariant
  | CONV, Covariant -> Invariant
  | CUMUL, Covariant -> Covariant

let infer_cumulative_ind_instance cv_pb cumi variances u =
  Array.fold_left2 (fun variances varu u ->
      match LMap.find u variances with
      | exception Not_found -> variances
      | varu' ->
        LMap.set u (Variance.sup varu' (variance_pb cv_pb varu)) variances)
    variances (ACumulativityInfo.variance cumi) (Instance.to_array u)

let infer_inductive_instance cv_pb env variances subst ind nargs u =
  let u = match subst with
          | u'::_ -> subst_instance_instance u' u
          | [] -> u in
  let mind = Environ.lookup_mind (fst ind) env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (inductive_cumulativity_arguments (mind,snd ind)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance cv_pb cumi variances u

let infer_constructor_instance_eq env variances subst ((mi,ind),ctor) nargs u =
  let u = match subst with
          | u'::_ -> subst_instance_instance u' u
          | [] -> u in
  let mind = Environ.lookup_mind mi env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (constructor_cumulativity_arguments (mind,ind,ctor)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance CONV cumi variances u

let infer_sort cv_pb variances subst s =
  let s = match s with
          | Sorts.Type s' ->
            (match subst with
             | u::_ -> subst_instance_universe u s'
             | [] -> s')
          | _ -> Sorts.univ_of_sort s in
  match cv_pb with
  | CONV ->
    LSet.fold infer_level_eq (Universe.levels s) variances
  | CUMUL ->
    LSet.fold infer_level_leq (Universe.levels s) variances

let infer_table_key infos variances subst c =
  let open Names in
  match c with
  | ConstKey (_, u) ->
    (match subst with
     | u'::_ -> let u = if Instance.is_empty u then u' else
                           subst_instance_instance u' u in
                infer_generic_instance_eq variances u
     | _ -> infer_generic_instance_eq variances u)
  | VarKey _ | RelKey _ -> variances

let whd_stack (infos, tab) hd stk = CClosure.whd_stack infos tab hd stk

let rec infer_fterm cv_pb infos variances subst hd stk =
  Control.check_for_interrupt ();
  let hd,stk = whd_stack infos hd stk in
  let subst = get_univ subst stk in
  let open CClosure in
  let infer_vect variances e xs =
      infer_vect infos variances subst (Array.map (mk_clos e) xs) in
  match fterm_of hd with
  | FAtom a ->
    begin match kind a with
      | Sort s -> infer_sort cv_pb variances subst s
      | Meta _ -> infer_stack infos variances subst stk
      | _ -> assert false
    end
  | FEvar ((_,args),e) ->
    let variances = infer_stack infos variances subst stk in
    infer_vect variances e args
  | FRel _ -> infer_stack infos variances subst stk
  | FFlex fl ->
    let variances = infer_table_key infos variances subst fl in
    infer_stack infos variances subst stk
  | FProj (_,c) ->
    let variances = infer_fterm CONV infos variances subst c [] in
    infer_stack infos variances subst stk
  | FLambda _ ->
    let (_,ty,bd) = destFLambda mk_clos hd in
    let variances = infer_fterm CONV infos variances subst ty [] in
    infer_fterm CONV infos variances subst bd []
  | FProd (_,dom,codom) ->
    let variances = infer_fterm CONV infos variances subst dom [] in
    infer_fterm cv_pb infos variances subst codom []
  | FInd (ind, u) ->
    let variances =
      if Instance.is_empty u then variances
      else
        let nargs = stack_args_size stk in
        infer_inductive_instance cv_pb (info_env (fst infos)) variances subst ind nargs u
    in
    infer_stack infos variances subst stk
  | FConstruct (ctor,u) ->
    let variances =
      if Instance.is_empty u then variances
      else
        let nargs = stack_args_size stk in
        infer_constructor_instance_eq (info_env (fst infos)) variances subst ctor nargs u
    in
    infer_stack infos variances subst stk
  | FFix ((_,(_,tys,cl)),e) | FCoFix ((_,(_,tys,cl)),e) ->
    let n = Array.length cl in
    let variances = infer_vect variances e tys in
    let le = (Esubst.subs_liftn n (fst e), snd e) in
    let variances = infer_vect variances le cl in
    infer_stack infos variances subst stk

  (* Removed by whnf *)
  | FLOCKED | FCaseT _ | FLetIn _ | FApp _ | FLIFT _ | FUNIV _
  | FCLOS _ -> assert false

and infer_stack infos variances subst (stk:CClosure.stack) =
  let open CClosure in
  match stk with
  | [] -> variances
  | z :: stk ->
    let (variances, subst) = match z with
      | Zapp v -> (infer_vect infos variances subst v, subst)
      | Zproj _ -> (variances, subst)
      | Zfix (fx,a) ->
        let variances = infer_fterm CONV infos variances subst fx [] in
        (infer_stack infos variances subst a, subst)
      | ZcaseT (ci,p,br,e) ->
        let variances =
            infer_fterm CONV infos variances subst (mk_clos e p) [] in
        (infer_vect infos variances subst (Array.map (mk_clos e) br), subst)
      | Zshift _ -> (variances, subst)
      (* tl subst must exist because subst is derived from get_univ stk *)
      | Zuniv u -> assert false (* (variances, List.tl subst) *)
      | Zupdate _ -> (variances, subst)
    in
    infer_stack infos variances subst stk

and infer_vect infos variances subst v =
  Array.fold_left (fun variances c -> infer_fterm CONV infos variances subst c []) variances v

let infer_term cv_pb env variances c =
  let open CClosure in
  let infos = (create_clos_infos all env, create_tab ()) in
  infer_fterm cv_pb infos variances [] (CClosure.inject (c,Instance.empty)) []

let infer_arity_constructor is_arity env variances arcn =
  let infer_typ typ (env,variances) =
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, infer_term CUMUL env variances typ')
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let typs, codom = Reduction.dest_prod env arcn in
  let env, variances = Context.Rel.fold_outside infer_typ typs ~init:(env, variances) in
  (* If we have Inductive foo@{i j} : ... -> Type@{i} := C : ... -> foo Type@{j}
     i is irrelevant, j is invariant. *)
  if not is_arity then infer_term CUMUL env variances codom else variances

let infer_inductive env mie =
  let open Entries in
  let { mind_entry_params = params;
        mind_entry_inds = entries; } = mie
  in
  let univs =
    match mie.mind_entry_universes with
    | Monomorphic_ind_entry _
    | Polymorphic_ind_entry _ as univs -> univs
    | Cumulative_ind_entry cumi ->
      let uctx = CumulativityInfo.univ_context cumi in
      let uarray = Instance.to_array @@ UContext.instance uctx in
      let env = Environ.push_context uctx env in
      let variances =
        Array.fold_left (fun variances u -> LMap.add u Variance.Irrelevant variances)
          LMap.empty uarray
      in
      let env, _ = Typeops.infer_local_decls env params in
      let variances = List.fold_left (fun variances entry ->
          let variances = infer_arity_constructor true
              env variances entry.mind_entry_arity
          in
          List.fold_left (infer_arity_constructor false env)
            variances entry.mind_entry_lc)
          variances
          entries
      in
      let variances = Array.map (fun u -> LMap.find u variances) uarray in
      Cumulative_ind_entry (CumulativityInfo.make (uctx, variances))
  in
  { mie with mind_entry_universes = univs }
