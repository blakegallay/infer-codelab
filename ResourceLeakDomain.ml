(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

module FiniteBounds = struct
  type t = int

  let leq ~lhs ~rhs = lhs <= rhs

  let join a b = max a b

  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt astate = F.fprintf fmt "%d" astate
end

module BoundsWithTop = struct
  open AbstractDomain.Types
  include AbstractDomain.TopLifted (FiniteBounds)

  let widening_threshold = 5

  let widen ~prev ~next ~num_iters =
    match (prev, next) with
    | Top, _ | _, Top ->
        Top
    | NonTop prev, NonTop next when num_iters < widening_threshold ->
        NonTop (FiniteBounds.join prev next)
    | NonTop _, NonTop _ (* num_iters >= widening_threshold *) ->
        Top
end

(* module AccessPathS = AbstractDomain.FiniteSet(AccessPath) *)
open AbstractDomain.Types
module AccessPathS = PrettyPrintable.MakePPSet (AccessPath)
(* module ResourcesHeld = AbstractDomain.Map(AccessPathS)(BoundsWithTop) *)

module ResourcesHeld = struct 
  module BaseMap = AbstractDomain.Map(AccessPathS)(BoundsWithTop)
  include BaseMap
  let do_merge astate1 astate2 op = BaseMap.fold (
    fun set count disjoint_sets -> 
      let (merge_set, merge_count, other_sets) = 
      BaseMap.fold (
        fun set count (merge_set, merge_count, other_sets) -> 
          if not (AccessPathS.is_empty (AccessPathS.inter set merge_set)) 
            then (AccessPathS.union set merge_set, op count merge_count, other_sets) 
          else (merge_set, merge_count, BaseMap.add set count other_sets) 
        ) disjoint_sets (set, count, BaseMap.empty)
        in BaseMap.add merge_set merge_count other_sets
       )
       (BaseMap.union (fun _ a b -> Some (op a b)) astate1 astate2) BaseMap.empty
  let join astate1 astate2 = do_merge astate1 astate2 BoundsWithTop.join
  let widen ~prev ~next ~num_iters = do_merge prev next (fun a b -> BoundsWithTop.widen ~prev:a ~next:b ~num_iters:num_iters)
end

module ResourcesHeldWithSummary = AbstractDomain.Pair(ResourcesHeld)(AbstractDomain.BooleanOr)

include ResourcesHeldWithSummary

let initial:t = (ResourcesHeld.empty, false)

let add_counts = function 
  | Top, _ | _, Top -> Top 
  | NonTop n, NonTop m -> NonTop (n + m)

let update_count count n = match count with Top -> Top | NonTop held -> NonTop (held + n)

let incr_count count = update_count count 1

let decr_count count = update_count count (-1)

let containing_set access_path held = 
  ResourcesHeld.fold (
    fun set count found -> match found with 
      | Some _ -> found 
      | None -> if AccessPathS.exists (AccessPath.equal access_path) set then Some (set, count) else None
    ) held None

let in_any_set access_path held = 
  ResourcesHeld.exists (
    fun set _ -> AccessPathS.exists (AccessPath.equal access_path) set
    ) held

let acquire_resource access_path state:t =
  match state with (held, returns_resource) -> (begin match containing_set access_path held with 
    | Some (set, old_count) -> ResourcesHeld.add set (incr_count old_count) held
    | None -> ResourcesHeld.add (AccessPathS.add access_path AccessPathS.empty) (NonTop 1) held end, returns_resource)

let release_resource access_path state:t =
  match state with (held, returns_resource) -> (begin match containing_set access_path held with 
  | Some (set, old_count) -> ResourcesHeld.add set (decr_count old_count) held
  | None -> ResourcesHeld.add (AccessPathS.add access_path AccessPathS.empty) (NonTop (-1)) held end, returns_resource)

let assign lhs_access_path rhs_access_path state:t = 
  match state with (held, returns_resource) -> ( begin
    let none_to_empty set_option = match set_option with | Some (set, count) -> (set, count) | None -> (AccessPathS.empty, NonTop 0) in
    let ((set1, count1), (set2, count2)) =
      ((none_to_empty (containing_set lhs_access_path held)),
      (none_to_empty (containing_set rhs_access_path held))) in
    let combined_set = (AccessPathS.union (AccessPathS.add lhs_access_path set1) (AccessPathS.add rhs_access_path set2)) in 
    let combined_count = if AccessPathS.equal set1 set2 then count1 else add_counts (count1, count2) in
    (*
    (Logging.d_printfln "%a in any set: %b\n %a in any set: %b" AccessPath.pp lhs_access_path (in_any_set lhs_access_path held) AccessPath.pp rhs_access_path (in_any_set rhs_access_path held));
    (Logging.d_printfln "set1: %a\n set2: %a\n combined_set %a" AccessPathS.pp set1 AccessPathS.pp set2 AccessPathS.pp combined_set);
    *)
  ResourcesHeld.add combined_set combined_count (ResourcesHeld.remove set2 (ResourcesHeld.remove set1 held)) end, returns_resource)

let has_leak state = match state with 
  (held, _) -> ResourcesHeld.exists (fun _ count -> match count with (NonTop n) when n > 0 -> true | _ -> false) held

let make_summary state = match state with (_, returns_resource) -> returns_resource

type summary = bool

let record_return_resource (state:t) = match state with (held, _) -> (held, true)

let apply_summary (state:t) (summary:summary) (access_path:AccessPath.t) = 
  if summary then acquire_resource access_path state else state

let pp_summary fmt summary = F.fprintf fmt "%b" summary