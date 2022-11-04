(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

include AbstractDomain.S

val initial : t

val acquire_resource : AccessPath.t -> t -> t

val release_resource : AccessPath.t -> t -> t

val assign : AccessPath.t -> AccessPath.t -> t -> t

val has_leak : t -> bool

val record_return_resource : t -> t

type summary

val make_summary : t -> summary

val apply_summary : t -> summary -> AccessPath.t -> t

val pp_summary : Format.formatter -> summary -> unit
