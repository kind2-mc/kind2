(* This file is part of the Kind 2 model checker.

   Copyright (c) 2018 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

module FileId = struct

  type t = int * int
    
  (* Total order on identifiers *)
  let compare (ino1, dev1) (ino2, dev2) =
    match compare ino1 ino2 with
    | 0 -> compare dev1 dev2
    | c -> c

  let equal id1 id2 = compare id1 id2 = 0

end

include FileId

let get_id filename =
  let { Unix.st_dev; Unix.st_ino } = Unix.stat filename in (st_ino, st_dev)

module FileIdSet = Set.Make (FileId)

