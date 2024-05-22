let package_name = "kind2"

let base_version = "v2.2.0"

let version =
  (match Build_info.V1.version () with
   | None -> (* No git *) base_version
   | Some v ->
     let str = Build_info.V1.Version.to_string v in
     let str_len = String.length str in
     if (str_len >= 3 && str.[2]='.') then
      (* Tag with v prefix *)
      str
     else if (str_len >= 2 && str.[1]='.') then
      (* Dune-project version without v prefix; add v prefix *)
      "v" ^ str
     else (* Git without tags *)
      base_version ^ "-g" ^ str
  )
