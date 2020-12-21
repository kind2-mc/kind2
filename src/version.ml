let package_name = "kind2"

let base_version = "v1.2.0"

let version =
  (match Build_info.V1.version () with
   | None -> base_version ^ "~dev"
   | Some v ->
     let str = Build_info.V1.Version.to_string v in
     if (String.length str >= 3 && str.[2]='.') then str
     else base_version ^ "-g" ^ str
  )
