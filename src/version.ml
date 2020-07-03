let package_name = "kind2"

let version =
  (match Build_info.V1.version () with
   | None -> "<version>"
   | Some v -> Build_info.V1.Version.to_string v)
