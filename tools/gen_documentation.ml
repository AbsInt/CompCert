(* Tool to generate documentation using coq2html from .v files compiled to compcert theory 

Copies around directories in build system.
*)
let copy_dir source_path target_path = 
  let command = if Sys.win32 then 
    Printf.sprintf "xcopy %s %s /i /q /s /e /y" source_path target_path
  else 
    Printf.sprintf "cp -a -R -f %s %s" source_path target_path
  in let _ = Sys.command(command) in ()

let to_directory platform = match platform with 
  | "aarch64" -> "aarch64"
  | "arm" -> "arm"
  | "peaktop" -> "peaktop"
  | "ppc" -> "powerpc"
  | "ppc_vle" -> "powerpc_vle"
  | "riscV" -> "riscV"
  | "tricore" -> "tricore"
  | "x86_32" -> "x86_32"
  | "x86_64" -> "x86_64"
  | x -> invalid_arg ("unexpected platform '" ^ x ^ "'")

let copy_and_rename new_platform_name file_dir = begin 
  let cwd = Sys.getcwd () in 
  Sys.chdir (Filename.concat cwd "platform");
  copy_dir "." (Filename.concat cwd file_dir);
  Sys.chdir cwd;
  (* rename platform *)
  Sys.rename (Filename.concat file_dir "TargetPlatformCopy") (Filename.concat file_dir new_platform_name)
end


let suffix_files_in_dirs directories suffix = 
  List.map (fun dir -> 
    let files_in_dir = (List.map (fun file -> Filename.concat dir file) (Array.to_list (Sys.readdir dir))) in 
    let v_files = List.filter (fun f -> 
      Sys.is_regular_file f && (Filename.check_suffix f suffix)
    ) files_in_dir in 
    (dir, v_files)
  ) directories

let dirs_and_files_of_suffix dir suffix = 
  let content = (Array.to_list (Sys.readdir dir)) in
  let content_prefixed = if dir = "." then content else List.map (fun l -> Filename.concat dir l) content in
  let directories = List.filter (fun f -> Sys.is_directory f) content_prefixed in 
  (* add prefix dir *)
  Printf.printf "Dirs %s\n" (String.concat ", " directories); 
  suffix_files_in_dirs directories suffix

(* collects .v files and directory names (if directory has .v files) *)
let collect_files_in_dirs dir = 
  let dir_file_pairs = dirs_and_files_of_suffix dir ".v" in 
  (List.filter_map (fun (dir, files) -> if files = [] then None else Some dir) dir_file_pairs, List.concat_map snd dir_file_pairs)

let read_whole_file filename =
  let ch = In_channel.open_bin filename in
  let s = In_channel.input_all ch in 
  In_channel.close ch;
  s

let write_whole_file filename s = 
  let ch = Out_channel.open_bin filename in 
  Out_channel.output_string ch s;
  Out_channel.close ch

let patch_file plat f = 
  let read_content = read_whole_file f in 
  (* Replace all ".TargetPlatformCopy." with ".<platform>."*)
  let regx = Str.regexp {|\.TargetPlatformCopy\.|} in 
  let patched_content = Str.global_replace regx ("."^plat^".") read_content in 
  (* Remove file *)
  Sys.remove f;
  write_whole_file f patched_content

let patch_glob_files dir plat = 
  let glob_file_pairs = dirs_and_files_of_suffix dir ".glob" in 
  let glob_files = List.concat_map snd glob_file_pairs in 
  List.iter (patch_file plat) glob_files

let docs_for_platform new_platform_name = 
  let file_dir = "platform_doc" in 
  (* Copy platform code *)
  copy_and_rename new_platform_name file_dir;
  Sys.chdir file_dir;
  Printf.printf "Copied dirs...\n"; 
  (* Patch references to TargetPlatformCopy to platform name *)
  patch_glob_files "." new_platform_name;
  (* Collect all .v files *)
  let (plat_dirs, plat_files) = collect_files_in_dirs "." in 
  let (flocq_dirs, flocq_files) = collect_files_in_dirs (Filename.concat ".." "flocq") in 
  let menhir_dirs = [Filename.concat ".." "MenhirLib"] in 
  let menhir_files = snd (List.hd (suffix_files_in_dirs menhir_dirs ".v")) in 
  (* Generate docs *)
  let globs = List.map (fun dir -> Filename.concat dir "*.glob") (List.concat [plat_dirs; flocq_dirs; menhir_dirs]) in 
  let files = List.concat [plat_files; flocq_files; menhir_files] in 
  let output_dir = Filename.concat ".." (Filename.concat "doc" "html") in 
  Printf.printf "Creating directory...\n";
  Sys.mkdir output_dir 0o777;
  Printf.printf "Generating docs...\n"; 
  let command = Printf.sprintf "coq2html -d %s -base compcert -short-names %s %s" output_dir (String.concat " " globs) (String.concat " " files) in 
  Printf.printf "Running command: \n%s" command;
  Sys.command command 

  

let _ = 
  if Array.length Sys.argv = 2 then 
    docs_for_platform (to_directory Sys.argv.(1))
  else 
    invalid_arg "expected only one file name argument"


