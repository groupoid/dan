open Format

let imported_files : string list ref = ref []
let global_simpl_ctx : (string * Simplicialtt.value) list ref = ref []
let global_simpl_env : (string * Simplicialtt.value) list ref = ref []

let rec process_file process_cmd file_path =
  printf "Loading file %s...\n" file_path;
  let ic = open_in file_path in
  let lexbuf = Lexing.from_channel ic in
  try
    let cmds = Parser.file Lexer.token lexbuf in
    close_in ic;
    List.iter (process_cmd file_path) cmds
  with
  | Parsing.Parse_error ->
      close_in ic;
      let pos = lexbuf.Lexing.lex_curr_p in
      failwith (sprintf "Parse error at %s:%d:%d" file_path pos.pos_lnum (pos.pos_cnum - pos.pos_bol))
  | e ->
      close_in ic;
      raise e
