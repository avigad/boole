
open Boole_lex

module Lexer = Boole_lex

module Parser = Boole_parse


let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      begin try
        Parser.top Lexer.token lexbuf;
        flush stdout;
        flush stderr
      with
        | Toplevel.NotFound s ->
            Printf.eprintf "Error: identifier %s not found\n" s;
            flush stderr
        | Toplevel.TypingError | Toplevel.UnifError -> ()
      end
    done
  with Lexer.Eof ->
    exit 0
