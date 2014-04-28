{
  open Boole_parse
  exception Eof
}

rule token = parse
  | [' ' '\t']  { token lexbuf }
  | ['\n' ] { EOL }
  | "fst"   { FST }
  | "snd"   { SND }
  | "Var"   { VAR }
  | "Def"   { DEF }
  | "Check" { CHECK }
  | "Hint"  { HINT }
  | ":="    { COLONEQ }
  | "=>"    { MAPSTO }
  | "->"    { ARROW }
  | "Type"  { TYPE }
  | "Bool"  { BOOL }
  | "~"     { TILDE }
  | "#"     { POUND }
  | "--"    { comment lexbuf; token lexbuf }
  | ['a'-'z''A'-'Z']+ as ident { IDENT(ident) }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQ }
  | ']' { RSQ }
  | '{' { LBRACK }
  | '}' { RBRACK }
  | '<' { LANGLE }
  | '>' { RANGLE }
  | ':' { COLON }
  | '|' { MBAR }
  | ',' { COMMA }
  | '\\' { ABST }
  | '_' { WILD }
  | eof  { raise Eof }

and comment = parse
  | eof  { raise Eof }
  | '\n' { () }
  | _    { comment lexbuf }
