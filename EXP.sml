(*SINTASSI ASTRATTA*)
datatype exp = const of int
             | var of string
             | sum of exp list
             | prod of exp list
             | let_ of exp * exp * exp;

datatype env = tuple of string * int;

exception SyntaxError of string;

(*REGOLE DI INFERENZA*)
fun eval(e, const(k)) = k
  | eval([], var(x)) = raise SyntaxError("undeclared var :" ^ x)
  | eval(tuple(x, k)::e, var(y)) = if (x = y) then
                                    k
                                   else
                                    eval(e, var(y))
  | eval(e, sum(l)) = foldl op+ 0 (map (fn x => eval(e, x)) l)
  | eval(e, prod(l)) = foldl op* 1 (map (fn x => eval(e, x)) l)
  | eval(e, let_(var(x), M, N)) = eval(tuple(x , eval(e, M))::e, N)
  | eval(e, let_(_, M, N)) = raise SyntaxError("Invalid Syntax");

(*PARSING*)
datatype s_exp = Atom of string | List of s_exp list;

fun tokenize (s : string) : string list = let
                                            fun pad [] = []
                                              | pad (#"(" :: rest) = #" " :: #"(" :: #" " :: pad rest
                                              | pad (#")" :: rest) = #" " :: #")" :: #" " :: pad rest
                                              | pad (c :: rest) = c :: pad rest
                                            val padded = String.implode(pad(String.explode s @ [#" "]))
                                          in
                                            String.tokens Char.isSpace padded
                                          end;

fun parseToken [] = raise SyntaxError "unexpected input end"
  | parseToken ("(" :: elements) = parseList elements
  | parseToken (")" :: elements) = raise SyntaxError "unexpected closing parentesis"
  | parseToken (atom :: elements) = (Atom atom, elements)
and parseList [] = raise SyntaxError "parentesis open but not closed"
  | parseList (")" :: elements) = (List [], elements)
  | parseList tokens = let
                         val (head, rest1) = parseToken tokens
                         val (List tail, rest2) = parseList rest1
                       in
                         (List(head :: tail), rest2)
                       end;

fun parseSexp (s : string) : s_exp = case parseToken (tokenize s) of
                                       (ast, []) => ast
                                     | (_, rest) => raise SyntaxError "Extra Tokens after expression";

(*helpers*)
fun IntFromString (s : string): int option =
    let
        fun parseDigits [] acc = SOME acc
          | parseDigits (c::cs) acc =
            if Char.isDigit c then
                parseDigits cs (acc * 10 + (Char.ord c - Char.ord #"0"))
            else
                NONE
    in
        case String.explode s of
            [] => NONE
          | (#"~" :: cs) => (case parseDigits cs 0 of SOME n => SOME (~n) | NONE => NONE)
          | (#"-" :: cs) => (case parseDigits cs 0 of SOME n => SOME (~n) | NONE => NONE)
          | cs => parseDigits cs 0
    end;

fun SexpLen (Atom _) = 0
  | SexpLen (List l) = length l;

fun SexpList (Atom _) = NONE
  | SexpList (List l) = SOME l;

(*INTEPRETER*)

fun interpretSexp (List []) = raise SyntaxError "Empty List"
  | interpretSexp (Atom s) = 
      (case IntFromString s of
         SOME n => const n
       | NONE   => var s)
  | interpretSexp (List (func :: args)) =
      (case args of
         [] => raise SyntaxError "List without arguments"
       | _ => (case func of
                 Atom "+" => sum (map (fn arg => interpretSexp arg) args)
               | Atom "*" => prod (map (fn arg => interpretSexp arg) args)
               | Atom "let" => if (length args = 2 andalso 
                                   (case hd args of
                                      List bindings => 
                                        foldl (fn (x, acc) => x andalso acc) 
                                              true 
                                              (map (fn b => SexpLen b = 2) bindings)
                                    | Atom _ => false))
                               then let
                                      val bindings = valOf (SexpList (hd args))
                                    in
                                      foldl (fn (binding : s_exp, block : exp) =>
                                              let_ (interpretSexp(hd (valOf (SexpList binding))),
                                              interpretSexp(hd (tl (valOf (SexpList binding)))),
                                              block))
                                            (interpretSexp (hd (tl args)))
                                            bindings
                                    end
                               else raise SyntaxError "error in the 'let' statement"
               | _ => raise SyntaxError "unrecognized operator"));

(*FINAL EXECUTION*)

fun execute (program : string) : int = eval([], interpretSexp(parseSexp program));

(*---FINAL TEST---*)

execute "(let ((x (+ 1 2 3)) (y 4) (z 5)) (+ x y z))";
