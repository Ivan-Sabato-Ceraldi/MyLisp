(*SINTASSI ASTRATTA*)
datatype exp = const of int
             | var of string
             | sum of exp list (*args*)
             | prod of exp list (*args*)
             | let_ of exp (*declared var*) * exp (*assigned value*) * exp (*local block*)
             | lambda of exp (*input var*) * exp (*function body*)
             | lambdaApp of exp (*lambda function*) * exp (*argument*);

datatype env = tuple of string * value
and      value = constVal of int | lambdaVal of exp * exp * env list;

exception SyntaxError of string;

fun extractValue (constVal k) = k
  | extractValue (lambdaVal(_,_,_)) = raise SyntaxError "Cannot treat a lambda function as a costant";

(*REGOLE DI INFERENZA*)
fun eval(E, const(k)) = constVal k
  | eval([], var(x)) = raise SyntaxError("undeclared var :" ^ x)
  | eval(tuple(x, k)::E, var(y)) = if (x = y) then
                                    k
                                   else
                                    eval(E, var(y))
  | eval(E, sum(args)) = constVal (foldl op+ 0 (map (fn x => extractValue (eval(E, x))) args))
  | eval(E, prod(args)) = constVal (foldl op* 1 (map (fn x => extractValue (eval(E, x))) args))
  | eval(E, let_(var(x), M, N)) = eval(tuple(x , eval(E, M))::E, N)
  | eval(E, let_(_, _, _)) = raise SyntaxError "first arg in a 'let tuple' must be a variable"
  | eval(E, lambda(var(x), M)) = lambdaVal(var(x), M, E)
  | eval(E, lambda(_, _)) = raise SyntaxError "first element in a list must be a function or operator"
  | eval(E, lambdaApp(M, N)) = case eval(E, M) of
                             lambdaVal(var(x), body, E') => eval(tuple(x, eval(E, N))::E', body)
                           | constVal _ => raise SyntaxError "cannot use a costant value as a function (it's possible too many args were given)";

(*PARSING*)
datatype s_exp = Atom of string | List of s_exp list;

fun tokenize (s : string) : string list = let
                                            fun pad [] = []
                                              | pad (#"(" :: rest) = #" " :: #"(" :: #" " :: pad rest
                                              | pad (#")" :: rest) = #" " :: #")" :: #" " :: pad rest
                                              | pad (c :: rest) = c :: pad rest
                                            val padded = String.implode(pad((map Char.toLower (String.explode s)) @ [#" "]))
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
                                              (map (fn binding => case SexpList binding of
                                                                    SOME l => length l = 2
                                                                  | NONE   => raise SyntaxError "first arg of a 'let' staement must be a list of tuples (variable, expression/constant)")
                                                   bindings)
                                    | Atom _ => false))
                               then let
                                      val bindings = valOf (SexpList (hd args))
                                      val block = hd (tl args)
                                    in foldr (fn (binding : s_exp, e : exp) =>
                                                let_ (interpretSexp(hd (valOf (SexpList binding))),
                                                interpretSexp(hd (tl (valOf (SexpList binding)))),
                                                e))
                                            (interpretSexp block)
                                            bindings
                                    end
                               else raise SyntaxError "error in the 'let' statement"
               | Atom "lambda" => if (length args = 2 andalso
                                      (case hd args of
                                         List inputVars =>
                                           foldl (fn (x, acc) => x andalso acc)
                                                 true
                                                 (map (fn inputVar => case interpretSexp inputVar of var(_) => true | _ => false) inputVars)))
                                  then let
                                         val inputVars = valOf (SexpList (hd args))
                                         val body = hd (tl args)
                                       in foldr (fn (inputVar : s_exp, e : exp) => lambda ((interpretSexp inputVar), e))
                                                (interpretSexp body)
                                                inputVars
                                       end
                                  else raise SyntaxError "error in the 'lambda' statement"
               | _ => foldl (fn (arg : s_exp, e : exp) => lambdaApp (e, (interpretSexp arg)))
                                                (interpretSexp func)
                                                args));

(*FINAL EXECUTION*)

fun execute (program : string) : value = eval([], interpretSexp(parseSexp program));

(*---FINAL TEST---*)

execute "0";