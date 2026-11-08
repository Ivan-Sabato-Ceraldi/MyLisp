(*SINTASSI ASTRATTA*)
datatype constant = integer of int
                  | boolean of bool;

datatype exp = const of constant
             | var of string
             | sum of exp list (*int args*)
             | prod of exp list (*int args*)
             | equals of exp list (*args*)
             | greatOrEq of exp list (*int args*)
             | lessThan of exp list (*int args*)
             | and_ of exp list (*bool args*)
             | or of exp list (*bool args*)
             | not_ of exp (*bool arg*)
             | let_ of exp (*declared var*) * exp (*assigned value*) * exp (*local block*)
             | lambda of exp (*input var*) * exp (*function body*)
             | lambdaApp of exp (*lambda function*) * exp (*argument*);

datatype env = tuple of string (*var name*) * value
and      value = constVal of constant | closure of exp * exp (*lambda (var,body)*) * env list (*enviroment of declaration*);

exception SyntaxError of string;
exception InternalError of string;

(*HELPERS*)
fun allTrue (l : bool list) = (foldl (fn (x, acc) => x andalso acc) true l);
fun atLeastOneTrue (l : bool list) = (foldl (fn (x, acc) => x orelse acc) false l)

fun extractInt (constVal (integer k)) = k
  | extractInt _ = raise SyntaxError "The '+', '*', '>', '<', '>=', '<=' functions require numerical values as arguments";

fun extractBool (constVal (boolean k)) = k
  | extractBool _ = raise SyntaxError "The 'not', 'and', 'or' functions require boolean values as arguments";



(*REGOLE DI INFERENZA*)
fun eval(E, const(k)) = constVal k
  | eval([], var(x)) = raise SyntaxError("undeclared var :" ^ x)
  | eval(tuple(x, k)::E, var(y)) = if (x = y) then
                                    k
                                   else
                                    eval(E, var(y))
  | eval(E, sum(args)) = applyOperator (E, args, "+")
  | eval(E, prod(args)) = applyOperator (E, args, "*")
  | eval(E, equals(args)) = applyOperator (E, args, "=")
  | eval(E, greatOrEq(args)) = applyOperator (E, args, ">=")
  | eval(E, lessThan(args)) = applyOperator (E, args, "<")
  | eval(E, and_(args)) = applyOperator (E, args, "andalso")
  | eval(E, or(args)) = applyOperator (E, args, "orelse")
  | eval(E, not_(arg)) = constVal (boolean (not (extractBool (eval (E, arg)))))
  | eval(E, let_(var(x), M, N)) = eval(tuple(x , eval(E, M))::E, N)
  | eval(E, let_(_, _, _)) = raise SyntaxError "first arg in a 'let tuple' must be a variable"
  | eval(E, lambda(var(x), M)) = closure(var(x), M, E)
  | eval(E, lambda(_, _)) = raise SyntaxError "first element in a list must be a function or operator"
  | eval(E, lambdaApp(M, N)) = case eval(E, M) of
                             closure(var(x), body, E') => eval(tuple(x, eval(E, N))::E', body)
                           | constVal _ => raise SyntaxError "cannot use a costant value as a function (it's possible too many args were given)"
(*HELPER*)
and applyOperator (E : env list, args : exp list, operator : string) = case args of [] => raise InternalError "cannot have empty list of args" | _ =>
  case operator of
    "+" => constVal (integer (foldl op+ 0 (map (fn x => extractInt (eval(E, x))) args)))
  | "*" => constVal (integer (foldl op* 1 (map (fn x => extractInt (eval(E, x))) args)))
  | "=" => constVal (boolean (allTrue (map (fn x => ((eval(E, (hd args)) = (eval(E, x))))) args)))
  | ">=" => let fun ge (l : int list) = case l of head::[] => [true] | head::rest => (head >= (hd rest)) :: ge(rest)
            in constVal (boolean (allTrue (ge (map (fn x => extractInt (eval(E, x))) args))))
            end
  | "<" => let fun lt (l : int list) = case l of
                                         head::[] => [true]
                                       | head::rest => (head < (hd rest)) :: lt(rest)
            in constVal (boolean (allTrue (lt (map (fn x => extractInt (eval(E, x))) args))))
            end
  | "andalso" => constVal (boolean (allTrue (map (fn x => extractBool (eval(E, x))) args)))
  | "orelse" => constVal (boolean (atLeastOneTrue (map (fn x => extractBool (eval(E, x))) args)));

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
      (case s of
         "true" => const (boolean true)
       | "false" => const (boolean false)
       | _ => (case IntFromString s of
                 SOME n => const (integer n)
               | NONE   => var s))
  | interpretSexp (List (func :: args)) =
      (case args of
         [] => raise SyntaxError "List without arguments"
       | _ => (case func of
                 Atom "+" => sum (map (fn arg => interpretSexp arg) args)
               | Atom "*" => prod (map (fn arg => interpretSexp arg) args)
               | Atom "=" => equals (map (fn arg => interpretSexp arg) args)
               | Atom ">=" => greatOrEq (map (fn arg => interpretSexp arg) args)
               | Atom "<=" => greatOrEq (rev (map (fn arg => interpretSexp arg) args))
               | Atom "<" => lessThan (map (fn arg => interpretSexp arg) args)
               | Atom ">" => lessThan (rev (map (fn arg => interpretSexp arg) args))
               | Atom "and" => and_ (map (fn arg => interpretSexp arg) args)
               | Atom "or" => or (map (fn arg => interpretSexp arg) args)
               | Atom "not" => if (length args = 1)
                               then not_ (interpretSexp (hd args))
                               else raise SyntaxError "the 'not' function takes only one argument"
               | Atom "let" => if (length args = 2 andalso
                                   (case hd args of
                                      List bindings =>
                                        allTrue (map (fn binding => case SexpList binding of
                                                                    SOME l => length l = 2
                                                                  | NONE   => raise SyntaxError "first arg of a 'let' statement must be a list of tuples (variable, expression/constant)")
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
                                         List inputVars => allTrue (map (fn inputVar => case interpretSexp inputVar of var(_) => true | _ => false)
                                                                        inputVars)))
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

(*TEST 1 : *) execute "(let ((succ1 (lambda (x) (+ x 1))) (succ2 (lambda (x) (+ x 1))))  (= succ1 succ2))";

(*TEST 2 : *) execute "(= (lambda (x) (+ x 1)) (lambda (x) (+ x 1)))";

(*TEST 3 : *) execute "(or false (not (= (lambda (x) (+ x 1)) (lambda (x) (+ x 1)))))";