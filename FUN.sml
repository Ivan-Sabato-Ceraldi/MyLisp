(*SINTASSI ASTRATTA*)
datatype constant = integer of int
                  | boolean of bool;

datatype exp = emptyList
             | const of constant
             | var of string
             | sum of exp list (*int args*)
             | prod of exp list (*int args*)
             | equals of exp list (*args*)
             | greatOrEq of exp list (*int args*)
             | lessThan of exp list (*int args*)
             | and_ of exp list (*bool args*)
             | or of exp list (*bool args*)
             | not_ of exp (*bool arg*)
             | ifThenElse of exp (*bool arg*) * exp (*then block*) * exp (*else block*)             
             | let_ of exp (*declared var*) * exp (*assigned value*) * exp (*local block*)
             | multiLet of (exp * exp) list (*bindings*) * exp (*local block*)
             | lambda of exp (*input var*) * exp (*function body*)
             | lambdaApp of exp (*lambda function*) * exp (*argument*)
             | cons of exp (*head*) * exp (*rest*)
             | car of exp (*list*)
             | cdr of exp (*list*)
             | quote of s_exp
             | eval_ of exp (*quoted value*)
and s_exp = Atom of string | List of s_exp list;


datatype enviroment = emptyEnv | extention of enviroment * string * value
and      value = constVal of constant
               | listVal of value list
               | closure of exp * exp (*lambda (var,body)*) * enviroment (*enviroment of declaration*)
               | quotedVal of s_exp;

fun extend (emptyEnv, s , v ) = extention (emptyEnv, s, v)
  | extend (extention(E, s', v'), s, v) = if (s = s')
                                          then extention (E, s, v)
                                          else extention (extend(E, s, v), s', v')

exception SyntaxError of string;
exception InternalError of string;

(*HELPERS*)
fun intFromString (s : string): int option =
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

fun allTrue (l : bool list) = (foldl (fn (x, acc) => x andalso acc) true l);

fun atLeastOneTrue (l : bool list) = (foldl (fn (x, acc) => x orelse acc) false l);

fun hasDuplicates l = case l of
                          [] => false
                        | h::rest => List.exists (fn x => x = h) rest orelse hasDuplicates rest

fun SexpList (Atom _) = NONE
  | SexpList (List l) = SOME l;

fun extractInt (constVal (integer k)) = k
  | extractInt _ = raise SyntaxError "The '+', '*', '>', '<', '>=', '<=' functions require numerical values as arguments";

fun extractBool (constVal (boolean k)) = k
  | extractBool _ = raise SyntaxError "The 'not', 'and', 'or' functions require boolean values as arguments";

(*PARSING*)

fun tokenize (s : string) : string list =
    let
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
  | parseToken (")" :: _) = raise SyntaxError "unexpected closing parentesis"
  | parseToken (atom :: elements) = (Atom atom, elements)
and parseList [] = raise SyntaxError "parentesis open but not closed"
  | parseList (")" :: elements) = (List [], elements)
  | parseList tokens =
      let
        val (head, rest1) = parseToken tokens
        val (tail, rest2) = parseList rest1
      in
        case tail of
            Atom _ => raise InternalError "PARSING ERROR"
          | List l => (List(head :: l), rest2)
      end;

fun parseSexp (s : string) : s_exp =
    case parseToken (tokenize s) of
        (ast, []) => ast
      | (_, _) => raise SyntaxError "Extra Tokens after expression";




(*INTEPRETER*)
fun interpretSexp (List []) = emptyList
  | interpretSexp (Atom s) =
      (case s of
           "true" => const (boolean true)
         | "false" => const (boolean false)
         | _ => (case intFromString s of
                     SOME n => const (integer n)
                   | NONE   => var s))
  | interpretSexp (List (func :: args)) =
      (case args of
           [] => raise SyntaxError "List without arguments"
         | _ => (case func of
                     Atom "+" => sum (map interpretSexp args)
                   | Atom "*" => prod (map interpretSexp args)
                   | Atom "=" => equals (map interpretSexp args)
                   | Atom ">=" => greatOrEq (map interpretSexp args)
                   | Atom "<=" => greatOrEq (rev (map interpretSexp args))
                   | Atom "<" => lessThan (map interpretSexp args)
                   | Atom ">" => lessThan (rev (map interpretSexp args))
                   | Atom "and" => and_ (map interpretSexp args)
                   | Atom "or" => or (map interpretSexp args)
                   | Atom "not" => if (length args = 1)
                                   then not_ (interpretSexp (hd args))
                                   else raise SyntaxError "the 'not' function takes only one argument"
                   | Atom "if" => if (length args = 3)
                                  then ifThenElse (interpretSexp (hd args), interpretSexp (hd (tl args)), interpretSexp (hd (tl (tl args))))
                                  else raise SyntaxError "the 'if' function requires 3 args : condition, then block, else block"
                   | Atom "let" => if (length args = 2 andalso
                                       (case hd args of
                                            List bindings =>
                                              allTrue (map (fn binding => case SexpList binding of
                                                                              SOME l => length l = 2
                                                                            | NONE   => raise SyntaxError "first arg of a 'let' statement must be a list of tuples (variable, expression/constant)")
                                                           bindings)
                                          | Atom _ => false))
                                   then
                                     let
                                       val bindings = (map (fn (List [x, v]) => (interpretSexp x, interpretSexp v) | _ => raise InternalError "error in let bindings") (valOf (SexpList (hd args))))
                                       val block = hd (tl args)
                                     in 
                                       multiLet(bindings, interpretSexp block)
                                     end
                                   else raise SyntaxError "error in the 'let' statement"
                   | Atom "let*" => if (length args = 2 andalso
                                        (case hd args of
                                             List bindings =>
                                               allTrue (map (fn binding => case SexpList binding of
                                                                               SOME l => length l = 2
                                                                             | NONE   => raise SyntaxError "first arg of a 'let*' statement must be a list of tuples (variable, expression/constant)")
                                                            bindings)
                                           | Atom _ => false))
                                    then
                                      let
                                        val bindings = valOf (SexpList (hd args))
                                        val block = hd (tl args)
                                      in
                                        foldr (fn (binding : s_exp, e : exp) =>
                                                  let_ (interpretSexp(hd (valOf (SexpList binding))),
                                                        interpretSexp(hd (tl (valOf (SexpList binding)))),
                                                        e))
                                              (interpretSexp block)
                                              bindings
                                      end
                                    else raise SyntaxError "error in the 'let*' statement"
                   | Atom "lambda" => if (length args = 2 andalso
                                          (case hd args of
                                               List inputVars => allTrue (map (fn inputVar => case interpretSexp inputVar of var _ => true | _ => false)
                                                                              inputVars)
                                             | Atom _ => false))
                                      then
                                        let
                                          val inputVars = valOf (SexpList (hd args))
                                          val body = hd (tl args)
                                        in
                                          foldr (fn (inputVar : s_exp, e : exp) => lambda ((interpretSexp inputVar), e))
                                                (interpretSexp body)
                                                inputVars
                                        end
                                      else raise SyntaxError "error in the 'lambda' statement"
                   | Atom "cons" => if (length args = 2)
                                    then cons(interpretSexp (hd args), interpretSexp (hd (tl args)))
                                    else raise SyntaxError "the 'cons' statement requires 2 args"
                   | Atom "list" => foldl cons emptyList (map interpretSexp args)
                   | Atom "car" => if (length args = 1)
                                    then car(interpretSexp (hd args))
                                    else raise SyntaxError "the 'cons' statement requires 1 arg"
                   | Atom "cdr" => if (length args = 1)
                                    then cdr(interpretSexp (hd args))
                                    else raise SyntaxError "the 'cons' statement requires 1 arg"
                   | Atom "quote" => quote(List args)
                   | Atom "eval" => if (length args = 1)
                                    then eval_(interpretSexp (hd args))
                                    else raise SyntaxError "the 'eval' statement requires 1 arg"
                   | _ => foldl (fn (arg : s_exp, e : exp) => lambdaApp (e, (interpretSexp arg)))
                                (interpretSexp func)
                                args));
                    

(*REGOLE DI INFERENZA*)
fun eval(_, emptyList) = listVal []
  | eval(_ , const k) = constVal k
  | eval(emptyEnv, var x) = raise SyntaxError("undeclared var :" ^ x)
  | eval(extention(E, x, v), var y) = if (x = y) then
                                        v
                                      else
                                        eval(E, var y)
  | eval(E, sum args) = applyOperator (E, args, "+")
  | eval(E, prod args) = applyOperator (E, args, "*")
  | eval(E, equals args) = applyOperator (E, args, "=")
  | eval(E, greatOrEq args) = applyOperator (E, args, ">=")
  | eval(E, lessThan args) = applyOperator (E, args, "<")
  | eval(E, and_ args) = applyOperator (E, args, "andalso")
  | eval(E, or args) = applyOperator (E, args, "orelse")
  | eval(E, not_ arg) = constVal (boolean (not (extractBool (eval (E, arg)))))
  | eval(E, ifThenElse(condition, M, N)) = (if extractBool (eval (E, condition))
                                            then eval(E, M)
                                            else eval(E, N))
  | eval(E, let_(var x, M, N)) = eval(extend(E, x , eval(E, M)), N)
  | eval(_, let_(_, _, _)) = raise SyntaxError "first arg in a 'let* tuple' must be a variable"
  | eval(E, multiLet(bindings, M)) = if (not (hasDuplicates (map (fn (x,_) => x) bindings)))
                                     then
                                       let
                                         fun addBindings (e, l) =
                                             case l of
                                                 [] => e
                                               | (V, N)::rest => case V of
                                                                     var x => addBindings(extend(e, x, eval(E, N)), rest)
                                                                   | _ => raise SyntaxError "first arg in a 'let tuple' must be a variable"
                                       in
                                         eval(addBindings(E, bindings), M)
                                       end
                                     else raise SyntaxError "there cannot be duplicates variables in the 'let' statemet, use 'let*' instead"
  | eval(E, lambda(var x, M)) = closure(var x, M, E)
  | eval(_, lambda(_, _)) = raise SyntaxError "first element in a list must be a function or operator"
  | eval(E, lambdaApp(M, N)) = (case eval(E, M) of
                                   closure(var x, body, E') => eval(extend(E', x , eval(E, N)), body)
                                 | closure(_,_,_) => raise InternalError "illegal closure instance"
                                 | _ => raise SyntaxError "the first element of a list must be a function (it's possible too many args were given)")
  | eval(E, cons(M, emptyList)) = listVal((eval(E, M)) :: [])
  | eval(E, cons(M, N)) = (case eval(E, N) of
                             listVal l => listVal((eval(E, M)) :: l)
                           | _ => raise SyntaxError "the secong arg of a 'cons' statement should be a list value")
  | eval(E, car M) = (case eval(E, M) of 
                        listVal [] => raise SyntaxError "'car' used on an empty list"
                      | listVal (h::_) => h
                      | quotedVal (List []) => raise SyntaxError "'car' used on an empty list"
                      | quotedVal (List (h::_)) => quotedVal h
                      | _ => raise SyntaxError "cannot use 'car' on an atomic value")
  | eval(E, cdr M) = (case eval(E, M) of 
                        listVal [] => raise SyntaxError "'cdr' used on an empty list"
                      | listVal (_::r) => listVal r
                      | quotedVal (List []) => raise SyntaxError "'cdr' used on an empty list"
                      | quotedVal (List (_::r)) => quotedVal(List r)
                      | _ => raise SyntaxError "cannot use 'cdr' on an atomic value")
  | eval(_, quote S) = quotedVal S
  | eval(E, eval_ M) = (case eval(E, M) of
                          quotedVal S => eval(E, (interpretSexp S))
                        | _ => raise SyntaxError "first arg of a 'eval' statement must be a quoted value")

(*HELPER*)
and applyOperator (E : enviroment, args : exp list, operator : string) =
    case args of
        [] => raise InternalError "cannot have empty list of args"
      | _ =>
          case operator of
              "+" => constVal (integer (foldl op+ 0 (map (fn x => extractInt (eval(E, x))) args)))
            | "*" => constVal (integer (foldl op* 1 (map (fn x => extractInt (eval(E, x))) args)))
            | "=" => constVal (boolean (allTrue (map (fn x => (eval(E, (hd args)) = (eval(E, x)))) args)))
            | ">=" => let
                        fun ge (l : int list) = case l of
                                                    [] => raise InternalError "error in func ge"
                                                  | _::[] => [true]
                                                  | head::rest => (head >= (hd rest)) :: ge rest
                      in
                        constVal (boolean (allTrue (ge (map (fn x => extractInt (eval(E, x))) args))))
                      end
            | "<" => let
                       fun lt (l : int list) = case l of
                                                   [] => raise InternalError "error in func ge"
                                                 | _::[] => [true]
                                                 | head::rest => (head < (hd rest)) :: lt rest
                     in
                       constVal (boolean (allTrue (lt (map (fn x => extractInt (eval(E, x))) args))))
                     end
            | "andalso" => constVal (boolean (allTrue (map (fn x => extractBool (eval(E, x))) args)))
            | "orelse" => constVal (boolean (atLeastOneTrue (map (fn x => extractBool (eval(E, x))) args)))
            | _ => raise InternalError "operator not implemented";


(*FINAL EXECUTION*)
fun executeStr (program : string) : value = eval(emptyEnv, interpretSexp(parseSexp program));

fun expToString (const (integer n)) = (Int.toString n)
  | expToString (const (boolean b)) = (Bool.toString b)
  | expToString (var x) = x
  | expToString (sum l) = "(+ " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (prod l) = "(* " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (equals l) = "(= " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (greatOrEq l) = "(>= " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (lessThan l) = "(< " ^ (foldr op^ ")" (map expToString l))
  | expToString (and_ l) = "(and " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (or l) = "(or " ^ (foldr (fn (x, acc) => x ^ " " ^ acc) ")" (map expToString l))
  | expToString (ifThenElse (M, N, O)) = "(if " ^ (expToString M) ^ " " ^ (expToString N) ^ " " ^ (expToString O) ^ ")"
  | expToString (let_ (M, N, O)) = "(let* (" ^ (expToString M) ^ " " ^ (expToString N) ^ ") " ^ (expToString O) ^ ")"
  | expToString (multiLet (l, M)) = "(let (" ^ (foldr op^ ")" (map (fn (x, y) => "(" ^ (expToString x) ^ " " ^ (expToString y) ^ ")") l)) ^ " " ^ (expToString M) ^ ")"
  | expToString (lambda (M, N)) = "(lambda (" ^ (expToString M) ^ ")" ^ (expToString N) ^ ")"
  | expToString (lambdaApp (M, N)) = "(" ^ (expToString M) ^ " " ^ (expToString N) ^ ")"
  | expToString _ = ""

fun envToString emptyEnv = ""
  | envToString (extention(E, s, v)) = envToString E ^ "(" ^ s ^ " : " ^ (#2 (valueToString v)) ^ ")"
and valueToString (constVal (integer n)) = ("costant : " , Int.toString n)
  | valueToString (constVal (boolean b)) = ("costant : " , Bool.toString b)
  | valueToString (listVal l) = ("list : (" , foldl (fn (x, acc) => x ^ " " ^ acc) ")" (map (fn v => #2 (valueToString v)) l))
  | valueToString (closure (var x, body, E)) = ("closure :" , "[" ^ x ^ ", " ^ (expToString body) ^ ", {" ^ (envToString E) ^ "}]")
  | valueToString (closure(_,_,_)) = raise InternalError "error in the closure"
  | valueToString (quotedVal (Atom s)) = ("symbol :" , s )
  | valueToString (quotedVal (List l)) = ("list : (" , foldl (fn (x, acc) => x ^ " " ^ acc) ")" (map (fn v => #2 (valueToString v)) (map quotedVal l)))



fun executeFile (path : string) =
    if String.isSuffix ".mylisp" path then
      let
        val instream = TextIO.openIn path
        val program = (TextIO.inputAll instream)
                      handle exn => (TextIO.closeIn instream; raise exn)
        val () = TextIO.closeIn instream
      in
        print ("\027[32mOUTPUT "^ path ^ " = " ^ op ^ (valueToString (executeStr program)) ^ "\027[0m\n")
        handle SyntaxError m   => print ("\027[31mSyntaxError: "^ m ^ "\027[0m\n")
             | InternalError m => print ("\027[31mInternalError: "^ m ^ "\027[0m\n")
             | exn => raise exn
      end
    else
      print "\027[31mFileError: expected a .mylisp extention\027[0m\n";

(*---FINAL TEST---*)
executeFile "test.mylisp";