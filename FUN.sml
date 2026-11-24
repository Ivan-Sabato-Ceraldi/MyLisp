(*SINTASSI ASTRATTA*)
datatype constant = integer of int
                  | boolean of bool
                  | ratio of int * int
                  | realNum of real
                  | stringVal of string;

datatype exp = emptyList
             | const of constant
             | var of string
             | opposite of exp (*num*)
             | inverse of exp (*num*)
             | sum of exp list (*num args*)
             | prod of exp list (*num args*)
             | modulus of exp * exp (*m mod n*)
             | strConcat of exp list (*string args*)
             | strExplode of exp (*string*)
             | equals of exp list (*args*)
             | greatOrEq of exp list (*num args*)
             | lessThan of exp list (*num args*)
             | and_ of exp list (*bool args*)
             | or of exp list (*bool args*)
             | not_ of exp (*bool arg*)
             | ifThenElse of exp (*bool arg*) * exp (*then block*) * exp (*else block*)             
             | let_ of exp (*declared var*) * exp (*assigned value*) * exp (*local block*)
             | multiLet of (exp * exp) list (*bindings*) * exp (*local block*)
             | letRec of (exp * exp) list (*bindings*) * exp (*local block*)
             | lambda of exp (*input var*) * exp (*function body*)
             | lambdaApp of exp (*lambda function*) * exp (*argument*)
             | cons of exp (*head*) * exp (*rest*)
             | car of exp (*list*)
             | cdr of exp (*list*)
             | quote of s_exp
             | eval_ of exp (*quoted value*)
             | typeCheck of string * exp (*predicate, arg*)
             | import of exp list (*file paths*) * exp (*body*)
             | export of exp list (*exported variables*)
             | exportAll
             | error_ of exp (*error message string*)
and s_exp = Atom of string | List of s_exp list;


datatype environment = emptyEnv
                     | eagerextension of environment * string * value
                     | lazyextension of environment * (string * exp) list
and      value = constVal of constant
               | symbolVal of string
               | listVal of value list
               | closure of exp * exp (*lambda (var,body)*) * environment (*environment of declaration*)
               | envVal of environment;

fun extend (emptyEnv, s, v) = eagerextension (emptyEnv, s, v)
  | extend (eagerextension(E, s', v'), s, v) =
      if (s = s')
      then eagerextension (E, s, v)
      else eagerextension (extend(E, s, v), s', v')
  | extend (lazyextension(E, bindings), s, v) =
      if List.exists (fn (s', _) => s = s') bindings
      then eagerextension (lazyextension(extend(E, s, v), bindings), s, v)
      else lazyextension (extend(E, s, v), bindings)

fun recExtend (E, []) = E
  | recExtend (E, bindings) =
      let
        val shadowedNames = map (fn (name, _) => name) bindings
        fun removeVars emptyEnv = emptyEnv
          | removeVars (eagerextension(env, s', v')) =
              if List.exists (fn name => name = s') shadowedNames
              then removeVars env
              else eagerextension(removeVars env, s', v')
          | removeVars (lazyextension(env, b)) =
              lazyextension(removeVars env, b)
        val E' = removeVars E
      in
        lazyextension(E', bindings)
      end

fun mergeEnv (baseEnv, emptyEnv) = baseEnv
  | mergeEnv (baseEnv, eagerextension (rest, x, v)) =
      extend (mergeEnv (baseEnv, rest), x, v)
  | mergeEnv (baseEnv, lazyextension (rest, bindings)) =
      recExtend (mergeEnv (baseEnv, rest), bindings);

exception SyntaxError of string;
exception RuntimeError of string;
exception InternalError of string;

(*HELPERS*)
val reservedWords = [
    "true", "false",
    "if", "cond", "else", "let", "let*", "letrec", "lambda", "quote", "eval",
    "list",
    "and", "or",
    "import", "export"
];

fun isReserved (s : string) : bool =
    List.exists (fn kw => kw = s) reservedWords;

val primNames : string list = [
    "+", "-", "*", "/", "mod",
    "=", "<", ">=", "<=", ">",
    "not",
    "cons", "car", "cdr",
    "concat", "explode",
    "null?", "atom?", "int?", "ratio?", "real?", "number?", "bool?", "symbol?", "list?", "string?"
];

fun isPrim (s : string) : bool =
    List.exists (fn p => p = s) primNames;

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
        | (#"-" :: []) => NONE
        | (#"-" :: cs) => (case parseDigits cs 0 of SOME n => SOME (~n) | NONE => NONE)
        | cs => parseDigits cs 0
    end;

fun allTrue (l : bool list) = (foldl (fn (x, acc) => x andalso acc) true l);

fun atLeastOneTrue (l : bool list) = (foldl (fn (x, acc) => x orelse acc) false l);

fun hasDuplicates l =
    case l of
        [] => false
      | h::rest => List.exists (fn x => x = h) rest orelse hasDuplicates rest

fun sExpList (Atom _) = NONE
  | sExpList (List l) = SOME l;

fun ratioFromString (s : string) : (int * int) option =
    case String.fields (fn c => c = #"/") s of
        [numStr, denStr] =>
          (case (intFromString numStr, intFromString denStr) of
               (SOME n, SOME d) => SOME (n, d)
             | _ => NONE)
      | _ => NONE;

fun realFromString (s : string) : real option =
    let
      val chars = String.explode s
      val hasDotOrExp = List.exists (fn c => c = #"." orelse c = #"e") chars
      fun isValidRealChar c =
          Char.isDigit c orelse c = #"." orelse c = #"-" orelse c = #"+" orelse c = #"e"
      fun reader [] = NONE
        | reader (c::cs) = SOME (c, cs)
    in
      if hasDotOrExp andalso allTrue (map isValidRealChar chars) then
        case Real.scan reader chars of
            SOME (r, []) => SOME r
          | _ => NONE
      else
        NONE
    end;

fun gcd (a : int, 0) = Int.abs a
  | gcd (a : int, b : int) = gcd (b, a mod b);

fun normalizeRatio (_, 0) = raise SyntaxError "division by zero in ratio"
  | normalizeRatio (num, den) =
      let
        val sign = if den < 0 then ~1 else 1
        val n = sign * num
        val d = sign * den
        val g = gcd (n, d)
        val n' = n div g
        val d' = d div g
      in
        if d' = 1 then integer n'
        else ratio (n', d')
      end;

fun toPair (integer n) = (n, 1)
  | toPair (ratio (n, d)) = (n, d)
  | toPair (realNum _) = raise InternalError "numerical arguments required in 'ToPair'"
  | toPair _ = raise InternalError "numerical arguments required in 'ToPair'";

fun toReal (integer n) = Real.fromInt n
  | toReal (ratio (n, d)) = (Real.fromInt n) / (Real.fromInt d)
  | toReal (realNum r) = r
  | toReal _ = raise InternalError "numerical argument required in 'toReal'";

fun addRatio (c1 : constant, c2 : constant) : constant =
    let
      val (n1, d1) = toPair c1
      val (n2, d2) = toPair c2
      val g = gcd (d1, d2)
      val lcm = (d1 div g) * d2
      val num = n1 * (lcm div d1) + n2 * (lcm div d2)
    in
      normalizeRatio (num, lcm)
    end;

fun prodRatio (c1 : constant, c2 : constant) : constant =
    let
      val (n1, d1) = toPair c1
      val (n2, d2) = toPair c2
      val g1 = gcd (n1, d2)
      val g2 = gcd (n2, d1)
    in
      normalizeRatio ((n1 div g1) * (n2 div g2), (d1 div g2) * (d2 div g1))
    end;

fun addNumber (realNum r1, c2) = realNum (r1 + toReal c2)
  | addNumber (c1, realNum r2) = realNum (toReal c1 + r2)
  | addNumber (c1, c2) = addRatio (c1, c2);

fun prodNumber (realNum r1, c2) = realNum (r1 * toReal c2)
  | prodNumber (c1, realNum r2) = realNum (toReal c1 * r2)
  | prodNumber (c1, c2) = prodRatio (c1, c2);

fun geNumber (realNum r1, c2) = r1 >= toReal c2
  | geNumber (c1, realNum r2) = toReal c1 >= r2
  | geNumber (c1, c2) =
      let
        val (n1, d1) = toPair c1
        val (n2, d2) = toPair c2
      in
        n1 * d2 >= n2 * d1
      end;

fun ltNumber (realNum r1, c2) = r1 < toReal c2
  | ltNumber (c1, realNum r2) = toReal c1 < r2
  | ltNumber (c1, c2) =
      let
        val (n1, d1) = toPair c1
        val (n2, d2) = toPair c2
      in
        n1 * d2 < n2 * d1
      end;

fun equalConstants (integer n1, integer n2) = n1 = n2
  | equalConstants (boolean b1, boolean b2) = b1 = b2
  | equalConstants (ratio (n1, d1), ratio (n2, d2)) = n1 = n2 andalso d1 = d2
  | equalConstants (realNum r1, c2 as integer _) = Real.== (r1, toReal c2)
  | equalConstants (realNum r1, c2 as ratio _) = Real.== (r1, toReal c2)
  | equalConstants (realNum r1, c2 as realNum _) = Real.== (r1, toReal c2)
  | equalConstants (c1 as integer _, realNum r2) = Real.== (toReal c1, r2)
  | equalConstants (c1 as ratio _, realNum r2) = Real.== (toReal c1, r2)
  | equalConstants (stringVal s1, stringVal s2) = (s1 = s2)
  | equalConstants _ = false;

fun equalValues (constVal c1, constVal c2) = equalConstants (c1, c2)
  | equalValues (listVal [], listVal []) = true
  | equalValues (listVal (h1::t1), listVal (h2::t2)) = equalValues (h1, h2) andalso equalValues (listVal t1, listVal t2)
  | equalValues (symbolVal s1, symbolVal s2) = (s1 = s2)
  | equalValues _ = false;
    

fun extractNumber (constVal (integer k)) = integer k
  | extractNumber (constVal (ratio r)) = ratio r
  | extractNumber (constVal (realNum r)) = realNum r
  | extractNumber _ = raise SyntaxError "The '+', '-', '/' , '*', '>', '<', '>=', '<=' functions require numerical values as arguments";

fun extractInt (constVal (integer k)) = k
  | extractInt _ = raise SyntaxError "The 'mod' function require numerical values as arguments";

fun extractBool (constVal (boolean k)) = k
  | extractBool _ = raise SyntaxError "The 'not', 'and', 'or' functions require boolean values as arguments";

fun extractStr (constVal (stringVal k)) = k
  | extractStr _ = raise SyntaxError "The 'concat', 'explode' functions require string values as arguments";

fun escapeString (s : string) : string =
    String.translate (fn #"\"" => "\\\""
                       | #"\\" => "\\\\"
                       | #"\n" => "\\n"
                       | #"\t" => "\\t"
                       | c     => String.str c) s;

fun constToString (integer n) =
      if n < 0 then "-" ^ Int.toString (~n)
      else Int.toString n
  | constToString (boolean b) = Bool.toString b
  | constToString (ratio (n, m)) =
      if n < 0 then "-" ^ (Int.toString (~n)) ^ "/" ^ (Int.toString m)
      else (Int.toString n) ^ "/" ^ (Int.toString m)
  | constToString (realNum r) =
      if r < 0.0 then "-" ^ Real.toString (~r)
      else Real.toString r
  | constToString (stringVal s) = "\"" ^ escapeString s ^ "\"";

fun stringFromAtom (s : string) : string option =
    let
      val len = String.size s
    in
      if len >= 2 andalso String.sub (s, 0) = #"\"" andalso String.sub (s, len - 1) = #"\"" then
        SOME (String.substring (s, 1, len - 2))
      else
        NONE
    end;

fun readFile (path : string) : string =
    let
      val instream = (TextIO.openIn path)
                     handle IO.Io _ => raise RuntimeError ("file not found or unreadable: " ^ path)
      val content = (TextIO.inputAll instream)
                    handle exn => (TextIO.closeIn instream; raise exn)
      val () = TextIO.closeIn instream
    in
      content
    end;

(*PARSING*)
fun tokenize (s : string) : string list =
    let
      fun readString [] _ = raise SyntaxError "unclosed string literal"
        | readString (#"\\" :: #"\"" :: rest) acc = readString rest (#"\"" :: acc)
        | readString (#"\\" :: #"n"  :: rest) acc = readString rest (#"\n" :: acc)
        | readString (#"\\" :: #"t"  :: rest) acc = readString rest (#"\t" :: acc)
        | readString (#"\\" :: #"\\" :: rest) acc = readString rest (#"\\" :: acc)
        | readString (#"\\" :: c :: _) _ =
            raise SyntaxError ("invalid escape sequence \\" ^ String.str c)
        | readString (#"\"" :: rest) acc =
            let
              val content = String.implode (rev (#"\"" :: acc))
            in
              (content, rest)
            end
        | readString (c :: rest) acc = readString rest (c :: acc)

      fun skipComment [] = []
        | skipComment (#"\n" :: rest) = rest
        | skipComment (_ :: rest) = skipComment rest

      fun scan [] current tokens =
            let
              val finalTokens =
                  if null current then tokens
                  else String.implode (rev current) :: tokens
            in
              rev finalTokens
            end
        | scan (#";" :: rest) current tokens =
            let
              val tokens' =
                  if null current then tokens
                  else String.implode (rev current) :: tokens
            in
              scan (skipComment rest) [] tokens'
            end
        | scan (#"\"" :: rest) current tokens =
            let
              val tokens' =
                  if null current then tokens
                  else String.implode (rev current) :: tokens
              val (strTok, rest') = readString rest [#"\""]
            in
              scan rest' [] (strTok :: tokens')
            end
        | scan (c :: rest) current tokens =
            if Char.isSpace c then
              let
                val tokens' =
                    if null current then tokens
                    else String.implode (rev current) :: tokens
              in
                scan rest [] tokens'
              end
            else if c = #"(" orelse c = #")" orelse c = #"'" then
              let
                val tokens' =
                    if null current then tokens
                    else String.implode (rev current) :: tokens
                val delim = String.str c
              in
                scan rest [] (delim :: tokens')
              end
            else
              scan rest ((Char.toLower c) :: current) tokens
    in
      scan (String.explode s) [] []
    end;

fun parseToken [] = raise SyntaxError "unexpected input end"
  | parseToken ("'" :: elements) =
      let
        val (quotedExpr, rest) = parseToken elements
      in
        (List [Atom "quote", quotedExpr], rest)
      end
  | parseToken ("(" :: elements) = parseList elements
  | parseToken (")" :: _) = raise SyntaxError "unexpected closing parenthesis"
  | parseToken (atom :: elements) = (Atom atom, elements)
and parseList [] = raise SyntaxError "parenthesis open but not closed"
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
         | _ => (case stringFromAtom s of
                     SOME str => const (stringVal str)
                   | NONE     => (case intFromString s of
                                      SOME n => const (integer n)
                                    | NONE   => (case ratioFromString s of
                                                     SOME (n, d) => const (normalizeRatio (n, d))
                                                   | NONE        => (case realFromString s of
                                                                         SOME r => const (realNum r)
                                                                       | NONE   => if (isReserved s)
                                                                                   then raise SyntaxError ("cannot use '" ^ s ^ "' as a variable name")
                                                                                   else var s)))))
  | interpretSexp (List (func :: args)) =
      (case args of
           [] => (case func of
                      Atom "+" => const(integer 0)
                    | Atom "*" => const(integer 1)
                    | Atom "concat" => const(stringVal "")
                    | Atom "export" => export []
                    | _ => raise SyntaxError "List without arguments")
         | _ => (case func of
                     Atom "-" =>
                       (case args of
                            [] => raise InternalError "check InterpretSexp of '-'"
                          | h::[] => opposite(interpretSexp h)
                          | h::rest => sum[(interpretSexp h), (opposite (sum (map interpretSexp rest)))])
                   | Atom "/" =>
                       (case args of
                            [] => raise InternalError "check InterpretSexp of '-'"
                          | h::[] => inverse(interpretSexp h)
                          | h::rest => prod[(interpretSexp h), (inverse (prod (map interpretSexp rest)))])
                   | Atom "+" => sum (map interpretSexp args)
                   | Atom "*" => prod (map interpretSexp args)
                   | Atom "mod" => if (length args = 2)
                                   then modulus(interpretSexp (hd args), interpretSexp (hd (tl args)))
                                   else raise SyntaxError "the 'mod' function requires 2 args"
                   | Atom "concat" => strConcat (map interpretSexp args)
                   | Atom "explode" => if (length args = 1)
                                       then strExplode (interpretSexp (hd args))
                                       else raise SyntaxError "the 'explode' function requires 1 arg"
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
                   | Atom "cond" => if(allTrue (map (fn arg => case sExpList arg of
                                                                              SOME l => length l = 2
                                                                            | NONE   => raise SyntaxError "args of a 'cond' statement must be a list of tuples (condition, expression)")
                                                           args))
                                    then
                                      let
                                        val condTuples = (map (fn (List [x, v]) => (x, v) | _ => raise InternalError "error in let condTuples") args)
                                        fun nestIf l =
                                          (case l of
                                               [] => raise InternalError "check interpretSexp of cond"
                                             | (condition, body)::[] => (case condition of Atom "else" => interpretSexp body | _ => raise SyntaxError "'cond' staement must finish with 'else' as a condition")
                                             | (condition , body)::rest => ifThenElse((interpretSexp condition), (interpretSexp body), (nestIf rest)))
                                      in nestIf condTuples
                                      end
                                    else raise SyntaxError "args of a 'cond' statement must be a list of tuples (condition, expression)"
                   | Atom "let" => if (length args = 2 andalso
                                       (case hd args of
                                            List bindings =>
                                              allTrue (map (fn binding => case sExpList binding of
                                                                              SOME l => length l = 2
                                                                            | NONE   => raise SyntaxError "first arg of a 'let' statement must be a list of tuples (variable, expression)")
                                                           bindings)
                                          | Atom _ => false))
                                   then
                                     let
                                       val bindings = (map (fn (List [x, v]) => (interpretSexp x, interpretSexp v) | _ => raise InternalError "error in let bindings") (valOf (sExpList (hd args))))
                                       val block = hd (tl args)
                                     in 
                                       multiLet(bindings, interpretSexp block)
                                     end
                                   else raise SyntaxError "error in the 'let' statement"
                   | Atom "let*" => if (length args = 2 andalso
                                        (case hd args of
                                             List bindings =>
                                               allTrue (map (fn binding => case sExpList binding of
                                                                               SOME l => length l = 2
                                                                             | NONE   => raise SyntaxError "first arg of a 'let*' statement must be a list of tuples (variable, expression)")
                                                            bindings)
                                           | Atom _ => false))
                                    then
                                      let
                                        val bindings = valOf (sExpList (hd args))
                                        val block = hd (tl args)
                                      in
                                        foldr (fn (binding : s_exp, e : exp) =>
                                                  let_ (interpretSexp(hd (valOf (sExpList binding))),
                                                        interpretSexp(hd (tl (valOf (sExpList binding)))),
                                                        e))
                                              (interpretSexp block)
                                              bindings
                                      end
                                    else raise SyntaxError "error in the 'let*' statement"
                   | Atom "letrec" => if (length args = 2 andalso
                                          (case hd args of
                                               List bindings =>
                                                 allTrue (map (fn binding => case sExpList binding of
                                                                                 SOME l => length l = 2
                                                                               | NONE   => raise SyntaxError "first arg of a 'letrec' statement must be a list of tuples (variable, lambda)")
                                                              bindings)
                                             | Atom _ => false))
                                      then
                                        let
                                          val bindings = (map (fn (List [x, v]) => (interpretSexp x, interpretSexp v) | _ => raise InternalError "error in let bindings") (valOf (sExpList (hd args))))
                                          val block = hd (tl args)
                                        in 
                                          letRec(bindings, interpretSexp block)
                                        end
                                      else raise SyntaxError "error in the 'letrec' statement"
                   | Atom "lambda" => if (length args = 2 andalso
                                          (case hd args of
                                               List (inputVars as _::_) =>
                                                 allTrue (map (fn inputVar => case interpretSexp inputVar of var _ => true | _ => false)
                                                              inputVars)
                                             | _ => false))
                                      then
                                        let
                                          val inputVars = valOf (sExpList (hd args))
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
                   | Atom "list" => foldr cons emptyList (map interpretSexp args)
                   | Atom "car" => if (length args = 1)
                                   then car(interpretSexp (hd args))
                                   else raise SyntaxError "the 'car' statement requires 1 arg"
                   | Atom "cdr" => if (length args = 1)
                                   then cdr(interpretSexp (hd args))
                                   else raise SyntaxError "the 'cdr' statement requires 1 arg"
                   | Atom "quote" => if (length args = 1)
                                     then quote(hd args)
                                     else raise SyntaxError "the 'quote' statement requires 1 arg"
                   | Atom "eval" => if (length args = 1)
                                    then eval_(interpretSexp (hd args))
                                    else raise SyntaxError "the 'eval' statement requires 1 arg"
                   | Atom (pred as ("null?" | "atom?" | "int?" | "ratio?" | "real?" | "number?" | "bool?" | "symbol?" | "list?" | "string?")) =>
                       if (length args = 1)
                       then typeCheck (pred, interpretSexp (hd args))
                       else raise SyntaxError ("the '" ^ pred ^ "' statement requires 1 arg")
                   | Atom "export" => 
                       (case args of 
                            (Atom "*")::[] => exportAll
                          | _ => export (map interpretSexp args))
                   | Atom "import" =>
                       if length args = 2
                       then (case hd args of
                                 List (paths as _::_) =>
                                   import (map interpretSexp paths, interpretSexp (hd (tl args)))
                               | List [] =>
                                   raise SyntaxError "the 'import' statement requires at least one file path"
                               | Atom _ =>
                                   raise SyntaxError "first arg of an 'import' statement must be a list of file paths")
                       else raise SyntaxError "the 'import' statement requires 2 args: a list of file paths and a body expression"
                   | Atom "error" => if (length args = 1)
                                     then error_ (interpretSexp (hd args))
                                     else raise SyntaxError "the 'error' statement requires 1 arg"
                   | _ => foldl (fn (arg : s_exp, e : exp) => lambdaApp (e, (interpretSexp arg)))
                                (interpretSexp func)
                                args));


(*REGOLE DI INFERENZA*)
val MAX_DEPTH = 5000;

fun nextDepth (d : int) : int =
    if d >= MAX_DEPTH then
      raise RuntimeError ("maximum evaluation depth exceeded (" ^ Int.toString MAX_DEPTH ^ ")")
    else
      d + 1;

val initialEnv : environment =
    let
      val prims = [
          ("+",       closure (var "x", lambda (var "y", sum [var "x", var "y"]), emptyEnv)),
          ("-",       closure (var "x", lambda (var "y", sum [var "x", opposite (var "y")]), emptyEnv)),
          ("*",       closure (var "x", lambda (var "y", prod [var "x", var "y"]), emptyEnv)),
          ("/",       closure (var "x", lambda (var "y", prod [var "x", inverse (var "y")]), emptyEnv)),
          ("mod",     closure (var "x", lambda (var "y", modulus (var "x", var "y")), emptyEnv)),
          ("=",       closure (var "x", lambda (var "y", equals [var "x", var "y"]), emptyEnv)),
          ("<",       closure (var "x", lambda (var "y", lessThan [var "x", var "y"]), emptyEnv)),
          (">=",      closure (var "x", lambda (var "y", greatOrEq [var "x", var "y"]), emptyEnv)),
          ("<=",      closure (var "x", lambda (var "y", greatOrEq [var "y", var "x"]), emptyEnv)),
          (">",       closure (var "x", lambda (var "y", lessThan [var "y", var "x"]), emptyEnv)),
          ("not",     closure (var "x", not_ (var "x"), emptyEnv)),
          ("cons",    closure (var "x", lambda (var "y", cons (var "x", var "y")), emptyEnv)),
          ("car",     closure (var "x", car (var "x"), emptyEnv)),
          ("cdr",     closure (var "x", cdr (var "x"), emptyEnv)),
          ("concat",  closure (var "x", lambda (var "y", strConcat [var "x", var "y"]), emptyEnv)),
          ("explode", closure (var "x", strExplode (var "x"), emptyEnv)),
          ("null?",   closure (var "x", typeCheck ("null?", var "x"), emptyEnv)),
          ("atom?",   closure (var "x", typeCheck ("atom?", var "x"), emptyEnv)),
          ("int?",    closure (var "x", typeCheck ("int?", var "x"), emptyEnv)),
          ("ratio?",  closure (var "x", typeCheck ("ratio?", var "x"), emptyEnv)),
          ("real?",   closure (var "x", typeCheck ("real?", var "x"), emptyEnv)),
          ("number?", closure (var "x", typeCheck ("number?", var "x"), emptyEnv)),
          ("bool?",   closure (var "x", typeCheck ("bool?", var "x"), emptyEnv)),
          ("symbol?", closure (var "x", typeCheck ("symbol?", var "x"), emptyEnv)),
          ("list?",   closure (var "x", typeCheck ("list?", var "x"), emptyEnv)),
          ("string?", closure (var "x", typeCheck ("string?", var "x"), emptyEnv))
      ]
    in
      foldl (fn ((name, v), env) => extend (env, name, v))
            emptyEnv
            prims
    end;

fun extractVarName (var x, _) =
      if isPrim x
      then raise SyntaxError ("cannot shadow built-in primitive: " ^ x)
      else x
  | extractVarName (_, letType) = raise SyntaxError ("first arg in a '" ^ letType ^ " tuple' must be a variable");

fun eval(_, _, emptyList) = listVal []
  | eval(_, _, const k) = constVal k
  | eval(_, emptyEnv, var x) = raise SyntaxError("undeclared var :" ^ x)
  | eval(d, eagerextension(E, x, v), var y) =
      if (x = y)
      then v
      else eval(d, E, var y)
  | eval(d, env as lazyextension(E, bindings), var y) =
      let
        fun lookup [] = eval(d, E, var y)
          | lookup ((name, expr)::rest) =
              if name = y
              then eval(nextDepth d, env, expr)
              else lookup rest
      in
        lookup bindings
      end
  | eval(d, E, opposite M) =
      constVal (case extractNumber(eval(d, E, M)) of
                    integer n => integer (~n)
                  | ratio (n,m) => normalizeRatio ((~n), m)
                  | realNum r => realNum (~r)
                  | _ => raise InternalError "check eval opposite")
  | eval(d, E, inverse M) =
      constVal (case extractNumber(eval(d, E, M)) of
                    integer n => normalizeRatio(1, n)
                  | ratio (n,m) => normalizeRatio(m, n)
                  | realNum r =>
                      if Real.== (r, 0.0)
                      then raise SyntaxError "division by zero"
                      else realNum (1.0 / r)
                  | _ => raise InternalError "check eval inverse")
  | eval(d, E, sum args) = applyOperator (d, E, args, "+")
  | eval(d, E, prod args) = applyOperator (d, E, args, "*")
  | eval(d, E, modulus(M, N)) =
      constVal (integer ((extractInt(eval(d, E, M))) mod (extractInt(eval(d, E, N)))))
  | eval(d, E, strConcat args) = applyOperator (d, E, args, "^")
  | eval(d, E, strExplode M) =
      (case eval(d, E, M) of
           constVal (stringVal s) => (listVal (map (fn x => constVal(stringVal(str x))) (String.explode s)))
         | _ => raise SyntaxError "the 'explode' function requires a string value as arg")
  | eval(d, E, equals args) = applyOperator (d, E, args, "=")
  | eval(d, E, greatOrEq args) = applyOperator (d, E, args, ">=")
  | eval(d, E, lessThan args) = applyOperator (d, E, args, "<")
  | eval(d, E, and_ args) = applyOperator (d, E, args, "andalso")
  | eval(d, E, or args) = applyOperator (d, E, args, "orelse")
  | eval(d, E, not_ arg) = constVal (boolean (not (extractBool (eval (d, E, arg)))))
  | eval(d, E, ifThenElse(condition, M, N)) =
      if extractBool (eval (d, E, condition))
      then eval(d, E, M)
      else eval(d, E, N)
  | eval(d, E, let_(V, M, N)) = eval(d, extend(E, extractVarName(V, "let*"), eval(d, E, M)), N)
  | eval(d, E, multiLet(bindings, M)) =
      let
        val varNames = map (fn (x, _) => extractVarName(x, "let")) bindings
      in
        if (not (hasDuplicates varNames))
        then
          let
            fun addBindings (e, l) =
                case l of
                    [] => e
                  | (var x, N)::rest => addBindings(extend(e, x, eval(d, E, N)), rest)
                  | _ => raise SyntaxError "first arg in a 'let tuple' must be a variable"
          in
            eval(d, addBindings(E, bindings), M)
          end
        else raise SyntaxError "there cannot be duplicates variables in the 'let' statement, use 'let*' instead"
      end
  | eval(d, E, letRec(bindings, M)) =
      let
        val validBindings = map (fn (V, F) =>
                                   (case F of
                                        lambda _ => (extractVarName(V, "letrec"), F)
                                      | _ => raise SyntaxError "first arg in a 'letrec tuple' must be a lambda declaration"))
                                bindings
      in
        if (not (hasDuplicates (map (fn (x, _) => x) validBindings)))
        then eval(d, recExtend(E, validBindings), M)
        else raise SyntaxError "there cannot be duplicates variables in the 'letrec' statement, use 'let*' instead"
      end
  | eval(_, E, lambda(var x, M)) =
      if isPrim x 
      then raise SyntaxError ("cannot shadow built-in primitive: " ^ x)
      else closure(var x, M, E)
  | eval(_, _, lambda _) = raise SyntaxError "first element in a list must be a function or operator"
  | eval(d, E, lambdaApp(M, N)) =
      let val d' = nextDepth d in
        (case eval(d, E, M) of
             closure(var x, body, E') => eval(d', extend(E', x, eval(d, E, N)), body)
           | closure(_, _, _) => raise InternalError "illegal closure instance"
           | _ => raise SyntaxError "the first element of a list must be a function (it's possible too many args were given)")
      end
  | eval(d, E, cons(M, emptyList)) = listVal((eval(d, E, M)) :: [])
  | eval(d, E, cons(M, N)) =
      (case eval(d, E, N) of
           listVal l => listVal((eval(d, E, M)) :: l)
         | _ => raise SyntaxError "the second arg of a 'cons' statement should be a list value")
  | eval(d, E, car M) =
      (case eval(d, E, M) of
           listVal [] => raise SyntaxError "'car' used on an empty list"
         | listVal (h::_) => h
         | _ => raise SyntaxError "cannot use 'car' on an atomic value")
  | eval(d, E, cdr M) =
      (case eval(d, E, M) of
           listVal [] => raise SyntaxError "'cdr' used on an empty list"
         | listVal (_::r) => listVal r
         | _ => raise SyntaxError "cannot use 'cdr' on an atomic value")
  | eval(_, _, quote S) =
      let
        fun sExpToValue (List l) = listVal (map sExpToValue l)
          | sExpToValue (Atom s) =
            (case s of
                 "true" => constVal (boolean true)
               | "false" => constVal (boolean false)
               | _ => (case stringFromAtom s of
                           SOME str => constVal (stringVal str)
                         | NONE     => (case intFromString s of
                                            SOME n => constVal (integer n)
                                          | NONE   => (case ratioFromString s of
                                                           SOME (n, d) => constVal (normalizeRatio (n, d))
                                                         | NONE        => (case realFromString s of
                                                                               SOME r => constVal (realNum r)
                                                                             | NONE   => symbolVal s)))))
      in sExpToValue S
      end
  | eval(d, E, eval_ M) =
      let
        val d' = nextDepth d
        fun valueToSexp (constVal k) = Atom (constToString k)
          | valueToSexp (symbolVal s) = Atom s
          | valueToSexp (listVal l) = List (map valueToSexp l)
          | valueToSexp (closure _) = raise SyntaxError "cannot 'eval' a closure directly"
          | valueToSexp (envVal _) = raise SyntaxError "cannot 'eval' an import";
      in
        case eval(d, E, M) of
            listVal [] => raise SyntaxError "cannot 'eval' an empty list"
          | v => eval(d', E, interpretSexp (valueToSexp v))
      end
  | eval(d, E, typeCheck(pred, M)) =
      let
        val v = eval(d, E, M)
        val res =
            case (pred, v) of
                ("null?",   listVal [])              => true
              | ("atom?",   constVal _)              => true
              | ("atom?",   symbolVal _)             => true
              | ("atom?",   listVal [])              => true
              | ("int?",    constVal (integer _))    => true
              | ("ratio?",  constVal (ratio _))      => true
              | ("real?",   constVal (realNum _))    => true
              | ("number?", constVal (integer _))    => true
              | ("number?", constVal (ratio _))      => true
              | ("number?", constVal (realNum _))    => true
              | ("bool?",   constVal (boolean _))    => true
              | ("symbol?", symbolVal _)             => true
              | ("list?",   listVal _)               => true
              | ("string?", constVal (stringVal _))  => true
              | _                                    => false
      in
        constVal (boolean res)
      end
  | eval(d, E, import (args, M)) =
      let
        val d' = nextDepth d
        val fileNames = map (fn arg =>
                               case eval(d, E, arg) of
                                   constVal (stringVal x) => x
                                 | _ => raise SyntaxError "imported file paths must evaluate to strings") args
        val exportedValues =
            if not (hasDuplicates fileNames) then
              map (fn path =>
                     if String.isSuffix ".mylisp" path
                     then executeStrWithDepth d' (readFile path)
                     else raise SyntaxError ("expected a .mylisp extension for imported file: " ^ path))
                  fileNames
            else
              raise SyntaxError "cannot 'import' the same file twice"
        val finalEnv =
            foldl (fn (v, acc) =>
                     case v of
                         envVal E' => mergeEnv (acc, E')
                       | _ => raise SyntaxError "imported files must evaluate to an environment (using the 'export' function)")
                  E
                  exportedValues
      in
        eval (d, finalEnv, M)
      end
  | eval(d, E, export args) =
      let
        val varNames = map (fn (var x) => x
                             | _ => raise SyntaxError "arguments of 'export' must be variables") args
        fun exportedEnv [] = emptyEnv
          | exportedEnv (x::rest) =
              if isPrim x
              then raise SyntaxError ("cannot export built-in primitive: " ^ x)
              else eagerextension((exportedEnv rest), x, eval(d, E, var x))
      in
        if (not (hasDuplicates varNames))
        then envVal (exportedEnv varNames)
        else raise SyntaxError "cannot 'export' the same variable twice"
      end
   | eval(d, E, exportAll) =
      let
        fun collect (emptyEnv, _, acc) = acc
          | collect (eagerextension (rest, x, v), seen, acc) =
              if isPrim x
              then collect (rest, seen, acc)
              else if List.exists (fn s => s = x) seen
              then collect (rest, seen, acc)
              else collect (rest, x :: seen, eagerextension (acc, x, v))
          | collect (env as lazyextension (rest, bindings), seen, acc) =
              let
                val (seen', acc') =
                    foldl (fn ((x, _), (sAcc, eAcc)) =>
                             if List.exists (fn s => s = x) sAcc then (sAcc, eAcc)
                             else (x :: sAcc, eagerextension (eAcc, x, eval (d, env, var x))))
                          (seen, acc)
                          bindings
              in
                collect (rest, seen', acc')
              end
      in
        envVal (collect (E, [], emptyEnv))
      end
   | eval(d, E, error_ M) =
    (case eval(d, E, M) of
         constVal (stringVal msg) => raise RuntimeError msg
       | _ => raise SyntaxError "the 'error' function requires a string value as arg")

(*HELPER*)
and applyOperator (d : int, E : environment, args : exp list, operator : string) =
    case args of
        [] => raise InternalError "cannot have empty list of args in applyOperator"
      | _ =>
          case operator of
              "+" => constVal (foldl addNumber (integer 0) (map (fn x => extractNumber (eval(d, E, x))) args))
            | "*" => constVal (foldl prodNumber (integer 1) (map (fn x => extractNumber (eval(d, E, x))) args))
            | "^" => constVal (stringVal (foldr op^ "" (map (fn x => extractStr (eval (d, E, x))) args)))
            | "=" => constVal (boolean (allTrue (map (fn x => equalValues (eval(d, E, (hd args)), eval(d, E, x))) args)))
            | ">=" => let
                        fun ge (l : constant list) =
                            case l of
                                [] => raise InternalError "error in func ge"
                              | _::[] => [true]
                              | head::rest => geNumber (head, hd rest) :: ge rest
                      in
                        constVal (boolean (allTrue (ge (map (fn x => extractNumber (eval(d, E, x))) args))))
                      end
            | "<" => let
                       fun lt (l : constant list) =
                           case l of
                               [] => raise InternalError "error in func lt"
                             | _::[] => [true]
                             | head::rest => ltNumber (head, hd rest) :: lt rest
                     in
                       constVal (boolean (allTrue (lt (map (fn x => extractNumber (eval(d, E, x))) args))))
                     end
            | "andalso" => constVal (boolean (allTrue (map (fn x => extractBool (eval(d, E, x))) args)))
            | "orelse" => constVal (boolean (atLeastOneTrue (map (fn x => extractBool (eval(d, E, x))) args)))
            | _ => raise InternalError "operator not implemented"

(*FINAL EXECUTION*)
and executeStrWithDepth (d : int) (program : string) : value =
    eval(d, initialEnv, interpretSexp(parseSexp program))
    
fun executeStr (program : string) : value =
    executeStrWithDepth 0 program;

fun sExptoString (Atom s) = s
  | sExptoString (List l) = "(" ^ (String.concatWith " " (map sExptoString l)) ^ ")"

fun expToString emptyList = "()"
  | expToString (const k) = constToString k
  | expToString (var x) = x
  | expToString (opposite M) = "(- " ^ (expToString M) ^ ")"
  | expToString (inverse M) = "(/ " ^ (expToString M) ^ ")"
  | expToString (sum l) = "(+ " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (prod l) = "(* " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (modulus (M, N)) = "(mod " ^ (expToString M) ^ " " ^ (expToString N) ^ ")"
  | expToString (strConcat l) = "(concat " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (strExplode M) = "(explode " ^ (expToString M) ^ ")"
  | expToString (equals l) = "(= " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (greatOrEq l) = "(>= " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (lessThan l) = "(< " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (and_ l) = "(and " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (or l) = "(or " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString (not_ M) = "(not " ^ (expToString M) ^ ")"
  | expToString (ifThenElse (M, N, O)) = "(if " ^ (expToString M) ^ " " ^ (expToString N) ^ " " ^ (expToString O) ^ ")"
  | expToString (let_ (M, N, O)) = "(let* (" ^ (expToString M) ^ " " ^ (expToString N) ^ ") " ^ (expToString O) ^ ")"
  | expToString (multiLet (l, M)) = "(let (" ^ (String.concatWith " " (map (fn (x, y) => "(" ^ (expToString x) ^ " " ^ (expToString y) ^ ")") l)) ^ ") " ^ (expToString M) ^ ")"
  | expToString (letRec (l, M)) = "(letrec (" ^ (String.concatWith " " (map (fn (x, y) => "(" ^ (expToString x) ^ " " ^ (expToString y) ^ ")") l)) ^ ") " ^ (expToString M) ^ ")"
  | expToString (lambda (M, N)) = "(lambda (" ^ (expToString M) ^ ")" ^ (expToString N) ^ ")"
  | expToString (lambdaApp (M, N)) = "(" ^ (expToString M) ^ " " ^ (expToString N) ^ ")"
  | expToString (cons (M, N)) = "(cons " ^ (expToString M) ^ " " ^ (expToString N) ^ ")"
  | expToString (car M) = "(car " ^ (expToString M) ^ ")"
  | expToString (cdr M) = "(cdr " ^ (expToString M) ^ ")" 
  | expToString (quote S) = "(quote " ^ (sExptoString S) ^ ")"
  | expToString (eval_ M) = "(eval " ^ (expToString M) ^ ")"
  | expToString (typeCheck (pred, M)) = "(" ^ pred ^ " " ^ (expToString M) ^ ")"
  | expToString (import (l, M)) = "(import (" ^ (String.concatWith " " (map expToString l)) ^ ") " ^ (expToString M) ^ ")"
  | expToString (export l) = "(export " ^ (String.concatWith " " (map expToString l)) ^ ")"
  | expToString exportAll = "(export *)"
  | expToString (error_ M) = "(error " ^ (expToString M) ^ ")" 

fun envToString emptyEnv = ""
  | envToString (eagerextension(E, s, v)) =
      if isPrim s
      then envToString E
      else envToString E ^ "(" ^ s ^ " : " ^ (#2 (valueToString v)) ^ ")"
  | envToString (lazyextension(E, bindings)) = envToString E ^ foldl (fn (x, acc) => x ^ " " ^ acc) "" (map (fn (s, M) => "(" ^ s ^ ":" ^ (expToString M) ^ ")") bindings)
and valueToString (constVal k) = ("constant : ", constToString k)
  | valueToString (listVal l) = ("list : ", "(" ^ (String.concatWith " " (map (fn v => #2 (valueToString v)) l)) ^ ")")
  | valueToString (closure (var x, body, E)) = ("closure :", "[" ^ x ^ ", " ^ (expToString body) ^ ", {" ^ (envToString E) ^ "}]")
  | valueToString (closure(_, _, _)) = raise InternalError "error in the closure"
  | valueToString (symbolVal s) = ("symbol :", "'" ^ s)
  | valueToString (envVal E) = ("environment : ", "{" ^ (envToString E) ^ "}")

fun executeFile (path : string) =
    if String.isSuffix ".mylisp" path then
      (print ("\027[32mOUTPUT " ^ path ^ " = " ^ op ^ (valueToString (executeStr (readFile path))) ^ "\027[0m\n")
       handle SyntaxError m   => print ("\027[31mSyntaxError: " ^ m ^ "\027[0m\n")
            | RuntimeError m  => print ("\027[31mRuntimeError: " ^ m ^ "\027[0m\n")
            | InternalError m => print ("\027[31mInternalError: " ^ m ^ "\027[0m\n")
            | exn => raise exn)
    else
      print "\027[31mFileError: expected a .mylisp extension\027[0m\n";

(*---FINAL TEST---*)
executeFile "test.mylisp";