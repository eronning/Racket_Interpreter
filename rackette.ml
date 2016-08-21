#use "/course/cs017/src/rackette/read.ml" ;;
#use "/course/cs017/src/ocaml/CS17setup.ml";; 


(* Data definition for Binding:
 * A binding is a tuple of an identifier and a value: abstract_syntax * value_syntax
 * Example : a binding can be (Identifier("x"), Number(5))
 *
 * Data definition for enviroment:
 * An enviroment is a list of bindings : (abstract_syntax * value_syntax) list
 * Example : a enviroment can be [(Identifier("x"), Number(5)) ; (Identifier("y"), Number(+)] *)

type abstract_syntax =
    | Remainder 
    | Equals (* = *)
    | And
    | Or
    | Add
    | Subtract
    | Divide
    | Multiply
    | Num of int
    | Bool of bool
    | Identifier of string 
    | Lambda of abstract_syntax * abstract_syntax
    | Let of (abstract_syntax * abstract_syntax) * abstract_syntax
    | If of abstract_syntax * abstract_syntax * abstract_syntax
    | PrimProc of abstract_syntax * abstract_syntax * abstract_syntax
    | AnonProc of abstract_syntax * abstract_syntax

type value_syntax =
    | Primitive of string
    | Number of int 
    | Boolean of bool
    | Closure of abstract_syntax * (abstract_syntax * value_syntax) list ;;


(*
* I/P: The procedure takes in quoted syntax: q
* O/P: The procedure turns the quoted syntax into abstract_syntax *)
let rec parse (q: quoted_syntax) : abstract_syntax =
  match q with
    | Symbol "remainder"                              -> Remainder
    | Symbol "="                                      -> Equals
    | Symbol "and"                                    -> And
    | Symbol "or"                                     -> Or
    | Symbol "+"                                      -> Add
    | Symbol "-"                                      -> Subtract
    | Symbol "*"                                      -> Multiply
    | Symbol "/"                                      -> Divide
    | Number number                                   -> Num(number)
    | Symbol "true"                                   -> Bool(true)
    | Symbol "false"                                  -> Bool(false)
    | List[(Symbol "lambda") ; List[v1] ; v2]         -> Lambda(parse v1, parse v2)
    | List[(Symbol "let") ; List[List[v1 ; v2]] ; v3] -> Let((parse v1, parse v2), parse v3)
    | List[(Symbol "if") ; v1 ; v2 ; v3]              -> If(parse v1, parse v2, parse v3)
    | List[v1 ; v2 ; v3]                              -> PrimProc(parse v1, parse v2, parse v3)
    | List[v1 ; v2]                                   -> AnonProc(parse v1, parse v2)
    | Symbol value                                    -> Identifier(value) 
    | _                                               -> failwith "Invalid quoted syntax was inputted" ;;

check_expect (parse (read "remainder")) 
  Remainder ;;

check_expect (parse (read "=")) 
  Equals ;;

check_expect (parse (read "and")) 
  And ;;

check_expect (parse (read "or")) 
  Or ;;

check_expect (parse (read "+")) 
  Add ;;

check_expect (parse (read "-")) 
  Subtract ;;

check_expect (parse (read "/")) 
  Divide ;;

check_expect (parse (read "*")) 
  Multiply ;;

check_expect (parse (read "17")) 
  (Num(17)) ;;

check_expect (parse (read "true")) 
  (Bool(true)) ;;

check_expect (parse (read "false")) 
  (Bool(false)) ;;

check_expect (parse (read "(lambda (x) (+ x 15))"))  
  (Lambda(Identifier("x"), PrimProc(Add, Identifier("x"), Num(15)))) ;;

check_expect (parse (read "(let ((x 15)) (+ x 15))")) 
  (Let((Identifier("x"), Num(15)), PrimProc(Add, Identifier("x"), Num(15)))) ;;

check_expect (parse (read "(if (= x 15) true false)"))
  (If(PrimProc(Equals, Identifier("x"), Num(15)), Bool(true), Bool(false))) ;;

check_expect (parse (read "(= 15 x)"))
  (PrimProc(Equals, Num 15, Identifier("x"))) ;;

check_expect (parse (read "((lambda (x) (+ x 15)) 5)"))
  (AnonProc(Lambda(Identifier("x"), PrimProc(Add, Identifier("x"), Num(15))), Num(5))) ;;

check_expect (parse (read "((lambda (x) x) 5)")) 
  (AnonProc(Lambda(Identifier("x"), Identifier("x")), Num(5)));;

check_expect (parse (read "x"))
  (Identifier("x")) ;;

(*
* I/P: the procedure takes in a binding and a enviroment : (id1, value1) e
* O/P: the procedure updates the enviroment with the inputted binding *)
let rec update_env ((id1, value1) : abstract_syntax * value_syntax) (e : (abstract_syntax * value_syntax) list) : (abstract_syntax * value_syntax) list =
  match e with
    | []                 -> (id1, value1) :: []
    | (id2, value2) ::tl -> 
        if   (id1 = id2) 
        then (id1, value1) :: tl
        else (id2, value2) :: (update_env (id1, value1) tl) ;;

check_expect (update_env (Identifier("x"), Number(15)) [(Identifier("x"), Number(20)) ; (Identifier("y"), Number(10)) ; (Identifier("z"), Number(2))])
  [(Identifier("x"), Number(15)) ; (Identifier("y"), Number(10)) ; (Identifier("z"), Number(2))] ;;

check_expect (update_env (Identifier("x"), Number(15)) [(Identifier("y"), Number(10)) ; (Identifier("z"), Number(2))])
  [(Identifier("y"), Number(10)) ; (Identifier("z"), Number(2)) ; (Identifier("x"), Number(15))];;

(*
* I/P: the procedure takes in an identifier and a enviroment : identifier e
* O/P: the procedure finds the value bound to the inputted identifier in the enviroment *)
let rec find_identifier (identifier : abstract_syntax) (e : (abstract_syntax * value_syntax) list) : value_syntax = 
  match e with
    | []              -> failwith "The value is not defined"
    | (id, value)::tl ->
        if   (identifier = id)
        then (value)
        else (find_identifier identifier tl) ;;

check_expect(find_identifier (Identifier("x")) [(Identifier("x"), Number(20)) ; (Identifier("y"), Number(10)) ; (Identifier("z"), Number(2))]) 
  (Number(20)) ;;

check_error (fun x -> (find_identifier (Identifier("g")) [(Identifier("x"), Number(20)) ; (Identifier("y"), Number(10)) ; (Identifier("z"), Number(2))])) 
  ("The value is not defined") ;;

(* 
* I/P: the procedure takes in abstract_syntax : a
* O/P: the procedure converts the abstract_syntax into value_syntax assuming an empty enviroment *)
let eval (a : abstract_syntax) : value_syntax = 
(*
* I/P: the procedure takes in abstract_syntax and an enviroment : a e
* O/P: the procedure converts the abstract_syntax into value_syntax using the enviroment  *)
  let rec eval_helper (a : abstract_syntax) (e : (abstract_syntax * value_syntax) list) : value_syntax =
    match a with
      | Remainder                         -> Primitive("remainder")
      | Equals                            -> Primitive("=")
      | And                               -> Primitive("and")
      | Or                                -> Primitive("or")
      | Add                               -> Primitive("+")
      | Subtract                          -> Primitive("-")
      | Multiply                          -> Primitive("*")
      | Divide                            -> Primitive("/")
      | Num(number)                       -> Number(number)
      | Bool(value)                       -> Boolean(value)
      | Lambda(Identifier(id), body)      -> Closure(Lambda(Identifier(id), body), e)
      | Let((Identifier(id), expr), body) -> 
          (let value = (eval_helper expr e) in
             (eval_helper body (update_env (Identifier(id), value) e)))
      | If(pred, expr1, expr2)            ->
          (let pred_val = (eval_helper pred e) in
             (if      (pred_val = Boolean(true))
              then    (eval_helper expr1 e)
              else if (pred_val = Boolean(false)) 
              then    (eval_helper expr2 e)
              else     failwith "The predicate didn't evaluate to a boolean"))
      | PrimProc(proc, arg1, arg2)        ->
          (let proc_val = (eval_helper proc e) and
            arg1_val = (eval_helper arg1 e) and
            arg2_val = (eval_helper arg2 e) in
             (match proc_val, arg1_val, arg2_val with
               | Primitive("remainder"), Number(num1), Number(num2) -> Number(num1 mod num2)
               | Primitive("="), Number(num1), Number(num2)         -> Boolean(num1 = num2)
               | Primitive("and"), Boolean(bool1), Boolean(bool2)   -> Boolean(bool1 && bool2)
               | Primitive("or"), Boolean(bool1), Boolean(bool2)    -> Boolean(bool1 || bool2)
               | Primitive("+"), Number(num1), Number(num2)         -> Number(num1 + num2)
               | Primitive("-"), Number(num1), Number(num2)         -> Number(num1 - num2)
               | Primitive("*"), Number(num1), Number(num2)         -> Number(num1 * num2) 
               | Primitive("/"), Number(num1), Number(num2)         -> Number(num1 / num2)
               | Primitive(_), Number(num1), Number(num2)           -> failwith "And and Or must be applied to boolean expressions"
               | Primitive(_), Boolean(num1), Boolean(num2)         -> failwith "Remainder, =, +, -, *, and / must be applied to numbers." 
               | _                                                  -> failwith "An invalid primitive was inputted"))
      | AnonProc(proc, arg)              ->
          (let proc_val = (eval_helper proc e) and
            arg_val = (eval_helper arg e)
           in 
             (match proc_val with
               | Closure(Lambda(id, body), e2) -> (eval_helper body (update_env (id, arg_val) e2))
               | _                             -> failwith "anonymous procedure application"))
      | Identifier(value)                -> (find_identifier (Identifier(value)) e)
      | _                                -> failwith "An invalid expression was inputted" in
    (eval_helper a []) ;;


check_expect (eval (parse (read "remainder"))) 
  (Primitive("remainder"));;

check_expect (eval (parse (read "="))) 
  (Primitive("="));;

check_expect (eval (parse (read "and"))) 
  (Primitive("and"));;

check_expect (eval (parse (read "or"))) 
  (Primitive("or"));;

check_expect (eval (parse (read "+"))) 
  (Primitive("+"));;

check_expect (eval (parse (read "-"))) 
  (Primitive("-"));;

check_expect (eval (parse (read "/"))) 
  (Primitive("/"));;

check_expect (eval (parse (read "*"))) 
  (Primitive("*"));;

check_expect (eval (parse (read "17"))) 
  (Number(17)) ;;

check_expect (eval (parse (read "true"))) 
  (Boolean(true));;

check_expect (eval (parse (read "false"))) 
  (Boolean(false));;

check_expect (eval (parse (read "(lambda (x) (+ x 15))"))) 
  (Closure(Lambda(Identifier("x"), PrimProc(Add, Identifier("x"), Num(15))), []));;

check_expect (eval (parse (read "(let ((x 15)) (+ x 15))"))) 
  (Number(30)) ;;

check_expect (eval (parse (read "(if (= 15 15) true false)"))) 
  (Boolean(true)) ;;

check_expect (eval (parse (read "(if (= 17 15) true false)"))) 
  (Boolean(false)) ;;

check_expect (eval (parse (read "((if (= 5 3) + *) 2 4)")))
  (Number(8)) ;; 

check_expect (eval (parse (read "((if (= 5 5) + *) 2 3)")))
  (Number(5)) ;; 

check_expect (eval (parse (read "(= 15 18)")))
  (Boolean(false)) ;;

check_expect (eval (parse (read "((lambda (x) x) 5)")))
  (Number(5)) ;; 

check_expect (eval (parse (read "((lambda (x) (+ x 15)) 5)")))
  (Number(20)) ;;

check_expect (eval (parse (read "(let ((x 1)) ((let ((x 17)) (lambda (y) (+ x y))) x ))")))
  (Number(18)) ;;

check_expect (eval (parse (read " (let ((a 100)) (let ((b 2)) (let ((f (lambda (x ) (let ((b a)) (+ a (+ b x )))))) (f 1))))")))
  (Number(202)) ;;

check_expect (eval (parse (read "(let ((a 0)) (let ((f (lambda (x ) (+ x a)))) (let ((a 1)) (let ((a 2)) (f 0)))))")))
  (Number(0)) ;;

check_error (fun x -> (eval (parse (read "(lambda (5) (+ 5 1))"))))
  ("An invalid expression was inputted") ;;

check_error (fun x -> (eval (parse (read "(let ((5 3)) (+ 5 3))"))))
  ("An invalid expression was inputted") ;;

check_expect (eval (parse (read "(let ((x +)) ((let ((x 4)) (lambda (y) (y x x))) x ))")))
  (Number(8)) ;;

check_expect (eval (parse (read "(let ((x 2)) ((let ((x 4)) (lambda (y) (/ x y))) x ))")))
  (Number(2)) ;;

check_expect (eval (parse (read "(let ((x 1)) (let ((x 17)) ((lambda (y) (+ x y)) x )))")))
  (Number(34)) ;;

check_expect (eval (parse (read "(let ((x 1)) (let ((x 17)) ((lambda (y) (/ x y)) x )))")))
  (Number(1)) ;;

check_error (fun x -> (eval (parse (read "x")))) ("The value is not defined") ;;

(*
* I/P: the procedure takes in value_syntax : v
* O/P: the procedure outputs a string that represents the value of the value_syntax *)
let print (v: value_syntax) : string =
  match v with
    | Primitive(value) -> value
    | Number(number)   -> string_of_int number
    | Boolean(value)   -> string_of_bool value
    | Closure(_)       -> "(lambda (a1) ...)" ;;

check_expect (print (eval (parse (read "remainder")))) 
  ("remainder") ;; 

check_expect (print (eval (parse (read "17")))) 
  ("17") ;;

check_expect (print (eval (parse (read "true")))) 
  ("true") ;;

check_expect (print (eval (parse (read "(lambda (x) (+ x 15))")))) 
  ("(lambda (a1) ...)") ;;

