namespace ParseCombinators

open System.IO
open System.Text
open System


(* Parser combinators *)

(* A parse state is two lists, stuff we have parsed and stuff yet to parse.  These are not neccesarily of the same
   type but they are in this example.  
   Generally the parsed stuff would be a discriminated union that would include the input type as well as other
   types to represent entire productions.                                                                          *)

type 'a PState  = 'a list * 'a list

(* A Parse is a set of valid interpretations of the input so far *)
type 'a Parse = 'a PState list

(* A parser takes a parse to a new, more complete, parse *)
type 'a Parser = 'a Parse -> 'a Parse

module ParseCombinators =

    let rec 
        empty : 'a PState = ([],[])

    and longest : 'a Parse -> 'a PState = fun p -> 
        List.fold (fun (p', r') (p, r) -> if List.length p > List.length p' 
                                          then (p, r) 
                                          else (p', r')) 
                  empty p 

    and shortest : 'a Parse -> 'a PState = fun p -> 
       List.fold (fun (p', r') (p, r) -> if List.length p < List.length p' || (p' = []) 
                                         then (p, r) 
                                         else (p', r'))
                 empty p 
    
    (* return a fresh resume point for the longest current parse together with its string representation *)
    and getParsed : char Parse -> char Parse * string = fun p ->
        let state = longest p
        ([[], snd state], new string(state |> fst |> List.toArray))

    (* Character parsers **************************************************************************************)
    
    (* Most of the parsers accept additional initial arguments and therefore do not have the Parser signature
       shown above.  When these (curried) configuration inputs are supplied then the correct signature
       remains and the parser can be plugged into a chain.
       To ensure that this works properly it is necessary to delimit the configured parser with parenthesis,
       use an operator, or to create the parser separately and assign it to a variable.  The operators will
       still require parenthesis on occasion.
       
       E.g. Neither pChar nor the !! operator are parsers; however both (pChar 'z') and !!'z' are parsers with
       the correct signature.  The parentheses are required for the function form but the high precedence of
       the operator form should make them unnecessary.  Another option is to use a temporary: 
          let zparse = pChar 'z'                                         
                                                                                                              *)     
    
    (* call the designated output function with the current longest parse and id
       clear all other current states and forget the current parse output          *)
    and pSuccess = fun (f: string -> string -> unit) (id: string) (p : char Parse) ->
        let state = longest p
        new string(state |> fst |> List.toArray) |> f id 
        [[], snd state] 
     
    (* return an empty parse state *)   
    and pFail = fun (p : 'a Parse) ->
        []
     
    (* reject all but the shortest match *)
    and pMin = fun (p : 'a Parse) ->
        [ shortest p ] 
        
    (* reject all but the longest match *)     
    and pMax = fun (p : 'a Parse) ->
        [ longest p ] 
    
    (* forget all parsed characters  but keep the parse points *) 
    and pForget = fun (p : 'a Parse) ->
        List.map (fun (_, rest) -> ([], rest)) p
        
    (* parse any specific character *)   
    and pChar = fun (ch : char) (p : char Parse) ->
        p |>
        List.choose (fun (out, next) -> 
                       match next with
                       | c :: rest when c = ch -> Some (out @ [c], rest)
                       | _                     -> None )
                 
    (* parse any character *)   
    and pAny = fun (p : char Parse) ->
        p |>
        List.choose (fun (out, next) -> 
                       match next with
                       | c :: rest -> Some (out @ [c], rest)
                       | _         -> None )
    
    (* parse one character from of a contiguous range *) 
    and pRange = fun (s: char, e: char) (p : char Parse) ->
        p |>
        List.choose (fun (out, next) -> 
                       match next with
                       | c :: rest when c >= s && c <= e -> Some (out @ [c], rest)
                       | _                               -> None )
    
    (* parse one member of a set given as a string *)
    and pMember = fun (s: string) (p : char Parse) ->
        p |>
        List.choose (fun (out, next) -> 
                       match next with
                       | c :: rest when s.IndexOf(c) >= 0 -> Some (out @ [c], rest)
                       | _                                -> None )

    (* parse a literal string *)
    and pString = fun (s: string) (p : char Parse) ->
        if(s = "") || (p = [])
        then p
        else p |> List.choose (fun (out, next) -> 
                                 match next with
                                 | c :: rest when s.[0] = c -> Some (out @ [c], rest)
                                 | _                        -> None )
               |> pString (s.Substring(1))                              

    (* parse any character matching the predicate *)
    and pIf = fun (pred : char -> bool) (p : char Parse) ->
        p |>
        List.choose (fun (out, next) -> 
                       match next with
                       | c :: rest when pred c -> Some (out @ [c], rest)
                       | _                     -> None )

    (* useful predicates for pIf *)
    and isLetter : char -> bool = fun c -> Char.IsLetter(c)                
    and isControl : char -> bool = fun c -> Char.IsControl(c)                
    and isDigit : char -> bool = fun c -> Char.IsDigit(c)                
    and isLetterOrDigit : char -> bool = fun c -> Char.IsLetterOrDigit(c)                
    and isLower : char -> bool = fun c -> Char.IsLower(c)                
    and isUpper : char -> bool = fun c -> Char.IsUpper(c)                     
    and IsPunctuation : char -> bool = fun c -> Char.IsPunctuation(c)
    and isSeparator : char -> bool = fun c -> Char.IsSeparator(c)       
    and isSymbol : char -> bool = fun c -> Char.IsSymbol(c)       
    and isWhiteSpace : char -> bool = fun c -> Char.IsWhiteSpace(c)
        
    (* Combinators *******************************************************************************************)
    
    (* alternative combinator *)
    and pAlt = fun (pa : 'a Parser) (pb : 'a Parser) (p : 'a Parse) ->
        pa p @ pb p

    (* either-or combinator *)
    and pOr = fun (pa : 'a Parser) (pb : 'a Parser) (p : 'a Parse) ->
        let ra = pa p 
        if ra = []
        then  pb p
        else ra
     
    (* if fail else combinator *)
    (* first continues in pc - the condition parser
       if pc completes then continue with pe
       otherwise continue in pf with the original parse state
       This allows a parse that is a prefix of another parse to be handled efficiently
       E.g. an integer is a prefix of a float if we fail to parse the decimal point then
       its an integer - So we restore that prior state and suceed                        *)
    and pIfFailElse = fun (pc: 'a Parser) (pf : 'a Parser) (pe : 'a Parser) (p : 'a Parse) -> 
        let px = pc p
        if px = []
        then pf p
        else pe px
          
    (* sequential combinator *)
    and pSeq = fun (pa : 'a Parser) (pb : 'a Parser) (p : 'a Parse) ->
        let ra = p |> pa 
        if ra = [] 
        then [] 
        else ra |> pb

        
    (* repeat combinator *)
    and pRpt = fun (n, m) (pa : 'a Parser) (p : 'a Parse) ->
        if (m < 1) || (p = [])
        then []
        else
          let res = p |> pa
          let rpt = pRpt (n - 1, m - 1) pa res 
          if n = 0 
          then p @ res @ rpt
          else if n > 0 
               then rpt
               else rpt @ res  
    
    (* zero or one repeats *)
    and pOpt = pRpt (0, 1)

    (* at least one repeat *)
    and pSome = pRpt (1, (System.Int32.MaxValue))
    
    (* unlimited repeats; just like telly! *)
    and pStar = pRpt (0, (System.Int32.MaxValue))
    
    (* Some handy operators  why not! *)
    and ( &&& ) = fun pa pb -> pSeq pa pb
    and ( <+> ) = fun pa pb -> pAlt pa pb
    and ( <|> ) = fun pa pb -> pOr pa pb
    and ( !* )  = fun pa -> pStar pa
    and ( !+ )  = fun pa -> pSome pa
    and ( !? )  = fun pa -> pOpt pa
    and ( *<= ) = fun pa n -> pRpt (1, n) pa
    and ( *= )  = fun pa n -> pRpt (n, n) pa
    and ( !! )  = fun c -> pChar c
    and ( !% )  = fun s -> pString s
    and ( !~ )  = fun s -> pMember s
    and ( !- )  = fun r -> pRange r
    and ( ~~ )  = fun f -> pIf f

(* Utilities for testing *)    
module Utils =
        (* string to char list *)
    let rec
        chars : string -> char list = fun s -> 
        [for c in s -> c]

        (* Set up a parse state *)
    and s_state : string -> char PState = fun s -> 
        let s2 = Array.map chars (s.Split([|'|'|], 2))
        s2.[0], s2.[1] 
    
        (* Convert a string to a parser input state *)
    and str : string -> char Parse = fun s ->
        [[], chars s]
         
        (* Print a parse state with a diamond cursor *)   
    and print_state = fun ((parse, next) : char PState) ->
        Console.WriteLine ()
        for ch in parse do Console.Write ch done
        Console.Write "\u2666";
        for ch in next do Console.Write ch done

        (* Dump all parse states *)
    and print_parse = fun (parse : char Parse) ->
        match parse with
        | []             -> ()
        | state :: rest  -> print_state state;
                            print_parse rest

(* Tests *)
module Test =

   open ParseCombinators
   open Utils

   let presult = [ s_state "abc|def"; s_state "abcd|ef"; s_state "ab|cdef" ]
    
   presult |> print_parse 
   Console.WriteLine ()
   presult |> longest |> print_state 
   Console.WriteLine ()
   presult |> shortest |> print_state 
   
   presult |> !!'e' |> print_parse 
   presult |> ~~isLetter |> print_parse 
   
   let testin = [ s_state "|aaaaaaaaax" ]
   let pAs = pRpt (4, 6) !! 'a'  
   pAs testin |> print_parse
   
   [ s_state "|Hello World" ] |> !% "Hello" |> longest |> print_state
   [ s_state "|abcdXYZ" ] |> !* ~~isLower |> longest |> print_state

   let rec
       accept = fun id text -> 
           Console.WriteLine ()
           Console.Write (String.Concat(id, " = ", text))
    
   (* Build some parsers for the parts of numbers *)        
   and space   = !* ~~isWhiteSpace &&& pForget
   and sign    = !? (!!'+' <+> !!'-')
   and digit   = ~~isDigit 
   and exp     = !!'E' <+> !!'e' &&& sign &&& digit *<= 2
   and dec     = !+ digit &&& !!'.' &&& !* digit
   (* Assemble into a complete parsers for floats *) 
   and flt     = space &&& sign &&& dec &&& !? exp
    
   (* A combined numeric parser using pIfFailElse                 *)
   and prefix = space &&& sign &&& !+ digit
   and number  = prefix &&&                                                  (* Common prefix *)
                     (!!'.' |> pIfFailElse)                                  (* Condition     *)
                         (pSuccess accept "Integer")                         (* Fail parser   *)
                         (!* digit &&& !? exp &&& (pSuccess accept "Float")) (* Continuation  *)
                            
   (* floats and integers are mutually exclusive so the use of an
       or combinator ensures that floats take priority            *)
   
   "2345215463"     |> str |> !* digit  |> longest |> print_state
   "-2345215463"    |> str |> (sign &&& !* digit) |> longest |> print_state
   "2345215463"     |> str |> (sign &&& !* digit) |> longest |> print_state
   "+2345215463"    |> str |> (sign &&& !* digit) |> longest |> print_state
   "e+55"           |> str |> exp |> longest |> print_state
   "E2"             |> str |> exp |> longest |> print_state
   
   "1234567"        |> str |> dec |> longest |> print_state
   "123.4567"       |> str |> dec |> longest |> print_state
   "-1234.567"      |> str |> flt |> longest |> print_state
   "+12.34567"      |> str |> flt |> longest |> print_state
   "12.34567e12"    |> str |> flt |> longest |> print_state
   "12.34567e+12"   |> str |> flt |> longest |> print_state
   "-12.34567e-12"  |> str |> flt |> longest |> print_state
   
   "-12.34567e-12 678"  |> str |> (number &&& number) |> ignore
     
   Console.ReadLine () |> ignore

