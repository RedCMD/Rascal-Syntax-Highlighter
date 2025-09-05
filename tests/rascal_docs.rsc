
int fac(int n) {
  if (n == 0)
    return 1;
  else
    return n * f(n - 1);
 }



int f(int n) = n == 0 ? 1 : n * f(n - 1);



int f(0) = 1;
default int f(int n) = n * f(n - 1);



data Bool
  = t()
  | f()
  | and(Bool l, Bool r)
  |   or(Bool l, Bool r)
  ;

Bool and(f(), Bool _) = f();
Bool and(t(), Bool b) = b;



and(t(),t())
Bool: t();
and(f(),t())
Bool: f();
and(or(t(),t()),t())
Bool: and(or(t(),t()),t())



data Bool = maybe();



Bool and(maybe(), maybe()) = maybe();
Bool and(maybe(), true()) = maybe();
Bool and(maybe(), false()) = false();



list[value] dup([*value a, value e, *value b, e, *value c]) = dup([*a, e, *b, *c]);
// TODO:
// list[value] dup([*value a, value e, *value b, e, *value c]) = dup([*a, e, *b, *c])
default list[value] dup(list[value] l) = l;



list[&T] dup([*&T a, &T e, *&T b, e, *&T c]) = dup([*a, e, *b, *c]);

default list[&T] dup(list[&T] l) = l; 



data Bool
  = t()
  | f()
  | and(Bool l, Bool r)
  | or(Bool l, Bool r)
  ;
  
Bool eval(and(f(), Bool _)) = f();
Bool eval(and(t(), Bool b)) = b;



eval(and(f(),t()))
Bool: f()



visit (and(and(f(),t()),t())) { case Bool b => eval(b) }
// TODO:
// visit (and(and(f(),t()),t())) { case Bool b => eval(b); }
Bool: f();



Bool eval(and(t(), Bool b)) = eval(b);



module Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Machine = machine: State+ states;

syntax State = @Foldable state: "state" Id name Trans* out;
syntax Trans = trans: Id event ":" Id to;



module Analyze

import Syntax;

set[Id] unreachable(Machine m) {
  r = { <q1,q2> | (State)`state <Id q1> <Trans* ts>` <- m.states, 
				  (Trans)`<Id _>: <Id q2>` <- ts }+;
  qs = [ q.name | q &- m.states ];
  return { q | q <- qs, q notin r[qs[0]] };
}



module Compile

import Syntax;

str compile(Machine m) =
  "while (true) {
  '  event = input.next();
  '  switch (current) { 
  '    <for (q <- m.states) {>
  '    case \"<q.name>\":
  '      <for (t <- q.out) {>
  '      if (event.equals(\"<t.event>\"))
  '        current = \"<t.to>\";
  '      <}>
  '      break;
  '    <}>
  '  }
  '}"; 



list[int] even0(int max) {
  list[int] result = [];
  for (int i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}



list[int] even1(int max) {
  result = [];
  for (i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}



list[int] even2(int max) {
  result = [];
  for (i <- [0..max], i % 2 == 0)
    result += i;
  return result;
}



list[int] even3(int max) {
  result = for (i <- [0..max], i % 2 == 0)
    append i;
  return result;
}



list[int] even4(int max) {
  return for (i <- [0..max], i % 2 == 0)
           append i;
}



list[int] even5(int max) {
  return [ i | i <- [0..max], i % 2 == 0];
}



list[int] even6(int max) = [i | i <- [0..max], i % 2 == 0];



set[int] even7(int max) = {i | i <- [0..max], i % 2 == 0};



int fac(int n) {
  if (n == 0)
    return 1;
  else
    return n * f(n - 1);
 }



int f(int n) = n == 0 ? 1 : n * f(n - 1);



int f(0) = 1;
default int f(int n) = n * f(n - 1);



data Bool
  = t()
  | f()
  | and(Bool l, Bool r)
  |   or(Bool l, Bool r)
  ;
  
Bool and(f(), Bool _) = f();
Bool and(t(), Bool b) = b;



and(t(),t())
Bool: t();
and(f(),t())
Bool: f();
and(or(t(),t()),t())
Bool: and(or(t(),t()),t())



data Bool = maybe();


// TODO:
// Bool and(maybe(), maybe()) = maybe()
// Bool and(maybe(), true()) = maybe()
// Bool and(maybe(), false()) = false()
Bool and(maybe(), maybe()) = maybe();
Bool and(maybe(), true()) = maybe();
Bool and(maybe(), false()) = false();



list[value] dup([*value a, value e, *value b, e, *value c]) = dup([*a, e, *b, *c]);
// TODO:
// list[value] dup([*value a, value e, *value b, e, *value c]) = dup([*a, e, *b, *c])
default list[value] dup(list[value] l) = l;



list[&T] dup([*&T a, &T e, *&T b, e, *&T c]) = dup([*a, e, *b, *c]);
default list[&T] dup(list[&T] l) = l;
// TODO:
// list[&T] dup([*&T a, &T e, *&T b, e, *&T c]) = dup([*a, e, *b, *c])
// default list[&T] dup(list[&T] l) = l



data Bool
  = t()
  | f()
  | and(Bool l, Bool r)
  | or(Bool l, Bool r)
  ;
  
Bool eval(and(f(), Bool _)) = f();
Bool eval(and(t(), Bool b)) = b;



eval(and(f(),t()))
Bool: f()



visit (and(and(f(),t()),t())) { case Bool b => eval(b) }
// TODO:
// visit (and(and(f(),t()),t())) { case Bool b => eval(b); }
Bool: f();



Bool eval(and(t(), Bool b)) = eval(b);



module Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Machine = machine: State+ states;
syntax State = @Foldable state: "state" Id name Trans* out;
syntax Trans = trans: Id event ":" Id to;



module Analyze

import Syntax;

set[Id] unreachable(Machine m) {
  r = { <q1,q2> | (State)`state <Id q1> <Trans* ts>` <- m.states, 
				  (Trans)`<Id _>: <Id q2>` <- ts }+;
  qs = [ q.name | q &- m.states ];
  return { q | q <- qs, q notin r[qs[0]] };
}



module Compile

import Syntax;

str compile(Machine m) =
  "while (true) {
  '  event = input.next();
  '  switch (current) { 
  '    <for (q <- m.states) {>
  '    case \"<q.name>\":
  '      <for (t <- q.out) {>
  '      if (event.equals(\"<t.event>\"))
  '        current = \"<t.to>\";
  '      <}>
  '      break;
  '    <}>
  '  }
  '}"; 



list[int] even0(int max) {
  list[int] result = [];
  for (int i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}



list[int] even1(int max) {
  result = [];
  for (i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}



list[int] even2(int max) {
  result = [];
  for (i <- [0..max], i % 2 == 0)
    result += i;
  return result;
}



list[int] even3(int max) {
  result = for (i <- [0..max], i % 2 == 0)
    append i;
  return result;
}



list[int] even4(int max) {
  return for (i <- [0..max], i % 2 == 0)
           append i;
}



list[int] even5(int max) {
  return [ i | i <- [0..max], i % 2 == 0];
}



list[int] even6(int max) = [i | i <- [0..max], i % 2 == 0];



set[int] even7(int max) = {i | i <- [0..max], i % 2 == 0};



:help



import IO;
remove(|home:///my-project-name|, recursive=true);



import util::Reflective;
newRascalProject(|home:///my-project-name|)



import util::FileSystem;
// there are these files in the newly create project
[ l | /file(l) := crawl(|home:///my-project-name|) ]



((|home:///my-project-name/src/main/rascal/Main.rsc|))



int a = 0; // statement
int f(int i) = 2 * i; // function declaration
syntax Exp = Exp "+" Exp; // syntax declaration
f(2) * f(2) // expression
:help // builtin command



:help



import List;
:set tracing true
index(["a","b","c"])



:set tracing false
index(["a","b","c"])



import lang::rascal::tests::library::String;
:test



a = 1;
b = 2;
c = 3;



c = 3;


// TODO:
// (reverse-i-search)`a': a = 3;



1+2



[ n * n | int n <- [0..10] ]



// import List;
size([ n * n | int n <- [0..10] ])



int x = 2;
int y = 3;



x * y



:quit



1 + 1
myList = [ i | i <- [1..11], i % 2 == 0];
import Prelude;
println("Hello <myList> is <size(myList)> long");



x = 1;
// TODO:
// x = 1








x = 1
;



import IO;
for (int i <- [0..11]) {
    println("Counting <i>");
}



import IO;
for (int i <- [0..11]) {

}



// declaring a normal data type with 2 constructors of which the second also has keyword parameters:
data _Type_
  = _ConstructorName1_ ( _ParameterType1_ _ParameterName1_, _ParameterType2_ _ParameterName2_)
  | _ConstructorName2_ ( _ParameterType1_ _ParameterName1_, _KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_)
  ;

// declaring a type-parametrized data-type:
// TODO:
// data _Type_ [&_TypeParameter1_, &_TypeParameter2_]
data _Type_[&_TypeParameter1_, &_TypeParameter2_]
  = _ConstructorName1_ ( &_TypeParameter1_ _ParameterName1_, &_TypeParameter2_ _ParameterName2_)
  | _ConstructorName2_ ( &_TypeParameter1_ _ParameterName1_, _KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_)
  ;  


// declaring common keyword parameters:
data _Type_(_KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_);

// declaring a normal data type with 2 constructors of which the second also has keyword parameters:
// TODO:
// data _Type_
//   = _ConstructorName1_ ( _ParameterType1_ _ParameterName1_, _ParameterType2_ _ParameterName2_, ...)
//   | _ConstructorName2_ ( _ParameterType1_ _ParameterName1_, ..., _KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_, ...)
//   ;

// declaring a type-parametrized data-type:
// TODO:
// data _Type_ [&_TypeParameter1_, &_TypeParameter2_]
//   = _ConstructorName1_ ( &_TypeParameter1_ _ParameterName1_, &_TypeParameter2_ _ParameterName2_, ...)
//   | _ConstructorName2_ ( &_TypeParameter1_ _ParameterName1_, ..., _KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_, ...)
//   ;  


// declaring common keyword parameters:
// TODO:
// data _Type_(_KeywordType1_ _KeywordType1_ = _KeywordDefaultExp1_, ...);



data Bool 
  = tt() 
  | ff() 
  | conj(Bool L, Bool R)  
  | disj(Bool L, Bool R)
  ;



example = conj(tt(),ff());
example.L
example.R



data Bool(loc origin=|unknown:///|);
example = tt(origin=|home:///MyDocuments/test.bool|);
example.origin



data SortedList[&T] = sorted(list[&T] lst);

SortedList[&T] sorted([*&T a, &T e, *&T b, &T f, *&T c]) = sorted([*a, f, *b, e, *c]) when f < e;
sorted([3,2,1])



sorted(["tic", "tac", "toe"])



Bool conj(ff(), Bool _) = ff();
Bool conj(tt(), Bool b) = b;
Bool disj(tt(), Bool _) = tt();
Bool disj(ff(), Bool b) = b;



disj(conj(tt(),tt()), ff())



data L = Cell(int nm) | Cell(int nm, L rest_of_list); 



L q = Cell(1, Cell(2, Cell(3, Cell(4))));



data ND;                              // Forward declaration of ND to include it in the definition of Atom.
data Atom = Atom(int a) | Atom(ND b); // An attempt to define Atom without the forward declaration would fail here.
data ND = ND(list[Atom] l);           // Final declaration of ND which re-uses Atom which itself re-uses ND



Atom g = Atom(ND([Atom(1), Atom(ND([Atom(2), Atom(3)]))]));



alias Name  = Type;
alias Name[&T1, ] = Type;
// TODO:
// alias Name[&T1, ...] = Type



alias ModuleId = str;
alias Frequency = int;



alias IntGraph = rel[int from, int to];



alias Graph[&T] = rel[&T from, &T to];



Graph[int,int] myGraph = {<1,2>,<2,3>};
rel[int,int] myRel = {<4,5>,<5,6>,<6,4>};
myGraph = myRel;
myRel = myGraph;



nodes = myGraph<from> + myGraph<to>;



extend QualifiedName;



Modifiers Type Name( Type Var, Type Var ) Body
Modifiers Type Name( Type Var, Type Var Type Name ) Body
Modifiers Type Name( Pattern, Pattern) Body
Modifiers Type Name( Pattern, Pattern, Type Name) Body
// TODO:
// Modifiers Type Name( Type~1~ Var~1~, ..., Type~n~ Var~n~ ) Body
// Modifiers Type Name( Type~1~ Var~1~, ..., Type~n~ Var~n~ Type~0~ Name~0~... ) Body
// Modifiers Type Name( Pattern~1~, ..., Pattern~n~) Body
// Modifiers Type Name( Pattern~1~, ..., Pattern~n~, Type~0~ Name~0~...) Body



{ 
   Statements
}

// TODO:
// throws Exception~1~, ..., Exception~n~
// throws Exception1, ..., Exceptionn

= Expression;



public
private
default
java
test

public java
private java
public test
private test
public default
private default



rel[int, int] invert(rel[int,int] R){
   return {<Y, X> | <int X, int Y> <- R };
}



invert({<1,10>, <2,20>});



rel[&T2, &T1] invert2(rel[&T1,&T2] R){  
   return {<Y, X> | <&T1 X, &T2 Y> <- R };
}



invert2({<1,10>, <2,20>});
invert2({<"mon", 1>, <"tue", 2>});



tuple[&T2, &T1] swap(tuple[&T1, &T2] TP) { return <TP[1], TP[0]>;}
swap(<1, 2>);
swap(<"wed", 3>);



int f(int i) = 1;
int f(real r) = 2;
f(0);
f(0.0);



int f(0) = 1;
default int f(int n) = n * f(n - 1);
f(0);
f(2);



data B = t() | f() | neg(B);



B neg(neg(B b)) = b;
neg(t());
neg(neg(f()));



import QualifiedName;



import IO;
println("IO library was imported.");



module Package::Name // <1>

// Import~1~ // <2>
// Extend~1~ 
// ...
// Import~n~
// Extend~n~

// SyntaxDefinition~1~ // <3>
// ...
// SyntaxDefinition~2~

// Declaration~1~ // <4>
// ...
// Declaration~n~
// TODO:
Import // <2>
Extend 
// ...
Import
Extend

SyntaxDefinition // <3>
// ...
SyntaxDefinition

Declaration // <4>
// ...
Declaration



_Name1_::_Name2_::_Namen_
// _Name~1~_::_Name~2~_:: ... ::_Name~n~_



_Module_ :: _Name_



module demo::basic::Hello

import IO;

void hello() {
  println("Hello world!");
}



int i = 3;



int j = "abc";



num n = i;
n = 3.14;



value v = true;
v = "abc";
v = [1, 2, 3];



EXP parseEXP(str s){  }
STAT parsePROGRAM(str s) {  }
PROGRAM parsePROGRAM(str s) {  }



&T parse(type[&T] start, str s) {  }

// EXP parseEXP(str s){ ... }
// STAT parsePROGRAM(str s) { ... }
// PROGRAM parsePROGRAM(str s) { ... }



// &T parse(type[&T] start, str s) { ... }



parse(#EXP, "1+3");



public &T <: num abs(&T <: num N)
{
	return N >= 0 ? N : -N;
}



import util::Math;
abs(-3);
abs(-3.5);



&T <: node setAnnotations(&T <: node x, map[str, value] annotations);



import Node;
nd = "f"(10, "abc");



setAnnotations(nd, ("color" : "red", "size" : "large"));



data Suite = hearts() | diamonds() | clubs() | spades();
st = diamonds();



setAnnotations(st, ("player" : "Hossein", "gain" : "120"));



tuple[&B, &A] swap(&A a, &B b) { return <b, a>; }
swap(1,2);
swap("abc", 3);



alias Graph[&Node] = rel[&Node, &Node];
Graph[int] GI = {<1,2>, <3,4>, <4,1>};
Graph[str] GS = {<"a", "b">, <"c","d">, <"d", "a">};



start syntax Nonterminal = Alternatives;

lexical Nonterminal = Alternatives;

layout Nonterminal = Alternatives;

keyword Nonterminal = Alternatives;



Tags           Symbols         
Tags left      Symbols          // <1>
Tags right     Symbols          // <1>
Tags non-assoc Symbols          // <1>
Tags left      Name : Symbols   // <2>
Tags right     Name : Symbols   // <2>
Tags non-assoc Name : Symbols   // <2>
left      ( Alternatives )      // <3>
right     ( Alternatives )      // <3>
non-assoc ( Alternatives )      // <3>

Alternatives  Alternatives   // <4>
// TODO:
// Alternatives~1~ | Alternatives~2~   // <4>

Alternatives > Alternatives   // <5>
// TODO:
// Alternatives~1~ > Alternatives~2~   // <5>



layout L = [\ ]*; start Program = Statement*;
// TODO:
// layout L = [\ ]*; start Program = Statement*;`



// layout is lists of whitespace characters
layout MyLayout = [\t\n\ \r\f]*;

// identifiers are characters of lowercase alphabet letters, 
// not immediately preceded or followed by those (longest match)
// and not any of the reserved keywords
lexical Identifier = [a-z] !<< [a-z]+ !>> [a-z] \ MyKeywords;

// this defines the reserved keywords used in the definition of Identifier
keyword MyKeywords = "if" | "then" | "else" | "fi";

// here is a recursive definition of expressions 
// using priority and associativity groups.
syntax Expression 
  = id: Identifier id
  | null: "null"
  | left multi: Expression l "*" Expression r
  > left ( add: Expression l "+" Expression r
         | sub: Expression l "-" Expression r
         )
  | bracket "(" Expression ")"
  ;



import analysis::grammars::Ambiguity;
diagnose(t); // for any t of which you know it contains an ambiguity



import IO;

lexical Id = [a-z]+ \ "type";

layout Whitespace = [\ \t\n]*;

start syntax Program = Stat+;

syntax Stat
    = "type" Id ";"
    | Type Id ";"
    | Exp ";"
    ;

syntax Type
    = Id
    | Id "*"
    ;

syntax Exp
    = Id
    | left Exp "*" Exp
    ;

start[Program] program(str input) {
  // we always start with an empty symbol table
  set[str] symbolTable = {};

  // here we collect type declarations
  Stat declareType(s:(Stat) `type <Id id>;`) {
    println("declared <id>");
    symbolTable += {"<id>"};
    return s;
  }

  // here we remove type names used as expressions
  Exp filterExp(e:(Exp) `<Id id>`) {
    if ("<id>" in symbolTable) {
        println("filtering <id> because it was declared as a type.");
        filter;
    }
    else {
        return e;
    }
  }

  return parse(#start[Program], input, |demo:///|, filters={declareType, filterExp}, hasSideEffects=true);
}



example = "a * a;";
p = program(example);
example = "type a;
          'a * a;
          ";
p = program(example);



lexical Id = [a-z]+;

syntax Exp
  = lookup: Id
  | call  : Exp "(" {Exp ","}* ")"
  >d left comma : Exp "," Exp
  ;



/amb(_) := [Exp] "a(a,b)"



lexical Id = [a-z]+;



syntax Exp
  = lookup: Id
  | bracket "(" Exp ")"
  | call  : Exp "(" {Exp!comma ","}* ")"
  > left comma : Exp "," Exp
  ;



(Exp) `<Id id>(<Exp first>,<Exp last>)` := [Exp] "a(a,b)"



(Exp) `a,b(<Exp first>,(d,<Exp z>))` := [Exp] "a,b(c,(d,e))"



syntax Program = "{" "statement"* "}";
layout Spaces = [\ ]*;



import ParseTree;
parse(#Program, "{ }");



syntax Program = "{" "statement"* "}";
layout Spaces = [\ ]* !>> [\ ];



import ParseTree;
parse(#Program, "{ }");



lexical Id = [a-z]+;
syntax Program = Id+;
layout Spaces = [\ ]*;



import ParseTree;
parse(#Program, "ab");



lexical Id = [a-z]+ !>> [a-z];
syntax Program = Id+;
layout Spaces = [\ ]*;



import ParseTree;
parse(#Program, "ab");



lexical Id = [a-z]+ \ "let" !>> [a-z]; // <1>
syntax E
  = "let" Id // <2>
  | Id+      // <2>
  ;
layout Spaces = [\ ]*; // <3>



import ParseTree;
parse(#E, "leta");



lexical Id = "let" !<< [a-z]+ \ "let" !>> [a-z]; 
syntax E
  = "let" Id 
  | Id+      
  ;
layout Spaces = [\ ]*; 



lexical Id = [a-z] !<< [a-z]+ \ "let" !>> [a-z]; 
syntax E
  = "let" Id 
  | Id+      
  ;
layout Spaces = [\ ]*; 



import ParseTree;
parse(#E, "leta");



syntax Exp 
  = A: Id
  | B: Number 
  > C: Exp "[" Exp "]" 
  | D: Exp "!"
  > E: Exp "*" Exp 
  > F: Exp "+" Exp
  | bracket G: "(" Exp ")";
//   TODO:
//   > F: Exp "+" Exp;
//   | bracket G: "(" Exp ")"
  ;



// the following definition
syntax A = "a";
// would make the following test succeed:
test a() = parse(#A,"a") ==  
appl(prod(
    sort("A"), 
    [lit("a")], 
    {}),
  [appl(
      prod(
        lit("a"),
        [\char-class([range(97,97)])],
        {}),
      [char(97)])]);
// you see that the defined non-terminal A ends up as the production for the outermost node. As the only child is the tree for recognizing the literal a, which is defined to be a single a from the character-class [ a ].



// when we use labels in the definitions, they also end up in the trees:
// the following definition
lexical A = myA:"a" B bLabel;
lexical B = myB:"b";
// would make the following [Test] succeed:
test a() = parse(#A,"ab") == appl(prod(label("myA",lex("A")),[lit("a"),sort("bLabel",lex("B"))],{}),[appl(prod(lit("a"),[\char-class([range(97,97)])],[char(97)]),appl(prod(label("myB", lex("B"),[lit("b")],{}),[appl(prod(lit("b"),[\char-class([range(98,98)])],[char(98)]))])) )]);
// TODO:
// test a() = parse(#A,"ab") == appl(prod(label("myA",lex("A")),[lit("a"),sort("bLabel",lex("B"))],{}),[appl(prod(lit("a"),[\char-class([range(97,97)]),[char(97)]),appl(prod(label("myB", lex("B"),[lit("b")],{}),[appl(prod(lit("b"),[\char-class([range(98,98)]),[char(98)])]) ]);
// here you see that the alternative name is a label around the first argument of `prod` while argument labels become labels in the list of children of a `prod`.



lexical AlphaNumeric = [a-zA-Z0-9];



lexical AnythingExceptQuote = ![\"];



lexical Id = [a-z]+ !>> [a-z];



lexical Id = [a-z] !<< [a-z]+ !>> [a-z];



lexical Id = [a-z]+ !>> [a-z] \ "if" \ "else" \ "fi";



syntax Statement = "if" Expression "then" Statement ("else" Statement)? "fi";



syntax Statement = "{" {Statement ";"}* "}";



syntax Declaration = ("public" | "private" | "static" | "final")* Type Id "(" {(Type Id) ","}* ")" Statement;



_Type_ _Name_; 



int max = 100;
min = 0;



day = {<"mon", 1>, <"tue", 2>, <"wed",3>, 
       <"thu", 4>, <"fri", 5>, <"sat",6>, <"sun",7>};



int month = 12;
month ="December";



if( 4 > 3){ x = "abc"; } else { x = "def";}
x;



int triple(int x) = 3 * x;



triple(5)



triple([1,2,3])



list[int] triple(list[int] L) = [3 * x | x <- L];
triple([1,2,3]);



{<1,10>, <2,20>} o {<10,100>, <20, 200>};



{<1,5,10>, <2,6,20>} o {<10,100>, <20, 200>};



{<1,2>, <2,3>,<4,5>}+
{<1,2>, <2,3>,<4,5>}*



{<1,2,3>, <2,3,4>,<4,5,6>}+
{<1,2,3>, <2,3,4>,<4,5,6>}*



$2013-07-15T09:15:23.123+03:00$;


// TODO:
// $2013-07-40T09:15:23.123+03:00$;



$2010-15-15T09:15:23.123+03:00$;



data M::D = d();



data D = d();



$2013-07-15$ < $2014-07-15$



$2013-01-11T23:03:56.901+01:00$ < $2013-01-11T23:05:00.901+01:00$



$2013-07-15$ < $T20:03:56.901+01:00$



@javaClass{org.rascalmpl.library.Prelude}
public java int size(list[&T] lst);



@javaClass{org.rascalmpl.library.Preludexxx}
public java int size(list[&T] lst);



@javaClass{org.rascalmpl.library.Preludexxx}
public java int size(list[&T] lst){
  return 0;
}



@javaClass{org.rascalmpl.library.Prelude}
public java int size(list[&T] lst);



@javaClass{org.rascalmpl.library.Prelude}
public int size(list[&T] lst);



int triple(int x) {
   x * 3;
}
triple(5)



int triple(int x) {
   return x * 3;
}
triple(5)



int triple(int x) = x * 3;
triple(5)



import List;



import Lis;



int incr(int x) = x + 1;
incr(3, delta=5);



int incr(int x, int delta=1) = x + delta;
incr(3, delta=5);



java int incr(int x) {}



void dummy() { return; }
[1, *dummy(), 2]
{1, *dummy(), 2}



list[int] dummy() { 
  return [17]; 
}
[1, *dummy(), 2]
{1, *dummy(), 2}



bool[int] x;
list[int,str] l;
map[str, int, int]  m;
set[int,str] s;



int x <- 17
b <- true



int x <- [17]
b <- {true}



tuple[int n, str] T;
rel[str name, int] R;



data D = d1(int key) | d2(str name, int key);



data D = d1(int key) | d2(str key);



data D = d1(int intKey) | d2(str strKey);



tuple[int x, str x] Q = <3,"abc">;



data D = d(int x);
alias D = str;



alias D = int;
alias D = str;



int n = 3;
int n = 4;



data Fruit = apple(int n) | orange(int n);
anno str Fruit @ quality;
piece = orange(13);
piece@quality = "great";



piece@qual



tuple[str name, int age] Jo = <"Jo", 33>;
Jo.gender;



data Person = person(str name, int age);
jo = person("Jo", 33);
jo.gender;



triple(5)



int triple(int n) = 3 * n;
triple(5)



size([20, 1, 77]);



import List;
size([20, 1, 77]);



import Prelude;
size([20, 1, 77]);



n + 1;



n = 3;
n + 1;



int n = 3;
n + 1;



@javaClass{org.rascalmpl.library.Prelude}
public java int size(list[&T] lst);



@javaClass{org.rascalmpl.library.Prelude}
public java int siz(list[&T] lst);



int incr(int n, int delta=1) = n + delta;



incr(3, diff=5);



incr(3, delta=5);



M::x = 3;
M::f(3);



import IO;
readFileLines(|standard:///demo/basic/Hello.rsc|);



readFileLines(|std:///demo/basic/Hello.rsc|);



import ParseTree;
syntax X = "a" Y;
parse(#X, "ab");



myint incr(myint n) = n + 1;



alias myint = int;
myint incr(myint n) = n + 1;
incr(3);



[1, *x, 3]



x = [5];
[1, *x, 3]



int incr(int x, int delta = 1) = n + delta;



incr(3, delta="more");



int n = "abc";



int n = 123;



assert 3;



for(int i <- [1..5]) append i*i;



append 3;



if(int N := 35){ if(N > 10) fail; }



if(true) { fail; }



fail;



data CTree = leaf(int n) | red(CTree left, CTree right) | green(CTree left, CTree right);



CTree T = red(green(leaf(1), red(leaf(2), leaf(3))), red(leaf(4), leaf(5)));



visit(T){ case red(CTree l, CTree r): insert red(r,l); }



insert red(leaf(1), leaf(2));



(0 | it + n | int n <- [1,5,9] )



it + 3



int triple(int n) { return 3 * n; }
triple(5);



return 3;



void dummy() { return; }
int n := dummy();



x



x = 3;
x + 5;



int x = 3;
x + 5;



L = [1,2,3];



[1, 2, 3] / 4;



L *= 3;



$2010-07-15$.justTime;



17(3, "abc");



"abc"[1];
[1,2,3][1];
"f"(1,2,3)[1];
("a":1, "b":2, "c":3)["b"]



true[1];
123[1];
{1,2,3}[1];



[1,2,3][2,1];
("a":1, "b":2, "c":3)["c", "d"];
<1, 2, 3>[5,6];



syntax A = "a";
syntax E = A | "(" E ")" | E "+" E;



import ParseTree;



parse(#E, "a+a");



parse(#E, "a+a+a");



syntax A = "a";
syntax E = A | "(" E ")" | left E "+" E;
import ParseTree;
parse(#E, "a+a+a");



syntax A = "a";
syntax E = A | "(" E ")" | left E "+" E | left E "*" E;
import ParseTree;
t = parse(#E, "a+a*a", allowAmbiguity=true);
// Is the forest indeed ambiguous?
/amb(_) := t
// How many alternatives?
import Set;
import IO;
/amb(a) := t ? size(a) : 0; 
// Which rules are at the top of the alternatives?
if (/amb({a1, a2}) := t) 
  println("alternative 1: <a1.prod>
          'alternative 2: <a2.prod>");



import IO;
try 
  parse(#E, "a+a*a");
catch Ambiguity(loc l, str s, _): 
  println("the input is ambiguous for <s> on line <l.begin.line>");



3/0;



import util::Math;
tan(-550000000000000000000000);



import Exception;
import IO;
try 
  println(3/0); 
catch ArithmeticException(str msg): 
  println("The message is: <msg>");



assert 3 > 4;



int incrPositive(int n) { 
  assert n > 0: "n should be greater than 0"; return n + 1; 
}



incrPositive(3);



incrPositive(-3);



import Exception;
import IO;
try 
  println(incrPositive(-3)); 
catch AssertionFailed(str msg): 
  println("incrPositive: <msg>");



import List;
L = [];



head(L);



tail(L);



import Exception;
import IO;
try 
  println(head(L)); 
catch EmptyList(): 
  println("Cannot take head of empty list");



import Map;
M = ();



getOneFrom(M);



import Exception;
import IO;
try 
  println(getOneFrom(M)); 
catch EmptyMap(): 
  println("Cannot use getOneFrom on empty map");



import Set;
S = {};



getOneFrom(S);



import Exception;
import IO;
try 
  println(getOneFrom(S)); 
catch EmptySet(): 
  println("Cannot apply getOneFrom to empty set");



L = [0, 10, 20, 30, 40];



L[5];



import Exception;
import IO;
try 
  L[5]; 
catch IndexOutOfBounds(msg):
  println("The message is: <msg>");



NOW = $2013-01-13T22:16:51.740+01:00$;
NOW.month = 13;



someLoc = |home:///abc.txt|;
someLoc.offset = -1;



someLoc = |home:///abc.txt|;
someLoc.scheme = "a:b";



|home:///|;
|home://|;



NOW = $2016-09-18$;
NOW.hour = 14;



someLoc = |home:///abc.txt|;
someLoc.begin = <1, 2>;



NOW = $T20:11:01.463+00:00$;
NOW.year = 2020;



import IO;
readFile(|myScheme:///example.rsc|);



import Exception;
try 
  readFileLines(|myScheme:///example.rsc|); 
catch IO(msg): 
  println("This did not work: <msg>");



data Fruit = apple(int n) | orange(int n);
anno str Fruit @ quality;
piece = orange(13);
piece@quality;



piece@quality?;



piece@quality ? "no quality value";



import Exception;
import IO;
try piece@quality; catch NoSuchAnnotation(l): println("No such annotation: <l>");



piece@quality = "excellent";
piece@quality;



data Entity = person(str name, int birthYear) | company(str name, Entity director);
jane = person("Jane", 2001);
icm =  company("ICM", jane);



icm.birthYear;
jane.birthYear;



import Map;
import IO;
M = ("a" : 1, "b" : 2);



M["c"]



if (M["c"]?) {
  println("defined"); 
} else {
  println("not defined");
}



M["c"] ? 3



import Exception;
try 
  println(M["c"]);
catch NoSuchKey(k): 
  println("Key <k> does not exist");



syntax As = "a"+;



import ParseTree;



parse(#As, "aaaaaaaa");



parse(#As, "aaaabaaa");



import Exception;
import IO;
try 
  parse(#As, "aaaabaaa"); 
catch ParseError(e): 
  println("Your input cannot be parsed: <e>");



/+/ := "aaaa";



$2016-09-14$.hour;
someLoc = |home:///abc.txt|;
someLoc.offset;



// Name ( Exp~1~, Exp~2~, ... )



// Name (Name~1~ = Exp~1~, Name~2~ = Exp~2~, ...)



// Name (Exp~1~, Exp~2~, ..., Name~1~ = Exp~1~, Name~2~ = Exp~2~, ...)



int square(int n) { return n * n; }



square(12);



// [ Exp~1~, ..., Exp~n~ | Exp~n+1~, ..., Exp~n+m~]
// { Exp~1~, ..., Exp~n~ | Exp~n+1~, ..., Exp~n+m~}
// ( Exp~1~ : Exp~2~ | Exp~3~, ..., Exp~n+m~)
// ( Exp~1~ | Exp~2~ | Exp~3~, ..., Exp~n+m~)



[ 3 * X | int X <- [1 .. 10] ];



[ 3 * X | int X <- [1 .. 10], X > 5];



[X, X * X | int X <- [1, 2, 3, 4, 5], X >= 3];



{X | int X <- {1, 2, 3, 4, 5}, X >= 3};



{<X, Y> | int X <- {1, 2, 3}, int Y <- {2, 3, 4}, X >= Y};
{<Y, X> | <int X, int Y> <- {<1,10>, <2,20>}};



fruits = ("pear" : 1, "apple" : 3, "banana" : 0, "berry" : 25, "orange": 35);
(fruit : fruits[fruit] | fruit <- fruits, fruits[fruit] > 10);



syntax X = "<" Type Var ">";
// TODO:
// syntax X = "<" Type Var ">";`



Exp + Exp
Exp [ Exp ]
! Exp
Exp in Exp



it = _InitExp_; // <1>
for(_Gen_, _Gen_ ) // <2>
// TODO:
// for(_Gen~1~_, _Gen~2~_, ... ) // <2>
    it = _RedExp_; // <3>
it; // <4>



L = [1, 3, 5, 7];
(0 | it + e | int e <- L);
(1 | it * e | int e <- L);



_Pat_ := _Exp_



[1, *int L, 2, *int M] := [1,2,3,2,4]



import IO;
for ([1, *int L, 2, *int M] := [1,2,3,2,4])
  println("L: <L>, M: <M>");



[1, *int L, 2, *int M] := [1,2,3,2,4] && size(L) > 0



import IO;
import List;



for ([1, *int L, 2, *int M] := [1,2,3,2,4] && size(L) > 0)
  println("L: <L>, M: <M>");



if ([1, *int L, 2, *int M] := [1,2,3,2,4] && size(L) > 0)
  println("L: <L>, M: <M>");



all(int n <- [1 .. 10], n % 2 == 0);



all(int n <- [0, 2 .. 10], n % 2 == 0);



all(int n <- [], n > 0);



true && false;
i <- [1,2,3] && (i % 2 == 0)
import IO;
if (i <- [1,2,3] && (i % 2 == 0))
  println("<i> % 2 == 0");
for (i <- [1,2,3,4] && (i % 2 == 0)) 
  println("<i> % 2 == 0");



import IO;
int i = 0;
bool incr() { i += 1; return true; }
for (int j <- [1,2,3] && incr() && (i % 2 == 0)) 
  println("once true for <j>");
i;



any(int n <- [1 .. 10], n % 2 == 0);



int N <- {"apples", "oranges"}



[ N * N | int N <- [1, 2, 3, 4, 5] ];
{<N, K> | <str K, int N> <- {<"a",10>, <"b",20>, <"c",30>}};



import IO;
false <==> false;
false <==> true;



[ X * X | int X <- [1, 2, 3, 4, 5, 6] ];
[ X * X | int X <- [1, 2, 3, 4, 5, 6], X % 3 == 0 ];



[<X, Y> | int X <- [0 .. 10], int Y <- [0 .. 10], X + Y == 10]



T = ("a" : 1, "b" : 2);



T["c"];



T["c"] ? 0;



T["c"] ? 0 += 1;



L = [10, 20, 30];
L[4] ? 0;



false ==> true;



T = ("a" : 1, "b" : 2);
T["b"]?
T["c"]?
L = [10, 20, 30];
L[1]?
L[5]?



123 := 456;
[10, *n, 50] := [10, 20, 30, 40, 50];
{10, *int n, 50} := {50, 40, 30, 30, 10};



!true;



123 !:= 456;
[10, *n, 50] !:= [10, 20, 30, 40];
{10, *n, 50} !:= {40, 30, 30, 10};



import IO;
false || true;
(i <- [1,2,3,4] && i % 2 == 0) || false
for ((i <- [1,2,3,4] && i % 2 == 0) || false) 
  println("true for <i>");



// Name ( Exp~1~, Exp~2~, ... )



data WF = wf(str word, int freq);



wf("Rascal", 10000);



data Shape
    = rectangle(int width, int height, int area=width * height);
rectangle(100,200).area
x = rectangle(100,200, area=100000);
x.area
y = rectangle(100,200);
y.area



Exp [ FieldName = Exp ]
// TODO:
// Exp~1~ [ FieldName = Exp~2~ ]



data Example
  = example(int key, str val="<key>"); // <1>
T = example(42);
T.key



data Example = example(int key, str val="<key>"); // <1>
t = example(42);
t.key = 2;
t.val
t.key += 2;
t.val



$2010-07-15$
$2010-07-15T07:15:23.123+0100$;



DT = $2010-07-15T09:15:23.123+03:00$;



DT.isDateTime;
DT.justDate;
DT.justTime;
DT.century;



$2010-07-15$ == $2010-07-15$;
$2010-07-15$ == $2010-07-14$;



$2010-07-15$ > $2010-07-14$;
$2011-07-15$ > $2010-07-15$;



$2011-07-15$ >= $2010-07-15$;
$2010-07-15$ >= $2010-07-14$;



$2010-07-14$ < $2010-07-15$;
$2011-07-15$ < $2010-07-14$;



$2010-07-15$ <= $2010-07-15$;
$2011-07-15$ <= $2010-07-14$;



$2010-07-15$ != $2010-07-14$;
$2010-07-15$ != $2010-07-15$;



[1, 2, 3];
[<1,10>, <2,20>, <3,30>];
[1, "b", 3];
[<"a",10>, <"b",20>, <"c",30>];
[["a", "b"], ["c", "d", "e"]];



L = [1, 2, 3];
[10, L, 20];
[10, *L, 20];



[] + 1;
[1] + 2;



[1] + [2]



[1] + [[2]]



[n * n | int n <- [0 .. 10], n % 3 == 0];



[n, n * n | int n <- [0 .. 10], n % 3 == 0];



[1, 2, 3] + [4, 5, 6];
[] + [1]
[1] + []
[1] + [2] + [3]



1 + []
[] + 1



[1, 2, 3, 4] - [1, 2, 3];
[1, 2, 3, 4] - [3];
[1, 2, 3, 4] - 3;
[1, 2, 3, 4] - [5, 6, 7];
[1, 2, 3, 1, 2, 3] - [1];
[1, 2, 3, 1, 2, 3] - [1, 2];



[1, 2, 3] == [1, 2, 3];
[1, 2, 3] == [3, 2, 1];



2 in [1, 2, 3];
4 in [1, 2, 3];



1 + []
1 + [2]
1 + [2,3]



[1] + [2]



[[1]] + [2]



[1, 2, 3, 4, 5] & [4, 5, 6];



[1, 2, 3] != [3, 2, 1];
[1, 2, 3] != [1, 2, 3];



4 notin [1, 2, 3];
2 notin [1, 2, 3];



[1, 2, 3] * [4, 5, 6];



["clubs", "hearts", "diamonds", "spades"] * [1 .. 13];



L = [0, 10, 20, 30, 40, 50, 60, 70, 80];



L[1..3];
L[1..];       // empty end => end of list
L[..3];       // empty begin => first element of list
L[..];        // both empty => whole list



L[3..1];      // slice contains elements with indices 3 and 2 (in that order)
L[3..3];      // empty slice when begin == end



L[2..-2];     // equivalent to L[2..7]
L[2..7];
L[-4..-2];    // equivalent to L[5..7]
L[5..7];



L[1,3..6];
L[5,3..];



L[..10];
L[..-11];



[1, 2, [10, 20, 30], 3, 4];



[1, 2, *[10, 20, 30], 3, 4];



L = [10, 20, 30];
[1, 2, *L, 3, 4];



[1, 2, 3] < [1, 2, 3, 4];
[1, 2, 3, 4] < [1, 2, 3, 4];
[1, 3, 5] < [1, 2, 3, 4, 5]



[1, 2, 3, 4] > [1, 2, 3];
[1, 2, 3, 4] > [1, 2, 3, 4];
[1, 2, 3, 4] > [1, 2, 3];
[1, 2, 3, 4, 5] > [1, 3, 5]



[1, 2, 3] <= [1, 2, 3, 4];
[1, 2, 3] <= [1, 2, 3];
[1, 3, 5] <= [1, 2, 3, 4, 5];



L = [10, 20, 30];
L[1];



L[5];



[1, 2, 3, 4] >= [1, 2, 3];
[1, 2, 3, 4] >= [1, 2, 3, 4];
[1, 2, 3, 4] >= [1, 2, 3];
[1, 2, 3, 4, 5] >= [1, 3, 5]



[<1,10>, <2,20>, <3,30>]



[<"a",10>, <"b",20>, <"c",30>]
[<"a", 1, "b">, <"c", 2, "d">]



[1, 2, 3] * [9];
[1, 2, 3] * [10, 11];



[<1,10>, <2,20>, <3,15>] o [<10,100>, <20,200>];



lrel[str street, int nm] R = [<"abc", 1>, <"abc", 2>, <"def", 4>, <"def", 5>];
R.street;



[<1,2>, <10,20>] join [<2,3>];
[<1,2>] join [3, 4];
[<1,2>, <10,20>] join [<2,3>, <20,30>];



[<1,2>, <2,3>, <3,4>]*;



R = [<1,10>, <2,20>, <1,11>, <3,30>, <2,21>];
R[1];
R[{1}];
R[{1, 2}];
RR = [<1,10,100>,<1,11,101>,<2,20,200>,<2,22,202>,
              <3,30,300>];
RR[1];
RR[1,_];



lrel[str country, int year, int amount] GDP =
[<"US", 2008, 14264600>, <"EU", 2008, 18394115>,
 <"Japan", 2008, 4923761>, <"US", 2007, 13811200>, 
 <"EU", 2007, 13811200>, <"Japan", 2007, 4376705>];



GDP["Japan"];



GDP["Japan", 2008];



[<1,2>, <2,3>, <3,4>]+;



// TODO:
//          foo://example.com:8042/over/there?name=ferret#nose
//          \_/   \______________/\_________/ \_________/ \__/
//           |           |            |            |        |
//        scheme     authority       path        query   fragment
//           |   _____________________|__
//          / \ /                        \
//          urn:example:animal:ferret:nose



|file:///home/paulk/pico.trm|(0,1,<2,3>,<4,5>)



|home://pico.trm|(0,1,<2,3>,<4,5>)



import IO;
println(readFile(|http://www.example.org|))



x = |tmp://myTempDirectory|;
x += "myTempFile.txt";



|tmp:///myDir| + "myFile";



(|tmp:///myDir| + "myFile").parent



("pear" : 1, "apple" : 3, "banana" : 0);



import Map;
("one" : 1, "two" : 2) o (1 : 10, 2 : 20);






fruits = ("pear" : 1, "apple" : 3, "banana" : 0, "berry" : 25, "orange": 35);
import String;



(fruit : fruits[fruit] | fruit <- fruits, size(fruit) <= 5);



(fruit : fruits[fruit] | fruit <- fruits, fruits[fruit] > 10);



("apple": 1, "pear": 2) - ("banana": 3, "apple": 4);



("apple": 1, "pear": 2) == ("pear": 2, "apple": 1);
("apple": 1, "pear": 2) == ("apple": 1, "banana": 3) 



"pear" in ("apple": 1, "pear": 2);
"pineapple" in ("apple": 1, "pear": 2);



("apple": 1, "pear": 2) & ("banana": 3, "apple": 1);
("apple": 1, "pear": 2) & ("banana": 3, "apple": 4);



("apple": 1, "pear": 2) != ("apple": 1, "banana": 3);
("apple": 1, "pear": 2) != ("pear": 2, "apple": 1);



"pineapple" notin ("apple": 1, "pear": 2);
"pear" notin ("apple": 1, "pear": 2);



("apple": 1, "pear": 2) < ("pear": 2, "apple": 1, "banana" : 3);
("apple": 1, "pear": 2) < ("apple": 1, "banana" : 3);



("pear": 2, "apple": 1, "banana" : 3) > ("apple": 1, "pear": 2);
("apple": 1, "banana" : 3) > ("apple": 1, "pear": 2);



("apple": 1, "pear": 2) <= ("pear": 2, "apple": 1);
("apple": 1, "pear": 2) <= ("pear": 2, "apple": 1, "banana" : 3);
("apple": 1, "pear": 2) <= ("apple": 1, "banana" : 3);



colors = ("hearts":"red", "clover":"black", 
          "trumps":"black", "clubs":"red");
colors["trumps"];



colors[0];
colors["square"];



("pear": 2, "apple": 1) >= ("apple": 1, "pear": 2);
("pear": 2, "apple": 1, "banana" : 3) >= ("apple": 1, "pear": 2);
("apple": 1, "banana" : 3) >= ("apple": 1, "pear": 2);



("apple": 1, "pear": 2) + ("banana": 3, "kiwi": 4);
("apple": 1, "pear": 2) + ("banana": 3, "apple": 4);



"my_node"(1, true, "abc");



"my_node1"(1, "my_node2"(3.5, ["a", "b", "c"]), true);



"my_node2"(1,2,size=2,age=24);



"f"(1, "abc", true) == "f"(1, "abc", true);
"f"(1, "abc", true) == "f"(1, "def", true);



Exp [ FieldName = Exp ]
// Exp~1~ [ FieldName = Exp~2~ ]



node T = "name"(1, x="abc");
T[x = "def"];
T
T = T[x="def"];
T



tuple[int key, str val] T = <1, "abc">;
T.val;



"g"(3) > "f"(10, "abc");
"f"(10, "abc") > "f"(10);



"g"(3) >= "f"(10, "abc");
"f"(10, "abc") >= "f"(10);
"f"(10, "abc") >= "f"(10, "abc");



"f"(10, "abc") < "g"(3);
"f"(10) < "f"(10, "abc");



"f"(10, "abc") <= "f"(10, "abc");
"f"(10) <= "f"(10, "abc");



"f"(1, "abc", true) != "g"(1, "abc", true);
"f"(1, "abc", true) != "f"(1, "abc", true);



ND = "f"(0, "abc", 20, false, 40, [3,4,5], 60, {"a", "b"}, 80);



ND[1..3];
ND[1..];       // empty end => end of list of children
ND[..3];       // empty begin => first child of list
ND[..];        // both empty => whole list of children



ND[3..1];      // slice contains children with indices 3 and 2 (in that order)
ND[3..3];      // empty slice when begin == end



ND[2..-2];     // equivalent to ND[2..7]
ND[2..7];
ND[-4..-2];    // equivalent to ND[5..7]
ND[5..7];



ND[1,3..6];
ND[5,3..];



ND[..10];
ND[..-11];



F = "f"(1, "abc", false);
F[0]
F[1]
F[2]



F[3];



12 + 13
12 + 13.5



(3 > 2) ? 10 : 20
(3 > 20) ? 10 : 20



12 / 3
10 / 3
12 / 3.0
10 / 3.0
12 / 0



12 == 12
12 == 12.0
12 == 13
12 == 13.0
3.14 == 3.14
3.14 == 3



13 > 12
12 > 13
13.5 > 12
12.5 > 13



13 >= 12
12 >= 13
13.5 >= 12
12.5 >= 13



13 < 12
12 < 13
13.5 < 12
12.5 < 13



13 <= 12
12 <= 13
13.5 <= 12
12.5 <= 13



12 * 13
12 * 13.5
-12*13



-12
-13.5
- -12



12 != 13
12 != 12
12 != 13.0
12.0 != 13
3.14 != 3
3.14 != 3.14



12 % 5
12 % 6



13.5 % 6



13 - 12
13.5 - 12
12 - 13
12 - 13.5



[1 .. 10];
[1, 3 .. 10];
[0.5, 3.2 .. 10];
[1, -2 .. -10];



[1, 3 .. -10];



import Type;



#int
#list[int]
#rel[int from, int to]



#int.symbol



data Nat = zero() | succ(Nat prev) | add(Nat l, Nat r) | mul(Nat l, Nat r);
#Nat



import Type;
#Nat.definitions[adt("Nat",[])]



type(\int(),())
type(\int(),()) == #int



import ValueIO;
int testInt = readTextValueString(#int, "1");
tuple[int,int] testTuple = readTextValueString(#tuple[int,int], "\<1,2\>");



{<1,10>, <2,20>, <3,30>}



{<"a",10>, <"b",20>, <"c",30>}
{<"a", 1, "b">, <"c", 2, "d">}



{1, 2, 3} * {9};
{1, 2, 3} * {10, 11};



import Relation;
{<1,10>, <2,20>, <3,15>} o {<10,100>, <20,200>};



rel[str day, int daynum, int length] Traffic = 
{<"mon", 1, 100>, <"tue", 2, 150>, <"wed", 3, 125>, 
 <"thur", 4, 110>, <"fri", 5, 90>};
Traffic<length,daynum>;
Traffic<2,day>;



rel[str street, int nm] R = {<"abc", 1>, <"abc", 2>, <"def", 4>, <"def", 5>};
R.street;



{<1,2>, <10,20>} join {<2,3>};
{<1,2>} join {3, 4};
{<1,2>, <10,20>} join {<2,3>, <20,30>};



{<1,2>, <2,3>, <3,4>}*;



R = {<1,10>, <2,20>, <1,11>, <3,30>, <2,21>};
R[1];
R[{1}];
R[{1, 2}];
RR = {<1,10,100>,<1,11,101>,<2,20,200>,<2,22,202>,
              <3,30,300>};
RR[1];
RR[1,_];



rel[str country, int year, int amount] GDP =
{<"US", 2008, 14264600>, <"EU", 2008, 18394115>,
 <"Japan", 2008, 4923761>, <"US", 2007, 13811200>, 
 <"EU", 2007, 13811200>, <"Japan", 2007, 4376705>};



GDP["Japan"];



GDP["Japan", 2008];



{<1,2>, <2,3>, <3,4>}+;



rel[int,int] tclosure(rel[int,int] R) {
   tc = R;
   while(true){
      tc1 = tc;
      tc += tc o R;
      if(tc1 == tc)
         return tc;
   }
}
tclosure({<1,2>, <2,3>, <3,4>});



{1, 2, 3};
{<1,10>, <2,20>, <3,30>};
{1, "b", 3};
{<"a", 10>, <"b", 20>, <"c", 30>}
{{"a", "b"}, {"c", "d", "e"}}



S = {1, 2, 3};



{10, S, 20};



{10, *S, 20};



{ N * N | int N <- [0 .. 10]};
{ N * N | int N <- [0 .. 10], N % 3 == 0};



{1, 2, 3, 4} - {1, 2, 3};
{1, 2, 3, 4} - {3};
{1, 2, 3, 4} - 3;
{1, 2, 3, 4} - {5, 6, 7};



{1, 2, 3} == {3, 2, 1};
{1, 2, 3} == {1, 2};



2 in {1, 2, 3};
4 in {1, 2, 3};



{1, 2, 3} + 4;
1 + { 2, 3, 4};
{1} + 1;
1 + {1};



{1, 2, 3, 4, 5} & {4, 5, 6};



{1, 2, 3} != {3, 2, 1};
{1, 2, 3} != {1, 2};



4 notin {1, 2, 3};
4 notin {1, 2, 3, 4};



{1, 2, 3} * {4, 5, 6};



{"clubs", "hearts", "diamonds", "spades"} * {1,2,3,4,5,6,7,8,9,10,11,12,13};



{1, 2, {10, 20, 30}, 3, 4};



{1, 2, *{10, 20, 30}, 3, 4};



S = {10, 20, 30};
{1, 2, *S, 3, 4};



{1, 2, 3} < {1, 2, 3, 4};
{1, 2, 3} < {1, 3, 4};
{1, 2, 3} < {1, 2, 3};



{1, 2, 3, 4} > {3, 2, 1};
{1, 2, 3, 4} > {4, 3, 2, 1};



{1, 2, 3} <= {1, 2, 3, 4};
{1, 2, 3} <= {1, 2, 3};



{1, 2, 3, 4} >= {3, 2, 1};
{1, 2, 3, 4} >= {4, 3, 2, 1};



{1, 2, 3} + {4, 5, 6};
{1,2,3} + {2,3,4};
{1, 2, 3} + {3};
{2} + { 2, 3, 4};



N = 13;
"The value of N is <N>";
"The value of N*N is <N*N>";
"The value is <(N < 10) ? 10 : N*N>";



"N is <if(N < 10){> small <} else {> large <}>";
"N is <if(N < 10){> small <} else {> large (<N>)<}>";
"before <for(x<-[1..5]){>a <x> b <}>after";



import IO;
println("hello
this
  is
    new")



if (true)
  println("this is
          'what
          '  margins
          'are good for
          ");



str genMethod(str n) = "int <n>() {
                       '  return 0;
                       '}";
str genClass() = "class myClass {
                 '  <genMethod("myMethod")>
                 '}";
println(genClass());



"abc" + "def";



"abc" == "abc";
"abc" == "defghi";



"abcdef" > "abc";
"defghi" > "abcdef";
"a" > "abc";



"abc" >= "abc";
"abcdef" >= "abc";
"defghi" >= "abcdef";
"a" >= "abc";



"abc" < "abcdef";
"abc" < "defghi";
"abc" < "a";



"abc" <= "abc";
"abc" <= "abcdef";
"abc" <= "defghi";
"abc" <= "a";



"abc" != "defghi";
"abc" != "abc";



S = "abcdefghi";



S[1..3];
S[1..];       // empty end => end of string
S[..3];       // empty begin => first character of string
S[..];        // both empty => whole string



S[3..1];      // slice contains characters with indices 3 and 2 (in that order)
S[3..3];      // empty slice when begin == end



S[2..-2];     // equivalent to S[2..7]
S[2..7];
S[-4..-2];    // equivalent to S[5..7]
S[5..7];



S[1,3..6];
S[5,3..];



S[..10];
S[..-11];



S = "abc";
S[1];



S[5];



tuple[str first, str last, int age] P = <"Jo","Jones",35>;
P.first;
P.first = "Bo";



<"abc", 1, 2.5> + <true, "def">;



<1, "abc", true> == <1, "abc", true>;



Exp [ FieldName = Exp ]
// Exp~1~ [ FieldName = Exp~2~ ]



tuple[int key, str val] T = <1, "abc">;
T[val = "def"];
 T;



rel[str day, int daynum, int length] traffic = 
{<"mon", 1, 100>, <"tue", 2, 150>, <"wed", 3, 125>, <"thur", 4, 110>, <"fri", 5, 90>};
traffic<length,daynum>
traffic<2,day>
// for every tuple we can use the same notation
import IO;
for (tup <- traffic) {
  println(tup<2,day>);
}



tuple[int a, str b] T = <1,"hello">;
T.a
T.b



<1, "def", true> > <1, "abc", true>;



<1, "abc", true> > <1, "abc", true>;
<1, "def", true> > <1, "abc", true>;



<1, "abc", true> < <1, "def", true>;



<1, "abc", true> <= <1, "abc", true>;
<1, "abc", true> <= <1, "def", true>;



<1, "abc", true> != <1, "abc">;
<1, "abc", true> != <1, "abc", true>;



T = <"mon", 1>;
T[0];



( 3 > 2 ) ? 30 : 40;
( 3 < 2 ) ? "abc" : {3, 4};






value X = "abc";
value Y = "abc";
value Z = 3.14;



X == Y;



X == Z;



value X = "def";
value Y = "abc";
value Z = 3.14;



X > Y;



X > Z;



value X = "def";
value Y = "abc";
value Z = 3.14;



X >= Y;



X >= Z;



value X = "abc";
value Y = "def";
value Z = 3.14;



X < Y;



X < Z;



value X = "abc";
value Y = "def";
value Z = 3.14;



X <= Y;



X <= Z;



value X = "abc";
value Y = "abc";
value Z = 3.14;



X != Y;



X != Z;



Strategy visit ( _Exp_ ) {
// TODO:
// case _PatternWithAction~1~_;
// case _PatternWithAction~2~_;
// ...
// default: ...
}



visit(t) {
     case leaf(int N): c = c + N;   
   };



visit(t) {
     case red(l, r) => green(l, r)   
   };



bottom-up visit(e){
           case Exp e1 => simp(e1)


case red(CTree l, CTree r) => red(r,l)
case red(l, r) => green(l, r)



case /Leila/: println("The topic is Starwars");
case red(_, _):    println("A red root node");
case red(_,_): c = c + 1; 



case red(_,_): { c = c + 1; println("c = <c>"); }

         }


Concrete pattern with expected symbol type; (Symbol) ` Token~1~ Token~2~ ... Token~n~ `
// Concrete pattern with expected symbol type: (_Symbol_) ` Token~1~ Token~2~ ... Token~n~ `



Typed variable inside a concrete pattern: <_Type_ _Var_>



import ParseTree;
syntax Id = [a-z]+;
syntax Num = [0-9]+;
syntax Exp = left Exp "*" Exp > Exp "+" Exp |  Id | Num;
layout WS = [\ \n\r\t]*;

visit (parse(#Exp, "x + x")) {
   case (Exp) `<Id a> + <Id b>` => (Exp) `2 * <Id a>` when a == b
}



/ Pattern 



import IO;
data ColoredTree = leaf(int N)
                 | red(ColoredTree left, ColoredTree right) 
                 | black(ColoredTree left, ColoredTree right);
T = red(red(black(leaf(1), leaf(2)), black(leaf(3), leaf(4))), black(leaf(5), leaf(4)));



for(/black(_,leaf(4)) := T)
    println("Match!");



for(/black(_,leaf(int N)) := T)
    println("Match <N>");



for(/int N := T)
    println("Match <N>");



for(/int N := T)
    append N;



Var : Pat



import IO;
data ColoredTree = leaf(int N)
                 | red(ColoredTree left, ColoredTree right) 
                 | black(ColoredTree left, ColoredTree right);
T = red(red(black(leaf(1), leaf(2)), black(leaf(3), leaf(4))), black(leaf(5), leaf(4)));
for(/M:black(_,leaf(4)) := T)
    println("Match <M>");



[Pat, Pat, * Pat, Pat]
// [Pat~1~, Pat~2~, * Pat~3~, ..., Pat~n~]



import IO;



if([10, int N, 30, 40, 50] := [10, 20, 30, 40, 50])
   println("Match succeeded, N = <N>");



if([10, *L, 50] := [10, 20, 30, 40, 50])
   println("Match succeeded, L = <L>");



if([10, *int L, 50] := [10, 20, 30, 40, 50])
   println("Match succeeded, L = <L>");



if([10, *L, 40, *L, 50] := [10, 20, 30, 40, 20, 30, 50])
   println("Match succeeded, L = <L>");



for([*L1, int N, *L2, N, *L3] := [ 5, 10, 20, 30, 40, 30, 15, 20, 10])
    println("N = <N>");



for([*L1, *L2] := [10, 20, 30, 40, 50]) 
    println("<L1> and <L2>");



list[int] L;
if([10, L, 50] := [10, 20, 30, 40, 50])
   println("Match succeeded, L = <L>");



int N;
if([10, N, 30, 40, 50] := [10, 20, 30, 40, 50])
   println("Match succeeded, N = <N>");



"string"
123
1.0
|http://www.rascal-mpl.org|



123 := 123
"abc" := "abc"



123 := 456
"abc" := "def"



123 := "abc";



value x = "abc";
123 := x;
x = 123;
123 := x;



* Var

* Type Var



import IO;



if([10, *N, 50] := [10, 20, 30, 40, 50])
   println("Match succeeds, N == <N>");



if([10, *int N, 50] := [10, 20, 30, 40, 50])
   println("Match succeeds, N == <N>");



if({10, *S, 50} := {50, 40, 30, 30, 10})
   println("Match succeeds, S == <S>");



if({10, *int S, 50} := {50, 40, 30, 30, 10})
   println("Match succeeds, S == <S>");



Pat ( Pat, Pat)

Name (Pat, Pat)

// TODO:
// Pat ~1~ ( Pat~12~, ..., Pat~1n~, KeywordLabel~1~ = Pat~22~, ..., KeywordLabel~n~ = Pat~2n~)

// Name ( Pat~12~, ..., Pat~1n~, KeywordLabel~1~ = Pat~22~, ..., KeywordLabel~n~ = Pat~2n~)






import IO;
if("f"(A,13,B) := "f"("abc", 13, false))
   println("A = <A>, B = <B>");



data Color = red(int N) | black(int N);
if(red(K) := red(13))
   println("K = <K>");



/ RegularExpression /



/\brascal\b/i



/^.*?<word:\w+><rest:.*$>/m






/<x><n>/



/abc3/



/a{<n>}/



/<x:a{<n>}>/



/XX$/ := "lineoneXX\nlinetwo";
/XX$/m := "lineoneXX\nlinetwo";
/(?m)XX$/ := "lineoneXX\nlinetwo";



/XX/ := "some xx";
/XX/i := "some xx";
/(?i)XX/ := "some xx";



/a.c/ := "abc";
/a.c/ := "a\nc";
/a.c/s := "a\nc";
/(?s)a.c/ := "a\nc";



/a\/b/ := "a/b";
/a\+b/ := "a+b";



{Pat, Pat, * Pat,  Pat}
// {Pat~1~, Pat~2~, * Pat~3~, ..., Pat~n~}



import IO;



if({10, 30, 40, 50, int N} := {10, 20, 30, 40, 50})
   println("Match succeeded, N = <N>");



if({10, *S, 50} := {50, 40, 30, 20, 10})
   println("Match succeeded, S = <S>");



if({10, *int S, 50} := {50, 40, 30, 20, 10})
   println("Match succeeded, S = <S>");



for({*S1, *S2} :={30, 20, 10})
    println("<S1> and <S2>");



set[int] S;
if({10, *S, 50} := {10, 20, 30, 40, 50})
   println("Match succeeded, S = <S>");



int N;
if({10, N, 30, 40, 50} := {50, 40, 30, 20, 10})
   println("Match succeeded, N = <N>");



<Pat, Pat>
// <Pat~1~, ..., Pat~n~>



import IO;
if(<A, B, C> := <13, false, "abc">)
   println("A = <A>, B = <B>, C = <C>");



[Type] Pattern



import IO;



data Exp = val(value v) | add(Exp l, Exp r) | sub(Exp l, Exp r);
ex = add(add(val("hello"(1,2)),val("bye")), sub(val(1),val(2)));



visit (ex) {
  case [Exp] str name(_,_) : println("node name is <name>");
}



visit (ex) {
  case str name(_,_) : println("node name is <name>");
}



Type Var : Pattern



import IO;
data Lang = add(Lang l, Lang r) | number(int i);
data Exp = id(str n) | add(Exp l, Exp r) | subtract(Exp l, Exp r) | otherLang(Lang a);
ex = add(id("x"), add(id("y"), otherLang(add(number(1),number(2)))));
visit (ex) {
  case Lang l:add(_,_) : println("I found a Lang <l>");
  case Exp e:add(_,_)  : println("And I found an Exp <e>");
}



N = 10;



N := 10;
N := 20;



import IO;
if(M := 10)
   println("Match succeeded, M == <M>");



Type Var



str S := "abc";



S;



import IO;
if (str S := "abc")
   println("Match succeeds, S == \"<S>\"");



append Exp

append Label: Exp



for(int i <- [1..5]) 
  append i*i;
L = for(int i <- [1..5]) 
  append i*i;

OUTER:for (int i <-[1..5])
  for (int j <- [1..5])
    append OUTER: <i,j>;



assert Exp;

assert Exp : Exp;
// assert Exp~1~ : Exp~2~;



assert 1==2 : "is never true";
int div(int x, int y) {
  assert y != 0 : "y must be non-zero";
  return x / y;
}
div(4,0);



_Name_(_V_, _V_, _V_) = _Exp_;
// _Name_(_V_~1~, _V_~2~, ..., _V_~n~) = _Exp_;



data FREQ = wf(str word, int freq);
W = wf("rascal", 1000);
wf(S, I) = W;
S;
I;



data FREQ = wf(str word, int freq);
W = wf("rascal", 1000);
W.freq = 100000;



M = ("Andy": 1, "Brian" : 2);



M["SomebodyElse"] ? 0 += 1;
M["SomebodyElse"];



M["Andy"] ? 0 += 1;
M["Andy"]



<A, B, C> = <"abc", 2.5, [1,2,3]>;
A;
B;
C;



L = [0,1,2,3,4,5,6,7,8,9];
L[3..6] = [100,200,300,400,500];



L = [0,1,2,3,4,5,6,7,8,9];
L[1,3..8] = [100,200];



L = [0,1,2,3,4,5,6,7,8,9];
L[1,3..8] = [100,200,300,400,500];



S = "abcdefghij";
S[3..6] = "UVWXYZ";
S = "abcdefghij";
S[1,3..8] = "XY";
S = "abcdefghij";
S[1,3..8] = "UVWXYZ";



N = "f"(0,true,2,"abc",4,5.5,6,{7,77},8,{9,99,999});
N[3..6] = [100,200,300,400,500];



N = "f"(0,true,2,"abc",4,5.5,6,{7,77},8,{9,99,999});
N[1,3..8] = [100,200];



N = "f"(0,true,2,"abc",4,5.5,6,{7,77},8,{9,99,999});
N[1,3..8] = [100,200,300,400,500];






L = [10,20,30];
P = L;
L[1] = 200;



P;



M = ("abc": 1, "def" : 2);
M["def"] = 3;



T = <1, "abc", true>;
T[1] = "def";



N = 3;
N;



{ 
  Statement

  Statement
}
// { 
//   Statement~1~
//   ...
//   Statement~n~
// }



{1;2;3;}



{int x = 3; x*x;}



x;



break;

break Label;



import IO;
for(int i <- [1 .. 10]){
    if(i % 3 == 0){
       println("i = <i> is divisible by 3");
       break;
    }
}



continue;

continue Label;



import IO;
for (int i <- [1 .. 10]) {
    if (i % 3 == 0)
       continue;
    println("i = <i>");
}



do 
  Statement 
while (Exp);

do {
  Statements
} while (Exp);



import IO;
int n = 3;
do { println("n = <n>"); n -= 1; } while (n > 0);



n = 3;
do { append n * n; n -= 1; } while (n > 0);



fail;

fail Label;



import IO;
public list[int] sort(list[int] numbers){
  switch(numbers){
    case [*int nums1, int p, int q, *int nums2]:
       if(p > q){
          return sort(nums1 + [q, p] + nums2);
       } else {
       	  fail;
       }
     default: return numbers;
   }
}
sort([10, 1, 5, 3]);



filter;



for (Exp , Exp, Exp) 
  Statement

for (Exp , Exp,  Exp) {
  Statements
}

Label: for (Exp , Exp, Exp) 
  Statement

Label: for (Exp , Exp,  Exp) {
  Statements
}
// for (Exp~1~ , Exp~2~, ..., Exp~n~) 
//   Statement

// for (Exp~1~ , Exp~2~, ..., Exp~n~) {
//   Statements
// }

// Label: for (Exp~1~ , Exp~2~, ..., Exp~n~) 
//   Statement

// Label: for (Exp~1~ , Exp~2~, ..., Exp~n~) {
//   Statements
// }




import IO;
for(int n <- [1 .. 5])  
  println("n = <n>");
for(int n <- [1 .. 5]) 
  append n * n;



if (Exp)
  Statement

if (Exp) {
  Statements
}

if (Exp) 
  Statement 
else 
  Statement

if (Exp) {
  Statements
}
else {
  Statements
}
// if (Exp) 
//   Statement~1~ 
// else 
//   Statement~2~

// if (Exp) {
//   Statements~1~
// }
// else {
//   Statements~2~
// }



if (3 > 2) {
  30; 
} else {
  40;
}
x = if (3 > 2) {
  30; 
} else {
  40;
}
if (3 > 2) 
  30;



if( 2 > 3 ) 
  30;



import IO;
Label: if ([*_, 1, *_] := [1,2,1]) {
  println("yep"); 
  fail Label;
}



insert Exp;



data CTree = leaf(int n) | red(CTree left, CTree right) | green(CTree left, CTree right);
CTree T = red(green(leaf(1), red(leaf(2), leaf(3))), red(leaf(4), leaf(5)));



visit(T){
  case red(CTree l, CTree r): insert red(r,l);
}



visit(T){
  case red(CTree l, CTree r) => red(r,l)
}



return;

return Exp;



int twice(int n) { 
  return 2 * n; 
}
twice(5);



int twiceb(int n) = 2 * n;
twiceb(5);



list[int] even1(int n) {
  return for (i <- [0..n + 1], i % 2 == 0) {
    append i;
  };
}
even1(10)
// although that could be written easier using a comprehension
list[int] even2(int n) = [i | i <- [0..n+1], i %2 == 0];
even2(10);


solve(Var, Var, Var)
// TODO:
// solve(Var~1~, Var~2~, ..., Var~n~)
  Statement

solve(Var, Var, Var~n~; Exp)
// TODO:
// solve(Var~1~, Var~2~, ..., Var~n~; Exp)
  Statement

solve(Var, Var, Var) {
// TODO:
// solve(Var~1~, Var~2~, ..., Var~n~) {
  Statements
}

solve(Var, Var, Var; Exp) {
// TODO:
// solve(Var~1~, Var~2~, ..., Var~n~; Exp) {
  Statements
}



R+ = R + (R o R) + (R o R o R); 
// R+ = R + (R o R) + (R o R o R) + ...



rel[int,int] R = {<1,2>, <2,3>, <3,4>};
T = R;
solve (T) {
  T = T + (T o R);
}



switch ( _Exp_ ) {
// TODO:
// case _PatternWithAction~1~_;
// case _PatternWithAction~2~_;
// ...
// default: ...
}



import IO;
S = "Princess Leila sipped from her rum punch";
switch(S){
  case /Leila/: println("The topic is Star Wars");
  case /rum/:   println("The topic is Drunken man");
  case /punch/: println("The topic is Kick Boxing");
}



throw Exp;



str conc(str x, str y) { 
  if ("ball" in {x, y}) 
    throw "I hate balls"; 
  return x + y; 
}
conc("fairy", "tale");
conc("foot", "ball");



import List;
aList = [1,2,3];
if (size(aList) == 3) {
  throw size(aList);
}



import Exception;
// highlight-next-line
data RuntimeException = facUndefinedOn(int cause);
int fac(int n) {
  if (n < 0) {
    // highlight-next-line
    throw facUndefinedOn(n);
  }
  else if (n == 0) {
    return 1;
  }
  else {
    return n * fac(n - 1);
  }
}
fac(-1)



try
   Statement~1~
catch Pattern~1~ :
  Statement~2~
catch Pattern~2~ : {
  Statements
}
catch: 
  Statement~3~
finally Statement~4~
// TODO:
// finally: Statement~4~



import List;
import Exception;
int hd(list[int] x) { try return head(x); catch: return 0; }
hd([1,2,3]);
hd([]);



int hd2(list[int] x) { try return head(x); catch EmptyList(): return 0; }
hd2([]);



x = [[1],[2],[3]];
if (true) {
  // this visit is a nested statement in an if block:
  visit (x) {
    case int i => i + 1
  }
}



while (Exp)
  Statement

while (Exp) {
  Statements
}



import IO;
int n = 3;
while( n > 0 ) { 
  println("n = <n>"); n -= 1; 
}



n = 3;
while (n > 0) { 
  append n * n; n -= 1; 
}



[n * n | n <- [3 .. 0]];



test bool integerAdditionIsCommutative(int a, int b) { // <1>
    return a + b == b + a; // <2>
}

test bool integerMultiplicationIsCommutative(int a, int b)
    = a * b == b * a; // <3>



:test



//    TODO:
// result = edit(subject) {  
//    case “string” => “string”  
//    case “string” => “string”  
//    case /regex/  => regex  
// }



// result = edit(“aaa”) {  
//    case “a” => “b”  
// }



result = visit ("“aaa”") {  
        case "“a”" => "“b”"  
}
// TODO:
// result = visit (“aaa”) {  
//         case “a” => “b”  
// }


case error[Statement] s : println("dot came to: <s.prod.dot>");
case error[&T] _ : println("skipping an error tree");


// TODO:
// data Exp = … ; // an abstract data definition or any other type  
data Exp =  ; // an abstract data definition or any other type  
Exp javaExp(str x, loc l); // given this function which can parse a java expression string to an abstract data-type

(javaExp) `1 + 1` // a concrete Java expression which will be parsed by the javaExp function (at compile time)



int f(int i) = 2 * i + 1 when i % 2 == 0;
int f(int i) = 3 * i when i % 2 != 0;



int cc(ifThenElse(_, _, _)) = 1;
int cc(while(_, _)) = 1;
default int cc(statement _) = 0;



boolean mod2(int i) = true when i %% 2 == 0;
boolean mod3(int i) = true when i %% 3 == 0;
default  other(int i) = false; 

(f + g + other)(9) // will return true because mod3 matches



int f(0) = 1; // type is int(int)
str f([]) = "hello"; // type is str(list[void])
// TODO:
// str f([]) = "hello" // type is str(list[void])

data X = x(); // type is X()`
list[value] f(x(), 1) = 1; // type is list[value] (X, int)



int apply(int (int) func, int arg) = func(arg);
int f(0) = 1;

int example = apply(f, 0); // f is matched against `int (int)` to bind the parameter `func` of `apply`



value x = someExpressionProducingValues;
int f(int i) = 0;
f(x); 



bool subtype(T1 (T2), T3 (T4)) = subtype(T1, T3) && comparable(T2, T4);



int f(int _) = 0;
int f(real _) = 1;

int g(int _) = 0;
real g(real _) = 0.0;



int f(int i) = 0;
int g(real r) = 1;
int example = (f + g)(0);



int f(int i = 0) = i * 2;



// TODO:
module A;  
// import basic/Identifiers;
import basicIdentifiers;

module B;  
import A;

syntax Exp \= Id; // error undeclared non-terminal Id (before it would get the Id from basic/Identifiers via the transitive import of A).



module A

// TODO: \=
// data X \= x(); 

// int f(x()) \= 0;

module B;  
import A;

// X shadows the X from module A:  
// data X \= y(X x); // possible warning: X is not productive, there is no base case

// int f(y(x())) \= 1 // undeclared constructor x on local type `X`



// parallel analysis of all files in a project  
facts = fork (/loc f <- crawl(myProject)) {  
  append analyze(f);  
}  
    
// map-reduce over a tree  
int sum(int i) = i;  
int sum(node n) {  
  result = fork(child <- node) { // map  
    append sum(child);     
  }  
//   TODO: \+
//   return (0 | it \+ i | i <- result); // reduce  
}




data MyTree 
   = leaf(int n) 
   | tree(str name, MyTree left, MyTree right);



data Formula 
   = and(Formula l, Formula r)
   | or(Formula l, Formula r)
   | not(Formula n)
   | \true()
   | \false()
   ;



nil :             -> LIST
cons: ELEM x LIST -> LIST
head: LIST        -> ELEM
tail: LIST        -> LIST


// TODO:
// head(cons(e, l)) = e
// tail(cons(e, l)) = l
head(cons(e, l)) = e;
tail(cons(e, l)) = l;


// TODO:
// if(x > 10) { System.err.println("x > 10"); } else { System.err.println("x <= 10"); }
if(x > 10) { System.err.println("x \> 10"); } else { System.err.println("x \<= 10"); }



if(x > 10) { 
   System.err.println("x \> 10"); 
//    TODO:
//    System.err.println("x > 10"); 
} else { 
   System.err.println("x \<= 10"); 
//    TODO:
//    System.err.println("x <= 10"); 
}



if( x > 10 )
{ 
  System.err.println("x \> 10"); 
//   TODO:
//   System.err.println("x > 10"); 
} else 
{ 
   System.err.println("x \<= 10"); 
//    TODO:
//    System.err.println("x <= 10"); 
}



rel[str parent, str child] = {
<"Paul", "Eva">,
<"Paul", "Thomas">,
<"Jurgen", "Simon">,
<"Jurgen", "David">,
<"Tijs", "Mats">
};



rel[int position, str artist, str title, int year] Top2000 = {
<1, "Eagles", "Hotel California",1977>,
<2, "Queen", "Bohemian rhapsody", 1975>,
<3, "Boudewijn de Groot", "Avond", 1997>,
// ...
};



data ColoredTree = 
      leaf(int N) 
    | red(ColoredTree left, ColoredTree right) 
    | black(ColoredTree left, ColoredTree right);
ColoredTree CT = red(black(leaf(1), red(leaf(2),leaf(3))), black(leaf(3), leaf(4)));
import IO;
switch (CT){
case red(_, _):
     println("A red root node");
case black(_, _):
     println("A black root node");
}



{ x * x | int x <- [1 .. 10], x % 3 == 0 }



{name | /asgStat(Id name, _) <- P}



if(N <= 0)
     return 1; 
  else
     return N * fac(N - 1);



for(/asgStat(Id name, _) <- P, size(name) > 10){
    println(name);
}



data STAT = asgStat(Id name, EXP exp)
          | ifStat(EXP exp,list[STAT] thenpart,
                           list[STAT] elsepart) 
          | whileStat(EXP exp, list[STAT] body)
          ;



true;
101;
3.14;
"Rascal";
|file:///etc/passwd|;
$2101-09-05$;
[30, 20, 10];
<"Rascal", 100000>;
{"apples", "oranges", "bananas"};
{<"apples", 10, 15>, <"oranges", 5, 7>, <"bananas", 9, 11>};
("apples" : 100, "oranges": 150, "bananas": 75);
"abc"(1, 2, 3);



int x <- { 1, 3, 5, 7, 11 }
int x <- [ 1 .. 10 ]
/asgStat(Id name, _) <- P



int x <- {};



int x <- {1, 3, 5, 7, 11 };
x;



str x <- {1, 3, 5, 7, 11 };



{ x * x | int x <- {1, 3, 5, 7, 11 }};



import IO;
for(int x <- {1, 3, 5, 7, 11 })
    println("x = <x>");



int countAssignments(PROGRAM P){
    int n = 0;
    visit (P){
    case asgStat(_, _):
         n += 1;
    }
    return n;
}



int double(int x) { return 2 * x; }

int triple(int x) { return 3 * x; }

int f(int x, int (int) multi){ return multi(x); }



f(5, int (int y){return 3 * y;});



L = [1, 2, 3];
M = L;



L[0] = 10;



L;



M;



import String;
replaceAll("abracadabra", "a", "A");



S = "abracadabra";
T = S;
S = replaceAll("abracadabra", "a", "A");
S;
T;



/^<before:\W*><word:\w+><after:.*$>/



<_Name_:_RegularExpression_>



whileStat(EXP Exp, list[STAT] Stats)



whileStat(EXP Exp, Stats*)



whileStat(EXP Exp, _*)



Exp simp(add(con(n), con(m))) = con(n + m);   //<1>
Exp simp(mul(con(n), con(m))) = con(n * m);

Exp simp(mul(con(1), Exp e))  = e;
Exp simp(mul(Exp e, con(1)))  = e;
Exp simp(mul(con(0), Exp e))  = con(0);
Exp simp(mul(Exp e, con(0)))  = con(0);

Exp simp(add(con(0), Exp e))  = e;
Exp simp(add(Exp e, con(0)))  = e;

default Exp simp(Exp e)       = e;            // <2>

Exp simplify(Exp e){                          // <3>
  return bottom-up visit(e){
           case Exp e1 => simp(e1)
         }
}



// this is a single line comment above a variable declaration
int age = 42;



/* you should really never
 * int age = 42;
 * comment out any code :-)
 */
int yearOfBirth = 1977;



@synopsis{Describes a concept in a single line.}
@description{
    Explains to everyone what the concept is and how to use it
}
@examples{
    Contain (executable) code examples
}



int I = 3;



I = 3.5;



num N = 3;



N = 3.5;



value V = 3;
V = "abc";
V = false;



str classify(value V){
  switch(V){
    case str S: return "A string";
    case bool B: return "A Boolean";
    default: return "Another type"; 
  }
}
classify(V);
V = 3.5;
classify(V);



data Color = red(int level) | blue(int level);



Color C = red(3);



node ND = red(3);



lexical IntegerLiteral = [0-9]+; 

start syntax Exp        
  = IntegerLiteral      
  | bracket "(" Exp ")" 
  > left Exp "*" Exp    
  > left Exp "+" Exp    
  ;

layout Whitespace
    = [\ \t\n]*;



import ParseTree;
parse(#start[Exp], "2+3*4");
t = [Exp] "1+2*3";
import vis::Text;
import IO;
println(prettyTree(t))



import Set;
import Relation;
import analysis::graphs::Graph;



alias Proc = loc;



rel[Proc, Proc] calls = {<|proc:///a|, |proc:///b|>, <|proc:///b|, |proc:///c|>, <|proc:///b|, |proc:///d|>, <|proc:///d|, |proc:///c|>, 
                         <|proc:///d|, |proc:///e|>, <|proc:///f|, |proc:///e|>, <|proc:///f|, |proc:///g|>, <|proc:///g|, |proc:///e|>};
// let's first visualize the calls relation to get an overview:
import vis::Graphs;
graph(calls)



size(calls);



carrier(calls);



size(carrier(calls));



domain(calls);
range(calls);



top(calls);



bottom(calls);



closureCalls = calls+;



calledFromA = closureCalls[|proc:///a|];
calledFromF = closureCalls[|proc:///f|];



calledFromA & calledFromF;



(carrier(calls) | it & (calls+)[p] | p <- top(calls));



alias proc = loc;
alias comp = loc;

rel[comp,comp] lift(rel[proc,proc] aCalls, rel[proc,comp] aPartOf)
    = { <C1, C2> | <proc P1, proc P2> <- aCalls, 
	               <comp C1, comp C2> <- aPartOf[P1] * aPartOf[P2]};



calls = {<|proc:///main|, |proc:///a|>, <|proc:///main|, |proc:///b|>, <|proc:///a|, |proc:///b|>, <|proc:///a|, |proc:///c|>, <|proc:///a|, |proc:///d|>, <|proc:///b|, |proc:///d|>};        
partOf = {<|proc:///main|, |proc:///Appl|>, <|proc:///a|, |proc:///Appl|>, <|proc:///b|, |proc:///DB|>, <|proc:///c|, |proc:///Lib|>, <|proc:///d|, |proc:///Lib|>};

test bool tstLift() = 
    lift(calls, partOf) == { < |proc:///DB| , |proc:///Lib| > , < |proc:///Appl| , |proc:///Lib| > , 
                             < |proc:///Appl| , |proc:///DB| > , < |proc:///Appl| , |proc:///Appl| > };



calls = {<|proc:///main|, |proc:///a|>, <|proc:///main|, |proc:///b|>, <|proc:///a|, |proc:///b|>, <|proc:///a|, |proc:///c|>, <|proc:///a|, |proc:///d|>, <|proc:///b|, |proc:///d|>};        
partOf = {<|proc:///main|, |proc:///Appl|>, <|proc:///a|, |proc:///Appl|>, <|proc:///b|, |proc:///DB|>, <|proc:///c|, |proc:///Lib|>, <|proc:///d|, |proc:///Lib|>};



lifted=lift(calls, partOf);



import vis::Graphs;
graph(calls);
graph(lifted);



data ColoredTree = leaf(int N) // <1>
                 | red(ColoredTree left, ColoredTree right) 
                 | black(ColoredTree left, ColoredTree right);

ColoredTree rb = red(black(leaf(1), red(leaf(2),leaf(3))), black(leaf(3), leaf(4)));
          
int cntRed(ColoredTree t) {
   int c = 0;

   visit(t) {
     case red(_,_): c = c + 1; // <2>
   };

   return c;
}

test bool tstCntRed() = cntRed(rb) == 2;

@synopsis{Compute the sum of all integer leaves}
int addLeaves(ColoredTree t) {
   int c = 0;

   visit(t) {
     case leaf(int N): c = c + N; // <3>
   };

   return c;
}

test bool tstAddLeaves() = addLeaves(rb) == 13;

// Add green nodes to ColoredTree
data ColoredTree = green(ColoredTree left, ColoredTree right); // <4>

// Transform red nodes into green nodes
ColoredTree makeGreen(ColoredTree t) {
   return visit(t) {
     case red(l, r) => green(l, r) // <5>
   };
}

test bool tstMakeGreen() = makeGreen(rb) == green(black(leaf(1),green(leaf(2),leaf(3))),black(leaf(3),leaf(4)));



rb = red(black(leaf(1), red(leaf(2),leaf(3))), black(leaf(3), leaf(4)));



cntRed(rb);



addLeaves(rb);



makeGreen(rb);



import Node;
import Map;

data ColoredTree 
    = leaf(int N)      
    | red(ColoredTree left, ColoredTree right) 
    | black(ColoredTree left, ColoredTree right)
    ;
                 
ColoredTree CT = red(black(leaf(1), red(leaf(2),leaf(3))), black(leaf(3), leaf(4)));

data Suite 
    = hearts() 
    | diamonds() 
    | clubs() 
    | spades()
    ;

data Card 
    = two(Suite s) 
    | three(Suite s) 
    | four(Suite s) 
    | five(Suite s) 
    | six(Suite s) 
    | seven(Suite s) 
    | eight(Suite s) 
    | nine(Suite s) 
    | ten(Suite s) 
    | jack(Suite s) 
    | queen(Suite s) 
    | king(Suite s) 
    | ace(Suite s)
    ;
             
data Hand = hand(list[Card] cards);

Hand H = hand([two(hearts()), jack(diamonds()), six(hearts()), ace(spades())]);

// Count frequencies of constructors

map[str,int] count(node N) { // <1>
  freq = ();   // <2>

  visit(N) {   // <3>
    case node M: { 
      name = getName(M); // <4>
      freq[name] ? 0 += 1; 
    }
  }

  return freq; // <5>
}

map[str,int] countRelevant(node N, set[str] relevant) = domainR(count(N), relevant); // <6>

test bool tstCount() =  count(CT) == ("red":2, "leaf":5, "black":2);
test bool tstCountRelevant() = countRelevant(CT, {"leaf"}) == ("leaf" : 5);



count(CT);
count(H);
countRelevant(H, {"hearts", "spades"});



import vis::Charts;
import Relation;
barChart(["CT", "H"], toRel(count(CT)), toRel(count(H)))



data Exp = con(int n) // <1>
         | var(str name)
         | mul(Exp e1, Exp e2)
         | add(Exp e1, Exp e2)
         ;
         
public Exp E = add(mul(con(3), var("y")), mul(con(5), var("x"))); // <2>

Exp dd(con(n), var(V))              = con(0); // <3>
Exp dd(var(V1), var(V2))            = con((V1 == V2) ? 1 : 0);
Exp dd(add(Exp e1, Exp e2), var(V)) = add(dd(e1, var(V)), dd(e2, var(V)));
Exp dd(mul(Exp e1, Exp e2), var(V)) = add(mul(dd(e1, var(V)), e2), mul(e1, dd(e2, var(V))));
 
Exp simp(add(con(n), con(m))) = con(n + m); // <4>
Exp simp(mul(con(n), con(m))) = con(n * m);

Exp simp(mul(con(1), Exp e))  = e;
Exp simp(mul(Exp e, con(1)))  = e;
Exp simp(mul(con(0), Exp e))  = con(0);
Exp simp(mul(Exp e, con(0)))  = con(0);

Exp simp(add(con(0), Exp e))  = e;
Exp simp(add(Exp e, con(0)))  = e;

default Exp simp(Exp e)       = e; // <5>

Exp simplify(Exp e) = bottom-up visit(e){ // <6>
    case Exp e1 => simp(e1)
};


test bool tstSimplity1() = simplify(mul(var("x"), add(con(3), con(5)))) == mul(var("x"), con(8));
test bool tstSimplity2() = simplify(dd(E, var("x"))) == con(5);



dd(E, var("x"));



simplify(mul(var("x"), add(con(3), con(5))));



simplify(dd(E, var("x")));



import Relation;
import analysis::graphs::Graph;

rel[&T, set[&T]] dominators(rel[&T,&T] pred, &T root) {
	set[&T] vertices = carrier(pred);

	return  { <v, (vertices - {v, root}) - reachX(pred, {root}, {v})> |  &T v <- vertices};
}



rel[str,set[str]] example1() {
	str ROOT = "R";

	rel[str,str] PRED ={
		<"R", "A">,<"R", "B">, <"R", "C">,
		<"A", "D">,
		<"B", "A">, <"B", "D">, <"B", "E">,
		<"C", "F">, <"C", "G">,
		<"D", "L">,
		<"E", "H">,
		<"F", "I">,
		<"G", "I">, <"G", "J">,
		<"H", "K">, <"H", "E">,
		<"I", "K">, 
		<"K", "I">, <"K", "R">,
		<"L", "H">
	};

	return dominators(PRED, ROOT);
}

test bool t1() =
  example1() ==
 	{
		<"R", {"A", "B", "C", "D", "E", "F", "G", "L", "H", "I", "J", "K"}>, 
		<"A", {}>, 
		<"B", {}>, 
		<"C", {"F", "G", "J"}>, 
		<"D", {"L"}>, 
		<"E", {}>, 
		<"F", {}>, 
		<"G", {"J"}>, 
		<"L", {}>, 
		<"H", {}>, 
		<"I", {}>, 
		<"J", {}>, 
		<"K", {}>
	};



rel[int,set[int]] example2() {
	int ROOT = 1;

	rel[int,int] PRED = {
		<1,2>, <1,3>,
		<2,3>,
		<3,4>,
		<4,3>,<4,5>, <4,6>,
		<5,7>,
		<6,7>,
		<7,4>,<7,8>,
		<8,9>,<8,10>,<8,3>,
		<9,1>,
		<10,7>
	};

	return dominators(PRED, ROOT);
}

test bool t2() =
  example2() ==
	{
		<1, {2, 3, 4, 5, 6, 7, 8, 9, 10}>, 
		<2, {}>,
		<3, {4, 5, 6, 7, 8, 9, 10}>,
		<4, {5, 6, 7, 8, 9, 10}>, 
		<5, {}>,
		<6, {}>,
		<7, {8, 9, 10}>,
		<8, {9, 10}>,
		<9, {}>,
		<10, {}>
	};



import analysis::graphs::Graph;
import Set;
import Relation;

int cyclomaticComplexity(Graph[&T] CFG){
    return size(CFG) - size(carrier(CFG)) + 2;
}



Graph[int] G1 = {<1,2>, <2,3>};
Graph[int] G3 = {<1,2>, <1,3>, <2,6>, <3,4>, <3,5>, <4,7>, <5,8>, <6,7>, <7,8>};
Graph[int] G5 = {<1,2>, <2,3>, <2,4>, <3,6>, <4,2>, <4,5>, <5, 10>, <6, 7>, 
                 <7, 8>, <7,9>, <8,9>, <9, 7>, <9,10>};

test bool tstCyclomaticComplexity1() = cyclomaticComplexity(G1) == 1;
test bool tstCyclomaticComplexity2() = cyclomaticComplexity(G3) == 3;
test bool tstCyclomaticComplexity3() = cyclomaticComplexity(G5) == 5;



:test



import Relation;
import analysis::graphs::Graph;

alias Stat = int;
alias Var = str;
alias Def  = tuple[Stat, Var];
alias Use = tuple[Stat, Var];



rel[Stat, Def] definition(rel[Stat, Var] defs)
	= {<s, <s, v>> | <Stat s, Var v> <- defs};

rel[Stat, Def] use(rel[Stat, Var] uses)
	= {<s, <s, v>> | <Stat s, Var v> <- uses};

rel[Stat, Def] kill(rel[Stat, Var] defs) { 
	return {<s1, <s2, v>> | <Stat s1, Var v> <- defs, <Stat s2, v> <- defs, s1 != s2};
}



rel[Stat, Def] reachingDefinitions(rel[Stat, Var] defs, rel[Stat, Stat] pred) {
	set[Stat] statement = carrier(pred);
	rel[Stat, Def] def  = definition(defs);
	rel[Stat, Def] kill = kill(defs);

	// The set of mutually recursive dataflow equations that has to be solved:

	rel[Stat, Def] \in = {};
	rel[Stat, Def] out = def;
	
	solve (\in, out) {
       \in =  {<s, d> | int s <- statement, Stat p <- predecessors(pred, s), Def d <- out[p]};
       out = {<s, d> | int s <- statement, Def d <- def[s] + (\in[s] - kill[s])};
	};

	return \in;
}



PRED = { <1,2>, <2,3>, <3,4>, <4,5>, <5,6>, <5,7>, <6,7>, <7,4>};
DEFS = { <1, "i">, <2, "j">, <3, "a">, <4, "i">, <5, "j">, <6, "a">, <7, "i">};
// let's test the `kill` function:
assert kill(DEFS) ==  {<1, <4, "i">>, <1, <7, "i">>, <2, <5, "j">>, <3, <6, "a">>, 
                       <4, <1, "i">>, <4, <7, "i">>, <5, <2, "j">>, <6, <3, "a">>, 
                       <7, <1, "i">>, <7, <4, "i">>};
// and what we expect from `reachingDefinitions` according to the Dragon book:
RES = reachingDefinitions(DEFS, PRED);
assert RES == {<2, <1, "i">>, <3, <2, "j">>, <3, <1, "i">>, <4, <3, "a">>, 
               <4, <2, "j">>, <4, <1, "i">>, <4, <7, "i">>, <4, <5, "j">>, 
               <4, <6, "a">>, <5, <4, "i">>, <5, <3, "a">>, <5, <2, "j">>, 
               <5, <5, "j">>, <5, <6, "a">>, <6, <5, "j">>, <6, <4, "i">>, 
               <6, <3, "a">>, <6, <6, "a">>, <7, <5, "j">>, <7, <4, "i">>, 
               <7, <3, "a">>, <7, <6, "a">>};



rel[Stat, Def] liveVariables(rel[Stat, Var] defs, rel[Stat, Var] uses, rel[Stat, Stat] pred) {
	set[Stat] statement = carrier(pred);
	rel[Stat, Def] def  = definition(defs);
	rel[Stat, Def] use = use(uses);
	
    rel[Stat, Def] lin = {};
	rel[Stat, Def] lout = def;
 	
 	solve (lin, lout) {
		lin  =  {<s, d> | Stat s <- statement,  Def d <- use[s] + (lout[s] - (def[s]))};
		lout =  {<s, d> | Stat s <- statement,  Stat succ <- successors(pred, s), Def d <- lin[succ] };
	}
	return lin;
}



ROOT = 1;
PRED= { <1,2>, <2,3>, <3,4>, <4,5>, <5,6>,<5,7>,<6,7>,<7,4>};
DEFS= { <"i",1>,<"j",2>,<"a",3>,<"i",4>,<"j",5>,<"a",6>,<"i",7>}<1,0>;
USES= {<"m",1>,<"n",2>,<"u1",3>,<"i",4>,<"j",5>,<"u2",6>,<"u3",7>}<1,0>;



assert liveVariables(DEFS, USES, PRED) ==
	 	      {<1, <6, "u2">>, <1, <7, "u3">>, <1, <5, "j">>, <1, <4, "i">>,
		       <1, <3, "u1">>, <1, <2, "n">>, <1, <1, "m">>, 
		       <2, <7, "u3">>, <2, <6, "u2">>, <2, <5, "j">>, <2, <4, "i">>, 
		       <2, <3, "u1">>, <2, <2, "n">>, 
		       <3, <7, "u3">>, <3, <6, "u2">>, <3, <5, "j">>, <3, <4, "i">>, 
		       <3, <3, "u1">>, 
		       <5, <4, "i">>, <5, <7, "u3">>, <5, <6, "u2">>, <5, <5, "j">>, 
		       <6, <5, "j">>, <6, <4, "i">>, <6, <7, "u3">>, <6, <6, "u2">>, 
		       <7, <6, "u2">>, <7, <5, "j">>, <7, <4, "i">>, <7, <7, "u3">>, 
		       <4, <7, "u3">>, <4, <6, "u2">>, <4, <5, "j">>, <4, <4, "i">>};



import Relation;
import analysis::graphs::Graph;
alias Stat = int;
alias Var  = str;
alias Def  = tuple[Stat, Var];
alias Use  = tuple[Stat, Var];
rel[Stat, Def] definition(rel[Stat, Var] defs) = {<s, <s, v>> | <Stat s, Var v> <- defs};
rel[Stat, Def] use(rel[Stat, Var] uses) = {<s, <s, v>> | <Stat s, Var v> <- uses};
rel[Stat, Def] kill(rel[Stat, Var] defs) { 
	return {<s1, <s2, v>> | <Stat s1, Var v> <- defs, <Stat s2, v> <- defs, s1 != s2};
}
rel[Stat, Def] reachingDefinitions(rel[Stat, Var] defs, rel[Stat, Stat] pred) {
	set[Stat] statement = carrier(pred);
	rel[Stat, Def] def  = definition(defs);
	rel[Stat, Def] kill = kill(defs);
	rel[Stat, Def] \in = {};
	rel[Stat, Def] out = def;
	solve (\in, out) {
       \in =  {<s, d> | int s <- statement, Stat p <- predecessors(pred, s), Def d <- out[p]};
       out = {<s, d> | int s <- statement, Def d <- def[s] + (\in[s] - kill[s])};
	};
	return \in;
}
rel[&T, set[&T]] dominators(rel[&T,&T] pred, &T root) {
	set[&T] vertices = carrier(pred);
	return  { <v, (vertices - {v, root}) - reachX(pred, {root}, {v})> |  &T v <- vertices};
}



set[Use] BackwardSlice(
	set[Stat] controlstatement, 
	rel[Stat, Stat] pred,
	rel[Stat, Var] uses,
	rel[Stat, Var] defs,	
	Use criterion) {

	rel[Stat, Def] reach = reachingDefinitions(defs, pred);

	// Compute the relation between each use and corresponding definitions: ud
	rel[Use, Def] useDef = 
 	 {<<s1, v>, <s2, v>> | <Stat s1, Var v> <- uses, <Stat s2, v> <- reach[s1]};

	// Internal dependencies per statement
	rel[Def, Use] defUsePerStat 
        = {<<s, v1>, <s, v2>> | <Stat s, Var v1> <- defs, <s, Var v2> <- uses}
        + {<<s, v>, <s, "EXEC">> | <Stat s, Var v> <- defs}
        + {<<s, "TEST">, <s,v>> | Stat s <- controlstatement, <s, Var v> <- domainR(uses, {s})};

	// Control dependence: control-dependence
	rel[Stat, set[Stat]] controldominator = domainR(dominators(pred, 1), controlstatement);

	rel[Def, Use] controlDependence  =
	   {<<s2, "EXEC">, <s1,"TEST">> | <Stat s1, set[Stat] s2s> <- controldominator, Stat s2 <- s2s};

	// Control and data dependence: use-control-def
	rel[Use, Def] useControlDef = useDef + controlDependence;
	rel[Use, Use] useUse = (useControlDef o defUsePerStat)*;

	return useUse[criterion];
}



PRED = {<1,2>, <2,3>, <3,4>, <4,5>, <5,6>, <5,9>, <6,7>, <7,8>,<8,5>, <8,9>, <9,10>};
DEFS = {<1, "n">, <2, "i">, <3, "sum">, <4,"product">, <6, "sum">, <7, "product">, <8, "i">};
USES = {<5, "i">, <5, "n">, <6, "sum">, <6,"i">, <7, "product">, <7, "i">, <8, "i">, <9, "sum">, <10, "product">};
CONTROLSTATEMENT = { 5 };



Example1 = BackwardSlice(CONTROLSTATEMENT, PRED, USES, DEFS, <9, "sum">);
assert Example1 == { <1, "EXEC">, <2, "EXEC">,  <3, "EXEC">, <5, "i">, <5, "n">,  <6, "sum">, <6, "i">, <6, "EXEC">, <8, "i">, <8, "EXEC">, <9, "sum"> };
Example2 = BackwardSlice(CONTROLSTATEMENT, PRED, USES, DEFS,<10, "product">);
assert Example2 == { <1, "EXEC">,  <2, "EXEC">, <4, "EXEC">, <5, "i">, <5, "n">, <7, "i">, <7, "product">, <7, "EXEC">, <8, "i">, <8, "EXEC">, <10,  "product">  };



import String;
import List;

str capitalize(str s) = "<toUpperCase(s[0])><s[1..]>";
  
private str genSetter(map[str,str] fields, str x) 
    = "public void set<capitalize(x)>(<fields[x]> <x>) {
      '  this.<x> = <x>;
      '}";

private str genGetter(map[str,str] fields, str x) 
    = "public <fields[x]> get<capitalize(x)>() {
      '  return <x>;
      '}";

str genClass(str name, map[str,str] fields) // <2>
    = "public class <name> {
      '  <for (x <- sort([f | f <- fields])) {>
      '  private <fields[x]> <x>;
      '  <genSetter(fields, x)>
      '  <genGetter(fields, x)><}>
      '}";

map[str, str] fields = (
     "name" : "String",
     "age" : "Integer",
     "address" : "String"
  );
  
str cperson = 
  // Do not change a single space in the string below! (for testing purposes)
  "public class Person {
  '  
  '  private String address;
  '  public void setAddress(String address) {
  '    this.address = address;
  '  }
  '  public String getAddress() {
  '    return address;
  '  }
  '  private Integer age;
  '  public void setAge(Integer age) {
  '    this.age = age;
  '  }
  '  public Integer getAge() {
  '    return age;
  '  }
  '  private String name;
  '  public void setName(String name) {
  '    this.name = name;
  '  }
  '  public String getName() {
  '    return name;
  '  }
  '}";

test bool tstGenClass() = genClass("Person", fields) == cperson;



import IO;
fields = (
     "name" : "String",
     "age" : "Integer",
     "address" : "String"
  );
println(genClass("Person", fields));



import Relation;
import analysis::graphs::Graph;



alias Expr = int;
alias Varname = str;



Expr root = 1;



Graph[Expr] pred = {<1,3>, <3,4>, <4,5>, <5,6>, <5,8>, <6,10>, <8,10>};
import vis::Graphs;
graph(pred);



rel[Varname,Expr] defs = {<"x", 3>, <"p", 4>, <"z", 6>, <"x", 8>, <"y", 10>};
rel[Varname, Expr] uses =  {<"q", 5>, <"y", 6>, <"x", 6>, <"z", 10>};



rel[Varname, Expr] uninit(rel[Varname,Expr] defs, rel[Varname, Expr] uses, Graph[Expr] pred) =
   { <v, e> | <Varname v, Expr e> <- uses,
              e in reachX(pred, {root}, defs[v])
   };



UNINIT = uninit(defs, uses, pred);
assert UNINIT == {<"q", 5>, <"y", 6>, <"z", 10>};



UNUSED = domain(defs) - domain(uses);
assert UNUSED == {"p"};
assert UNUSED & UNINIT<0> == {}; // empty intersection



import String;
import List;

int countInLine1(str s) {
  int count = 0;
  for (/[a-zA-Z0-9_]+/ := s) {
    count += 1;
  }
  return count;
}

test bool tstCountInLine1a() = countInLine1("") == 0;
test bool tstCountInLine1b() = countInLine1("Jabberwocky by Lewis Carroll") == 4;

int countInLine2(str S) {
  int count = 0;

  // \w matches any word character
  // \W matches any non-word character
  // <...> are groups and should appear at the top level.
  while (/^\W*\w+<rest:.*$>/ := S) {
    count += 1;
    S = rest;
  }
  return count;
}

test bool tstCountInLine2a() = countInLine2("") == 0;

// this is the simplest solution:
int countInLine3(str s) = (0 | it + 1 | /\w+/ := s);

test bool tstCountInLine3a() = countInLine3("") == 0;
test bool tstCountInLine3b() = countInLine3("Jabberwocky by Lewis Carroll") == 4;

public list[str] Jabberwocky = [
	"Jabberwocky by Lewis Carroll",
	"",
	"\'Twas brillig, and the slithy toves",
	"Did gyre and gimble in the wabe;",
	"All mimsy were the borogoves,",
	"And the mome raths outgrabe.",
	"",
	"\"Beware the Jabberwock, my son!",
	"The jaws that bite, the claws that catch!",
	"Beware the Jubjub bird, and shun",
	"The frumious Bandersnatch!\"",
	"",
	"\'Twas brillig, and the slithy toves",
	"Did gyre and gimble in the wabe;",
	"All mimsy were the borogoves,",
	"And the mome raths outgrabe.",
	"",
	"\"Beware the Jabberwock, my son!",
	"The jaws that bite, the claws that catch!",
	"Beware the Jubjub bird, and shun",
	"The frumious Bandersnatch!\"",
	"",
	"He took his vorpal sword in hand:",
	"Long time the manxome foe he sought.",
	"So rested he by the Tumtum tree,",
	"And stood awhile in thought.",
	"",
	"And as in uffish thought he stood,",
	"The Jabberwock, with eyes of flame,",
	"Came whiffling through the tulgey wood",
	"And burbled as it came!",
	"",
	"One, two! One, two! and through and through",
	"The vorpal blade went snicker-snack!",
	"He left it dead, and with its head",
	"He went galumphing back.",
	"",
	"\"And hast thou slain the Jabberwock?",
	"Come to my arms, my beamish boy!",
	"O frabjous day! Callooh! Callay!",
	"He chortled in his joy.",
	"",
	"\'Twas brillig, and the slithy toves",
	"Did gyre and gimble in the wabe;",
	"All mimsy were the borogoves,",
	"And the mome raths outgrabe."
];


int wordCount(list[str] input, int (str s) countInLine) {
  count = 0;
  for (str line <- input){ // <1>
     count += countInLine(line); // <2>
  }
  return count;
}

int wordCountReduce(list[str] input, int (str s) countInline)
  = (0 | it + countInline(line) | str line <- input);

int wordCountMapSum(list[str] input, int (str s) countInLine)
  = sum(mapper(input, countInLine));


test bool tstWordCount1() = wordCount(Jabberwocky, countInLine1) == wordCount(Jabberwocky, countInLine2);
test bool tstWordCount2() = wordCount(Jabberwocky, countInLine1) == wordCount(Jabberwocky, countInLine3);
test bool tstWordCount3() = wordCount(Jabberwocky, countInLine2) == wordCount(Jabberwocky, countInLine3);

test bool tstWordCount4(str txt) {
    lines = split(txt, "\n");
    return wordCount(lines, countInLine1) == wordCount(lines, countInLine2);
}    
    
test bool tstWordCount5(str txt) {
    lines = split(txt, "\n"); 
    return wordCount(lines, countInLine1) == wordCount(lines, countInLine3); 
}

test bool tstWordCount6(str txt) {
    lines = split(txt, "\n");  
    return wordCount(lines, countInLine2) == wordCount(lines, countInLine3);
}



wordCount(Jabberwocky, countInLine1);
wordCount(Jabberwocky, countInLine2);
wordCount(Jabberwocky, countInLine3);



int wordCount2(list[str] lines) = (0 | it + (0 | it + 1 | /\w+/ := line) | str line <- lines);
wordCount2(Jabberwocky);



int wordCount3(list[str] lines) = (0 | it + 1 | line <- lines, /\w+/ := line);
wordCount3(Jabberwocky);



import String;

str capitalize(str word:/^<letter:[a-z]><rest:.*>/) 
  = "<toUpperCase(letter)><rest>";

default str capitalize(str word) = word;

test bool capitalize1() = capitalize("1") == "1";
test bool capitalize2() = capitalize("rascal") == "Rascal";

@synopsis{Version 1: capAll1: using a while loop}
str capAll1(str S) // <2>
{
 result = "";
 while (/^<before:\W*><word:\w+><after:.*$>/ := S) { 
    result = result + before + capitalize(word);
    S = after;
  }
  return result;
}

test bool tstCapAll1() =  capAll1("turn this into a title") == "Turn This Into A Title";

@synopsis{Version 2: capAll2: using visit}
str capAll2(str S) // <3>
{
   return visit(S){
   	case /^<word:\w+>/i => capitalize(word)
   };
}

test bool tstCapAll2() = capAll2("turn this into a title") == "Turn This Into A Title";



capitalize("rascal");
capAll1("turn this into a capitalized title")
capAll2("turn this into a capitalized title")



data Exp 
    = con(int n)          // <1>
    | mul(Exp e1, Exp e2) // <2>
    | add(Exp e1, Exp e2) // <3>
    ;



int eval(con(int n)) = n;                            // <1>
int eval(mul(Exp e1, Exp e2)) = eval(e1) * eval(e2); // <2>
int eval(add(Exp e1, Exp e2)) = eval(e1) + eval(e2); // <3>

test bool tstEval1() = eval(con(7)) == 7;
test bool tstEval2() = eval(mul(con(7), con(3))) == 21;
test bool tstEval3() = eval(add(con(7), con(3))) == 10;
test bool tstEval4() = eval(add(con(3), mul(con(4), con(5)))) == 23;



eval(mul(con(7), con(3)));
eval(add(con(3), mul(con(4), con(5))));



layout Whitespace = [\t-\n\r\ ]*;                    

lexical IntegerLiteral = [0-9]+;           

start syntax Exp 
    = con: IntegerLiteral   // <1>
    | bracket "(" Exp ")"     
    > left mul: Exp "*" Exp // <2>  
    > left add: Exp "+" Exp // <3>   
    ;



import ParseTree;

Tree parseExp(str txt) = parse(#Exp, txt); 



example = parseExp("2+3*4");



data Exp  // <2>
    = con(int n)                 
    | mul(Exp e1, Exp e2)        
    | add(Exp e1, Exp e2)        
    ;

import ParseTree; // <3>

Exp load(Tree t) = implode(#Exp, t); 



example2 = load(example);



int eval(con(int n)) = n;                            
int eval(mul(Exp e1, Exp e2)) = eval(e1) * eval(e2); 
int eval(add(Exp e1, Exp e2)) = eval(e1) + eval(e2); 



eval(example2);



layout Whitespace = [\t-\n\r\ ]*;
    
lexical IntegerLiteral = [0-9]+;           

start syntax Exp 
  = IntegerLiteral          
  | bracket "(" Exp ")"     
  > left Exp "*" Exp        
  > left Exp "+" Exp        
  ;



import ParseTree;

Exp parseExp(str txt) = parse(#Exp, txt); 



example = parseExp("2+3");



data Exp 
    = con(int n)               
    | mul(Exp e1, Exp e2)        
    | add(Exp e1, Exp e2)        
    ;



import String;

Exp load((Exp)`<IntegerLiteral l>`)  = con(toInt("<l>"));        // <4>
Exp load((Exp)`<Exp e1> * <Exp e2>`) = mul(load(e1), load(e2));  
Exp load((Exp)`<Exp e1> + <Exp e2>`) = add(load(e1), load(e2)); 
Exp load((Exp)`( <Exp e> )`)         = load(e);                    



load(example);



int eval(con(int n)) = n;                            
int eval(mul(Exp e1, Exp e2)) = eval(e1) * eval(e2); 
int eval(add(Exp e1, Exp e2)) = eval(e1) + eval(e2); 



eval(load(example));



lexical IntegerLiteral = [0-9]+; // <1>

start syntax Exp        // <2>
  = IntegerLiteral      // <3>
  | bracket "(" Exp ")" // <4>
  > left Exp "*" Exp    // <5>
  > left Exp "+" Exp    // <6>
  ;



import String;
import ParseTree; // <1>

int eval(str txt) = eval(parse(#Exp, txt)); // <2>

int eval((Exp)`<IntegerLiteral l>`) = toInt("<l>");       // <3>
int eval((Exp)`<Exp e1>*<Exp e2>`) = eval(e1) * eval(e2); // <4>
int eval((Exp)`<Exp e1>+<Exp e2>`) = eval(e1) + eval(e2); // <5>
int eval((Exp)`(<Exp e>)`) = eval(e);                     // <6>

test bool tstEval1() = eval("7") == 7;
test bool tstEval2() = eval("7*3") == 21;
test bool tstEval3() = eval("7+3") == 10;
test bool tstEval4() = eval("3+4*5") == 23;



parse(#Exp, "2+3");



eval("2+3");
eval("2+3*4");
eval("(2+3)*4");



layout Whitespace = [\t-\n\r\ ]*; // <1>
    
lexical IntegerLiteral = [0-9]+;           

start syntax Exp 
  = IntegerLiteral          
  | bracket "(" Exp ")"     
  > left Exp "*" Exp        
  > left Exp "+" Exp        
  ;



import String;
import ParseTree;                                                   

int eval(str txt) = eval(parse(#start[Exp], txt).top);              

int eval((Exp)`<IntegerLiteral l>`) = toInt("<l>");       
int eval((Exp)`<Exp e1> * <Exp e2>`) = eval(e1) * eval(e2);  
int eval((Exp)`<Exp e1> + <Exp e2>`) = eval(e1) + eval(e2); 
int eval((Exp)`( <Exp e> )`) = eval(e);                    

value main() {
  return eval(" 2+3");
}

test bool tstEval1() = eval(" 7") == 7;
test bool tstEval2() = eval("7 * 3") == 21;
test bool tstEval3() = eval("7 + 3") == 10;
test bool tstEval4() = eval(" 3 + 4*5 ") == 23;



syntax Exp 
  = IntegerLiteral          
  | bracket "(" Whitespace Exp Whitespace ")"     
  > left Exp Whitespace "*" Whitespace Exp        
  > left Exp Whitespace "+" Whitespace Exp        
  ;

syntax start[Exp] = Whitespace Exp top Whitespace;



eval("2 +  3");
eval("2   +  3*4");
eval("( 2+3 )* 4");



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|))



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F1.func|))



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F2.func|))



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F3.func|))



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.rsc|))



demo::lang::Func::AST



demo::lang::Func::Func



demo::lang::Func::Eval0



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|))



import demo::lang::Func::Load;
import demo::lang::Func::Eval0;
import demo::lang::Func::programs::F0;
eval0("fact", [10], load(F0));



demo::lang::Func::Eval1



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F1.func|))



import demo::lang::Func::Load;
import demo::lang::Func::Eval1;
import demo::lang::Func::programs::F1;
eval1("fact", [10], load(F1));



demo::lang::Func::Eval2



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F2.func|))



import demo::lang::Func::Load;
import demo::lang::Func::Eval2;
import demo::lang::Func::programs::F2;
eval2("fact", [10], load(F2));



demo::lang::Func::Eval3



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F3.func|))



import demo::lang::Func::Load;
import demo::lang::Func::Eval3;
import demo::lang::Func::programs::F3;
eval3("fact", [10], load(F3));



demo::lang::Func::Load



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|))



import demo::lang::Func::Load;
import demo::lang::Func::programs::F0;
load(F0);



load(|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|);



demo::lang::Func::Parse



((|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|))



import demo::lang::Func::Parse;
import demo::lang::Func::programs::F0;
parse(F0);



parse(|project://rascal-website/courses/Recipes/demo/lang/Func/programs/F0.func|);



demo::lang::Lisra::Eval



import demo::lang::Lisra::Runtime;
import demo::lang::Lisra::Eval;
eval(Integer(5));
eval(Atom("x"));
eval(List([Atom("+"), Integer(5), Integer(7)]));



demo::lang::Lisra::Parse



(LispExp)`<IntegerLiteral il>`



(LispExp)`( <LispExp* lst> )`



import demo::lang::Lisra::Parse;
import demo::lang::Lisra::Runtime;
parse("1");
parse("x");
parse("(+ 5 7)");



demo::lang::Lisra::Pretty



Lval parse(str txt);
str pretty(Lval x);



parse(pretty(L)) == L



import demo::lang::Lisra::Runtime;
import demo::lang::Lisra::Pretty;
pretty(Integer(42));
pretty(Atom("x"));
L = List([Atom("+"), Integer(5), Integer(7)]);
pretty(L);



import demo::lang::Lisra::Parse;
parse(pretty(L)) == L;



demo::lang::Lisra::Runtime



demo::lang::Lisra::Syntax



demo::lang::Lisra::Test



lexical Id = [a-z]+;
lexical Num = [0-9]+;

syntax Exp
    = Id
    | Num
    | bracket "(" Exp ")" // <1>
    > right Exp "^" Exp   // <2>
    > left ( Exp "*" Exp  // <3>
           | Exp "/" Exp  // <4>
           )
    > left ( Exp "+" Exp  // <5>
           | Exp "-" Exp  // <6>
           )
    ;



Exp brackets(Exp e) = visit(e) {
case Exp f => (Exp) `(<Exp f>)` 
  when (Exp) `(<Exp _>)` !:= f, (Exp) `<Id i>` !:= f, (Exp) `<Num n>` !:= f
};



import IO;
for (input <- ["a+b*c", "a^b*c+d", "(a^b+1)^d+1"]) {
  t = parse(#Exp, input);
  println("<t> - <brackets(t)>");
}



import vis::Text;
for (input <- ["a+b*c", "a^b*c+d", "(a^b+1)^d+1"]) {
  t = parse(#Exp, input);
  println(prettyTree(t));
}



// // highlight-next-line
// begin declare input : natural, 
//               output : natural,           
//               repnr : natural,
//               rep : natural;
//       input := 14;
//       output := 1;
// // highlight-next-line
//       while input - 1 do 
//           rep := output;
//           repnr := input;
//           while repnr - 1 do
//              output := output + rep;
//              repnr := repnr - 1
//           od;
//           input := input - 1
//       od
// end



demo::lang::Pico::Abstract



demo::lang::Pico::Assembly



demo::lang::Pico::Compile



import demo::lang::Pico::Compile;
compileProgram("begin declare x : natural; x := 47 end");



compileProgram("begin declare input : natural,  
               '              output : natural,           
               '             repnr : natural,
               '              rep : natural;
               '      input := 14;
               '      output := 1;
               '      while input - 1 do        
               '          rep := output;
               '          repnr := input;
               '          while repnr - 1 do
               '             output := output + rep;
               '             repnr := repnr - 1
               '          od;
               '          input := input - 1
               '      od
               'end");



demo::lang::Pico::ControlFlow



import demo::lang::Pico::ControlFlow;
cflowProgram("begin declare n : natural, s : string; n := 10; s := \"a\"; while n do s := s + \"a\"; n := n - 1 od end");



demo::lang::Pico::Eval



import demo::lang::Pico::Eval;
evalProgram("begin declare x : natural, y : natural; x := 1; y := x + 5 end");



demo::lang::Pico::Load



import demo::lang::Pico::Load;
load("begin declare x : natural; x := 3 end");



demo::lang::Pico::Syntax



demo::lang::Pico::Typecheck



import demo::lang::Pico::Typecheck;
checkProgram("begin declare  x : natural; x := \"abc\" end");



demo::lang::Pico::Uninit



import demo::lang::Pico::Uninit;
uninitProgram("begin declare n : natural, m : natural, p : natural; n := 10; m := n + p end");



demo::lang::Pico::UseDef



import IO;
if ({l} := findResources("Metrics/MeasuringJava/snakes-and-ladders-project-source.zip")) {
   copy(l[scheme="zip+<l.scheme>"][path="<l.path>!/"], |tmp:///snakes-and-ladders|, recursive=true);
} else {
   throw "failed to copy necessary source code to analyze for this example";
}



import lang::java::m3::Core;
import lang::java::m3::AST;



|tmp:///snakes-and-ladders/src/snakes/|.ls



myModel = createM3FromDirectory(|tmp:///snakes-and-ladders/src|);



import util::Reflective;
cp = getProjectPathConfig(|tmp:///snakes-and-ladders|).javaCompilerPath;



myModel = createM3FromDirectory(|tmp:///snakes-and-ladders/src|, classPath=cp);



import IO;
if ({l} := findResources("Metrics/MeasuringJava/snakes-and-ladders-project-source.zip")) {
   copy(l[scheme="zip+<l.scheme>"][path="<l.path>!/"], |tmp:///snakes-and-ladders|, recursive=true);
} else {
   throw "failed to copy necessary source code to analyze for this example";
}



import lang::java::m3::Core;
import lang::java::m3::AST;



|tmp:///snakes-and-ladders/src/snakes/|.ls



myModel = createM3FromDirectory(|tmp:///snakes-and-ladders/src|);



myModel.containment



import IO;
println(readFile(|java+class:///snakes/Snake|))
myModel.containment[|java+class:///snakes/Snake|]



snakeMethods = [ e | e <- myModel.containment[|java+class:///snakes/Snake|], e.scheme == "java+method"];



import List;
size(snakeMethods)



int numberOfMethods(loc cl, M3 model) = size([ m | m <- model.containment[cl], isMethod(m)]);
numberOfMethods(|java+class:///snakes/Snake|, myModel)



classes(myModel)
map[loc class, int methodCount] numberOfMethodsPerClass = (cl:numberOfMethods(cl, myModel) | cl <- classes(myModel));



int numberOfFields(loc cl, M3 model) = size([ m | m <- model.containment[cl], isField(m)]);
map[loc class, int fieldCount] numberOfFieldsPerClass = (cl:numberOfFields(cl, myModel) | cl <- classes(myModel));



(cl : (numberOfFieldsPerClass[cl] * 1.0) / (numberOfMethodsPerClass[cl] * 1.0) | cl <- classes(myModel))



import Node;
import Set;
for (r <- sort(getKeywordParameters(myModel)<0>)) println("  <r>");



import IO;
if ({l} := findResources("Metrics/MeasuringJava/snakes-and-ladders-project-source.zip")) {
   copy(l[scheme="zip+<l.scheme>"][path="<l.path>!/"], |tmp:///snakes-and-ladders|, recursive=true);
} else {
   throw "failed to copy necessary source code to analyze for this example";
}



import lang::java::m3::Core;
import lang::java::m3::AST;



myModel = createM3FromDirectory(|tmp:///snakes-and-ladders/src|);



myMethods = methods(myModel);



import IO;
methodSrc = readFile(|java+method:///snakes/Square/landHereOrGoHome()|);



println(methodSrc)



(0 | it + 1 | /\W+/ := methodSrc)



methodFiles = myModel.declarations[|java+method:///snakes/Square/landHereOrGoHome()|];
// Now we know what file to look in, parse it:
fileAST = createAstFromFile(|tmp:///snakes-and-ladders/src/snakes/Square.java|, true);
// one of the declarations in this file is the method we wanted to see:
methodASTs = {d | /Declaration d := fileAST, d.decl == |java+method:///snakes/Square/landHereOrGoHome()|};



(0 | it + 1 | /Expression _ := methodASTs)



[m.src | /Expression m := methodASTs]



import List;
size([m.src | /Expression m := methodASTs]) == (0 | it + 1 | /Expression _ := methodASTs)



import IO;

str bottles(0) = "no more bottles"; // <1>
str bottles(1) = "1 bottle";
default str bottles(int n) = "<n> bottles"; // <2>

void sing() { // <3>
  for (n <- [99 .. 0]) {
       println("<bottles(n)> of beer on the wall, <bottles(n)> of beer.");
       println("Take one down, pass it around, <bottles(n-1)> of beer on the wall.\n");
  }  
  println("No more bottles of beer on the wall, no more bottles of beer.");
  println("Go to the store and buy some more, 99 bottles of beer on the wall.");
}



sing();



import IO;

str bottles(0) = "no more bottles";
str bottles(1) = "1 bottle";
default str bottles(int n) = "<n> bottles";

str singString() 
    = "<for (n <- [99 .. 0]) {><bottles(n)> of beer on the wall, <bottles(n)> of beer.
      'Take one down, pass it around, <bottles(n-1)> of beer on the wall.
      '
      '<}>
      'No more bottles of beer on the wall, no more bottles of beer.
      'Go to the store and buy some more, 99 bottles of beer on the wall.";



mySong = singString();



import List;

@synopsis{sort1: uses list indexing, a for-loop and a (complex) assignment}
list[int] sort1(list[int] numbers) { 
  if (size(numbers) > 0) {
     for (int i <- [0 .. size(numbers)-1]) {
       if (numbers[i] > numbers[i+1]) {
         // interesting destructuring bind:
         <numbers[i], numbers[i+1]> = <numbers[i+1], numbers[i]>;
         return sort1(numbers);
       }
    }
  }  
  return numbers;
}

@synopsis{sort2 uses list matching, a switch and recursion instead of assignment}
list[int] sort2(list[int] numbers) {
  switch(numbers){
    case [*int nums1, int p, int q, *int nums2]:
       if (p > q) {
          return sort2(nums1 + [q, p] + nums2);
       } else {
       	  fail;
       }
     default: return numbers;
   }
}

@synopsis{sort3: uses list matching, while and an assignment}
list[int] sort3(list[int] numbers) {
  while ([*int nums1, int p, *int nums2, int q, *int nums3] := numbers && p > q)
        numbers = nums1 + [q] + nums2 + [p] + nums3;
  return numbers;
}

@synopsis{sort4: uses list matching, solve, list concatentation, and assignment}
list[int] sort4(list[int] numbers) {
  solve (numbers) {
    if ([*int nums1, int p, *int nums2, int q, *int nums3] := numbers && p > q)
      numbers = nums1 + [q] + nums2 + [p] + nums3;
  }
  return numbers;
}

@synopsis{sort5: using recursion instead of iteration, and splicing instead of concat}
list[int] sort5([*int nums1, int p, *int nums2, int q, *int nums3]) {
  if (p > q) 
    return sort5([*nums1, q, *nums2, p, *nums3]); 
  else 
    fail sort5;
}

default list[int] sort5(list[int] x) = x;

@synopsis{sort6: inlines the condition into a when, and uses overloading with a default function.}
list[int] sort6([*int nums1, int p, *int nums2, int q, *int nums3]) 
  = sort5([*nums1, q, *nums2, p, *nums3])
  when p > q; 

default list[int] sort6(list[int] x) = x;


bool isSorted(list[int] lst) = !any(int i <- index(lst), int j <- index(lst), (i < j) && (lst[i] > lst[j]));

test bool sorted1a() = isSorted([]);
test bool sorted1b() = isSorted([10]);
test bool sorted1c() = isSorted([10, 20]);
test bool sorted1d() = isSorted([-10, 20, 30]);
test bool sorted1e() = !isSorted([10, 20, -30]);

test bool sorted2(list[int] lst) = isSorted(sort2(lst));
test bool sorted3(list[int] lst) = isSorted(sort3(lst));
test bool sorted4(list[int] lst) = isSorted(sort4(lst));
test bool sorted5(list[int] lst) = isSorted(sort5(lst));
test bool sorted6(list[int] lst) = isSorted(sort6(lst));



L = [9,8,7,6,5,4,3,2,1];
sort1(L);
sort2(L);
sort3(L);
sort4(L);
sort5(L);



list[int] even0(int max) {
  list[int] result = [];
  for (int i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}
even0(25);



list[int] even1(int max) {
  result = [];
  for (i <- [0..max])
    if (i % 2 == 0)
      result += i;
  return result;
}
even1(25);



list[int] even2(int max) {
  result = [];
  for (i <- [0..max], i % 2 == 0)
    result += i;
  return result;
}
even2(25);



list[int] even3(int max) {
  result = for (i <- [0..max], i % 2 == 0)
    append i;
  return result;
}
even3(25);



list[int] even4(int max) {
  return for (i <- [0..max], i % 2 == 0)
           append i;
}
even4(25);



list[int] even5(int max) {
  return [ i | i <- [0..max], i % 2 == 0];
}
even5(25);



list[int] even6(int max) = [i | i <- [0..max], i % 2 == 0];
even6(25);



set[int] even7(int max) = {i | i <- [0..max], i % 2 == 0};
even7(25);



@synopsis{fac1 demonstrates the ternary conditional and recursion}
int fac1(int n) = n <= 0 ? 1 : n * fac1(n - 1); //<1>

@synopsis{fac2 demonstrates overloading and dynamic dispatch with pattern matching}
int fac2(0) = 1;  //<2>
default int fac2(int n) = n * fac2(n - 1); //<3>

@synopsis{fac3 demonstrates structured programming and recursion}
int fac3(int n)  { //<4>
  if (n == 0) 
     return 1;
  return n * fac3(n - 1);
}



fac1(47);



fac2(47);



import IO; 

@synopsis{fizzbuzz1 revolves around ternary conditions}
void fizzbuzz1() {
   for (int n <- [1 .. 101]){
      fb = ((n % 3 == 0) ? "Fizz" : "") + ((n % 5 == 0) ? "Buzz" : "");
      println((fb == "") ?"<n>" : fb);
   }
}

@synopsis{fizzbuzz2 embraces pattern matching and the switch statement}
void fizzbuzz2() {
  for (n <- [1..101]) 
    switch(<n % 3 == 0, n % 5 == 0>) {
      case <true,true>  : println("FizzBuzz");
      case <true,false> : println("Fizz");
      case <false,true> : println("Buzz");
      default: println(n);
    }
}
 
@synopsis{fizzbuzz3 uses classical structured if-then-else} 
void fizzbuzz3() {
  for (n <- [1..101]) {
    if (n % 3 == 0) {
      print("Fizz");
    }
    if (n % 5 == 0) {
      print("Buzz");
    } else if (n % 3 != 0) {
      print(n);
    }
    println("");
  }
}



fizzbuzz1();



import IO;
println("Hello world, this is my first Rascal program");



import IO;
void hello() {
   println("Hello world, this is my first Rascal program");
}



hello()
hello()



module demo::basic::Hello

import IO;

void hello() {
   println("Hello world, this is my first Rascal program!");
}



println("I think I forgot to import the IO module...")



import List;
import util::Math;



alias Pos = tuple[int x,int y];



bool diagonalOverlap(Pos l, Pos r) = l != r ==> abs(l.x - r.x) == abs(l.y - r.y);



lrel[&T,&T] pairs(list[&T] p) =
        [ <p[i],p[j]> | i <- [0..size(p)-1], j <- [i+1..size(p)]];

bool isSolution(list[Pos] queens) = all(<l,r> <- pairs(queens), !diagonalOverlap(l,r));



list[list[Pos]] nQueens(int n) 
    = [queens 
        | cols <- permutations([0..n]),
          queens := [<i,cols[i]> | i <- [0..n]],
          isSolution(queens)];



nQueens(4)



import IO;
import String;

void quine(){
  println(program); // <3>
  println("\"" + escape(program, ("\"" : "\\\"", "\\" : "\\\\")) + "\";"); // <4>
}

str program = // <1>
"import IO;
import String;

void quine(){
  println(program);
  println(\"\\\"\" + escape(program, (\"\\\"\" : \"\\\\\\\"\", \"\\\\\" : \"\\\\\\\\\")) + \"\\\";\");
}

str program ="; // <2>



import IO;
str greeting = "\"Good Morning, Dr. Watson\", said Holmes";
println("\"" + greeting + "\"");



import String;
println("\"" + escape(greeting, ("\"": "\\\"")) + "\"");



println("\"" + escape(program, ("\"" : "\\\"", "\\" : "\\\\")) + "\";");



quine();



import IO; // <1>

@synopsis{Print a table of squares using a for loop and single line string templates}
void squares(int n) {
  println("Table of squares from 1 to <n>\n"); // <2>
  for (int I <- [1 .. n + 1])
      println("<I> squared = <I * I>");        // <3>
}

@synopsis{a solution with one multi line string template}
str squaresTemplate(int N) // <4>
  = "Table of squares from 1 to <N>
    '<for (int I <- [1 .. N + 1]) {>
    '  <I> squared = <I * I><}>";



squares(9);



squaresTemplate(9);



import IO;
println(squaresTemplate(9));



characters = {"Sneezy", "Sleepy", "Dopey", "Doc", "Happy", "Bashful", "Grumpy"};
pairs = (characters * characters) - {<c,c> | c <- characters};



import lang::html::IO;
import lang::html::AST;
import Content;

HTMLElement table(rel[&T, &U] r)
    = table([
        tr([
            td([text("<a>")]),
            td([text("<b>")])
        ])
    | <a, b> <- r    
    ]);



serve(table(pairs));



import IO;
if ({l} := findResources("Metrics/MeasuringJava/snakes-and-ladders-project-source.zip")) {
   copy(l[scheme="zip+<l.scheme>"][path="<l.path>!/"], |tmp:///snakes-and-ladders|, recursive=true);
} else {
   throw "failed to copy necessary source code to analyze for this example";
}



import lang::java::m3::Core;
import lang::java::m3::AST;



|tmp:///snakes-and-ladders/src/snakes/|.ls



myModel = createM3FromDirectory(|tmp:///snakes-and-ladders/src|);



myModel.containment



import IO;
println(readFile(|java+class:///snakes/Snake|))
myModel.containment[|java+class:///snakes/Snake|]
methods(myModel)
import Set;
size(methods(myModel))



allMethods = methods(myModel);
// methodInvocation reports on who calls who
myModel.methodInvocation
// so let's find out which method definitions are never invoked
allMethods - myModel.methodInvocation<1>



// methodOverrides is a tabel that explains which method overrides which other method
myModel.methodOverrides
// so we can compose that to find out who is probably called:
myModel.methodInvocation o (myModel.methodOverrides<1,0>) 
// and by adding all the others as well, we have a "complete" call graph
calls = myModel.methodInvocation + myModel.methodInvocation o (myModel.methodOverrides<1,0>);
// so which methods are defined but never called int this Game?
notCalled = methods(myModel) - calls<1>;
notConstructed = constructors(myModel) - calls<1>;



println(readFile(|java+method:///snakes/Player/square()|))
println(readFile(|java+method:///snakes/Square/nextSquare()|))



module Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Machine = machine: State+ states;    // <1>
syntax State = state: "state" Id name Trans* out; // <1>
syntax Trans = trans: Id event ":" Id to;         // <2>



extend lang::std::Layout;
extend lang::std::Id;
start syntax Machine = machine: State+ states;    // <1>
syntax State = state: "state" Id name Trans* out; // <1>
syntax Trans = trans: Id event ":" Id to;         // <2>



import IO;
writeFile(|tmp:///example.sm|, 
    "state Init
    '   buttonOn : Started
    '
    'state Started
    '   buttonPauze: Paused
    '   buttonPrint: Printing
    '
    'state Printing
    '   printingDone: Started
    '
    'state Failed
    '   buttonReset: Init
    ");



import ParseTree;
start[Machine] myStartMachine = parse(#start[Machine], |tmp:///example.sm|);
Machine myMachine = myStartMachine.top; // drop the whitespace before and after the machine



module Analyze

import Syntax;

set[str] unreachable(Machine m) {
  r = { <"<q1>","<q2>"> | (State)`state <Id q1> <Trans* ts>` <- m.states, 
				  (Trans)`<Id _>: <Id q2>` <- ts }+;
  qs = [ "<q.name>" | q <- m.states ];
  return { q | q <- qs, q notin r[qs[0]] } - qs[0];
}



set[str] unreachable(Machine m) {
  r = { <"<q1>","<q2>"> | (State)`state <Id q1> <Trans* ts>` <- m.states, 
				  (Trans)`<Id _>: <Id q2>` <- ts }+;
  qs = [ "<q.name>" | q <- m.states ];
  return { q | q <- qs, q notin r[qs[0]] } - {qs[0]};
}



unreachableIds = unreachable(myMachine);



module Compile

import Syntax;

str compile(Machine m) =
  "while (true) {
  '  event = input.next();
  '  switch (current) { 
  '    <for (q <- m.states) {>
  '    case \"<q.name>\":
  '      <for (t <- q.out) {>
  '      if (event.equals(\"<t.event>\"))
  '        current = \"<t.to>\";
  '      <}>
  '      break;
  '    <}>
  '  }
  '}"; 



str compile(Machine m) =
  "while (true) {
  '  event = input.next();
  '  switch (current) { 
  '  <for (q <- m.states) {>
  '    case \"<q.name>\":
  '      <for (t <- q.out) {>
  '      if (event.equals(\"<t.event>\"))
  '        current = \"<t.to>\";
  '      <}>
  '      break;
  '    <}>
  '  }
  '}"; 



import IO;
println(compile(myMachine))



module Idiomatic

import lang::java::\syntax::Java15; // <1>

CompilationUnit idiomatic(CompilationUnit unit) = innermost /*<2>*/ visit(unit) {
	
   case (Stm) `if (!<Expr cond>) <Stm a> else <Stm b>` =>   // <3>
        (Stm) `if (<Expr cond>)  <Stm b> else <Stm a>`
        
   case (Stm) `if (<Expr cond>) <Stm a>` =>                 // <4>
        (Stm) `if (<Expr cond>) { <Stm a> }` 
     when (Stm) `<Block _>` !:= a                           // <5>
        
   case (Stm) `if (<Expr cond>) <Stm a> else <Stm b>` =>   
        (Stm) `if (<Expr cond>) { <Stm a> } else { <Stm b> }` 
     when (Stm) `<Block _>` !:= a
                 
   case (Stm) `if (<Expr cond>) { return true; } else { return false; }` => // <6>
        (Stm) `return <Expr cond>;`
};



import lang::java::\syntax::Java15; // <1>
CompilationUnit idiomatic(CompilationUnit unit) = innermost /*<2>*/ visit(unit) {
   case (Stm) `if (!<Expr cond>) <Stm a> else <Stm b>` =>   // <3>
        (Stm) `if (<Expr cond>)
              '  <Stm b> 
              'else 
              '  <Stm a>`        
   case (Stm) `if (<Expr cond>) <Stm a>` =>                 // <4>
        (Stm) `if (<Expr cond>) { 
              '  <Stm a> 
              '}` 
     when (Stm) `<Block _>` !:= a                           // <5>
   case (Stm) `if (<Expr cond>) <Stm a> else <Stm b>` =>   
        (Stm) `if (<Expr cond>) { 
              '  <Stm a> 
              '} else { 
              '  <Stm b> 
              '}` 
     when (Stm) `<Block _>` !:= a                 
   case (Stm) `if (<Expr cond>) { return true; } else { return false; }` => // <6>
        (Stm) `return <Expr cond>;`
};



code = (CompilationUnit)  `class MyClass { 
                          '   int m() { 
                          '       if (!x) 
                          '           println("x"); 
                          '       else 
                          '           println("y");  
                          '       if (x)
                          '           return true; 
                          '       else 
                          '           return false;
                          '   } 
                          '}`;
idiomatic(code)
