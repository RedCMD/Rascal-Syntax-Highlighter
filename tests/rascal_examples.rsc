// examples
module bug::Report

start syntax Start [start] /* start */ = @\start{start} \start: Start start "start" start[Start]; // start

visit (and(and(f(),t()),t())) { case Bool b => eval(b) }

void dummy(/include::\{LibDir\}<path:[^\]]+>\[tags=module\]/) {}

void no(loc a = |unknown:///|, loc b = |unknown://a/|, loc c = |unknown:///|, int d = 0) {}

void yes1(loc a = |unknown:///|, loc b = |unknown:///|, int d = 0){}

void yes2(loc l) {
	
	if (|unknown:///| == 1 && |unknown:///| == l) {
		;
	}
}

loc validRascal(int i, str s) {
     return |file:///x/a/< "dir< i + 1 >" >/file< i > 2 ? s : "fallback" >.txt|; 
}

|file:///mnt/<callX("arg")>/y.txt|

true

eval(and(f(),t()));

test bool tstWordCount4(str txt) {
    lines = split(txt, "\n");
    return wordCount(lines, countInLine1) == wordCount(lines, countInLine2);
}    

10
0


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


int square(int n) { return n * n; }
test int (int): function(|prompt:///|(0,35,<1,0>,<1,35>));

list[Declaration] smallSqlAST = getASTs(|project://smallsql0.21_src|);
list[Declaration] smallSqlAST = getASTs(|file:///path/to/smallsql0.21_src|);
void (): function(|prompt:///|(0,76,<1,0>,<3,1>))

square(12);
int: 144


L = [1, 3, 5, 7];
list[int]: [1,3,5,7]

(0 | it + e | int e <- L);
int: 16

(1 | it * e | int e <- L);
int: 105

$2010-07-15$
datetime: $2010-07-15$
$2010-07-15T07:15:23.123+0100$;
datetime: $2010-07-15T07:15:23.123+01:00$
DT = $2010-07-15T09:15:23.123+03:00$;
datetime: $2010-07-15T09:15:23.123+03:00$
DT.isDateTime;
bool: true
DT.justDate;
datetime: $2010-07-15$
DT.justTime;
datetime: $T09:15:23.123+03:00$
DT.century;
int: 20

N = 13;
int: 13
"The value of N is <N>";
str: "The value of N is 13"
// ---
// The value of N is 13
// ---
"The value of N*N is <N*N>";
str: "The value of N*N is 169"
// ---
// The value of N*N is 169
// ---
"The value is <(N < 10) ? 10 : N*N>";
str: "The value is 169"
// ---
// The value is 169
// ---

"N is <if(N < 10){> small <} else {> large <}>";
str: "N is  large "
// ---
// N is  large 
// ---
"N is <if(N < 10){> small <} else {> large (<N>)<}>";
str: "N is  large (13)"
// ---
// N is  large (13)
// ---
"before <for(x<-[1..5]){>a <x> b <}>after";
str: "before a 1 b a 2 b a 3 b a 4 b after"
// ---
// before a 1 b a 2 b a 3 b a 4 b after
// ---

import IO;
ok
println("hello
this
  is
    new")
// hello
// this
//   is
//     new
// ok

if (true)
  println("this is
          'what
          '  margins
          'are good for
          ");
// this is
// what
//   margins
// are good for
          
// ok

str genMethod(str n) = "int <n>() {
                       '  return 0;
                       '}";
str (str): function(|prompt:///|(0,99,<1,0>,<3,27>))
str genClass() = "class myClass {
                 '  <genMethod("myMethod")>
                 '}";
str (): function(|prompt:///|(0,99,<1,0>,<3,21>))
println(genClass());

class myClass {
  int myMethod() {
    return 0;
  }
}
ok

tuple[str first, str last, int age] P = <"Jo","Jones",35>;
tuple[str first,str last,int age]: <"Jo","Jones",35>
P.first;
str: "Jo"
// ---
// Jo
// ---
P.first = "Bo";

tuple[str first,str last,int age]: <"Bo","Jones",35>

test a() = parse(#A,"ab") == appl(prod(label("myA",lex("A")),[lit("a"),sort("bLabel",lex("B"))],{}),[appl(prod(lit("a"),[\char-class([range(97,97)]),[char(97)]])),appl(prod(label("myB", lex("B"),[lit("b")],{}),[appl(prod(lit("b"),[\char-class([range(98,98)]),[char(98)]]))])) ]);

@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@synopsis{Tests the potential clashes among value constructors of different adts, plus, the identified clash with: bool eq(value, value);}
module lang::rascal::\syntax::tests::ImplodeTestGrammar

import ParseTree;

lexical Id = [a-z] !<< [a-z]+ !>> [a-z];
layout W = [\ \t\n\r]*;

lexical Num = \int: [0-9]+;
syntax Exp 
	= id: Id name
	| number: Num n
	| non-assoc eq: Exp e1 "==" Exp e2;
	

lexical Number = \int: [0-9]+;
syntax Expr 
	= id: Id name
	| number: Number n
	| non-assoc eq: Expr e1 "==" Expr e2;


public Exp parseExp(str s) = parse(#Exp, s);
public Exp expLit1() = (Exp) `a == b`;
public Exp expLit2() = (Exp) `a == 11`;

public Expr parseExpr(str s) = parse(#Expr, s);
public Expr exprLit1() = (Expr) `a == b`;
public Expr exprLit2() = (Expr) `a == 11`;



default bool asubtype(AType l, AType r){
    switch(r){
        case l:
            return true;
        case tvar(_):
            throw TypeUnavailable();
        case overloadedAType(overloads):
            //TODO: Alternative: return asubtype(l, (\avoid() | alub(it, tp) | <_, _, tp> <- overloads));
           return isEmpty(overloads) ? asubtype(l, avoid()) : any(<_, _, tp> <- overloads, asubtype(l, tp));
	}
}

public AType alt({*AType a, alt(set[AType] b)}) = AType::alt(a + b);

// deprecated; remove after bootstrap
AProduction associativity(AType rhs, AAssociativity a, set[AProduction] rest)
  = associativity(rhs, a, withAssoc + withNewAssocs)
  when  withoutAssoc := {p | AProduction p:prod(_,_) <- rest, !(\aassoc(_) <- p.attributes)},
        withoutAssoc != {},
        withAssoc := rest - withoutAssoc,
        withNewAssocs := {p[attributes = p.attributes + {\aassoc(a)}] | AProduction p <- withoutAssoc}
        ;

void storeAllowUseBeforeDef(Tree container, list[Tree] allowedParts, Collector c){
    c.push(key_allow_use_before_def, <getLoc(container), cover([getLoc(allowed) | allowed <- allowedParts])>);
}

        	    beginUseTypeParameters(c, closed=false);
                 // The standard rules would declare arguments and kwFormals as variableId();
                for(arg <- arguments) { c.enterScope(arg); collect(arg.\type, c); if(arg is named) { c.fact(arg, arg.\type); } c.leaveScope(arg); }
                for(kwa <- kwFormals) { c.enterScope(kwa); collect(kwa.\type, kwa.expression, c); c.fact(kwa, kwa.\type); c.leaveScope(kwa); }
            endUseTypeParameters(c);
			
			if (atuple(_) := aglbParams)
        return afunc(aglbReturn, aglbParams.formals, kwl == kwr ? kwl : []);
    else
        return avalue();
		
		
        alwaysSucceeds = all(pat <- getFormals(signature.parameters), pat is typedVariable) && !(decl is conditional) && !(decl is \default && /(Statement) `fail <Target _>;` := decl.body);
		
        if(decl is \default) collect(decl.body, c);
		
                vars += { *introducedVars(kwa.expression, c) | kwa <- keywordArguments.keywordArgumentList };
				
				
            try {
                tern_overloads += <key, idr, ternaryOp(op, computeType, current, tp, t2, t3, s)>;
             } catch checkFailed(list[FailMessage] _): /* continue with next overload */;
               catch NoBinding(): /* continue with next overload */;
               catch _: /* continue with next overload */;
			   
			   
        try {
            mfrom = getRascalModuleName(from, moduleStrs, pcfg);
            mto = getRascalModuleName(to, moduleStrs, pcfg);
            strPaths += <mfrom, r, mto >;
        } catch _: ;/* ignore non-existing module */
		
		
    moduleScopes = { t@\loc | t <- range(namedTrees) };
	
	
bool inPatternNames(str name, Collector c){
    for(lrel[str,loc] pnames :=  c.getStack(patternNames), <str n, loc _> <-pnames) if(n == name) return true;
    return false;
}



                if(tm.store[key_bom]? && rel[str,datetime,PathRole] bom := tm.store[key_bom]){
                   for(<str mname, datetime timestampInBom, PathRole pathRole> <- bom){
                        if(timestampInBom != lastModRSC[mname]){
                            valid = false;
                            println("In BOM of <m> (<lastModRSC[m]>), unequal src time for <mname>: <timestampInBom> != <lastModRSC[mname]>");
                        }
                        if(timestampInBom > lastModTPL[mname]){
                            valid = false;
                            println("In BOM of <m> (<lastModRSC[m]>), outdated tpl for <mname>: <timestampInBom> \> <lastModTPL[mname]>");
                        }
                        if(mname == m && timestampInBom != lastModRSC[m]){
                            valid = false;
                            println("In BOM of <m> (<lastModRSC[m]>), <timestampInBom> != <lastModRSC[m]>");
                        }
                    }
                }
				
				
		visit(m) { case Expression e: cnt += 1; };
		
		
    visit(m){
      case (SyntaxDefinition) `<Visibility _> layout <Sym name> = <Prod p> ;`: {
            stats["layout"] ? 0 += 1;
            nonterm += "<name>";
            stats["layoutAlts"] ? 0 += cntAlt(p);
            }
      case (SyntaxDefinition) `lexical <Sym name> = <Prod p> ;` : {
            stats["lexical"] ? 0 += 1;
             nonterm += "<name>";
            stats["lexicalAlts"] ? 0 += cntAlt(p);
            }
      case (SyntaxDefinition) `keyword <Sym name> = <Prod p> ;` : {
            stats["keyword"] ? 0 += 1;
            nonterm += "<name>";
            stats["keywordAlts"] ? 0 += cntAlt(p);
            }
      case (SyntaxDefinition) `<Start _> syntax <Sym name> = <Prod p> ;` : {
            nonterm += "<name>";
            stats["syntax"] ? 0 += 1;
            stats["syntaxtAlts"] ? 0 += cntAlt(p);
        }
      case Declaration d:
            if(d is \data || d is \dataAbstract) datadefs += "<d.user>"; 
      case Variant _: 
          stats["variant"] ? 0 += 1;
    }
	
	
MuExp muPrim("negative", areal(), [areal()], [muCon(real r)], loc src2)  = muCon(-r);


data JGenie
    = jgenie(
        str () getModuleName,
        loc () getModuleLoc,
        void (MuFunction) setFunction,
        MuFunction () getFunction,
        str () getFunctionName,
        bool (MuExp) isDefinedInCurrentFunction,
        AType (loc src) getType,
        str(loc def) getImportedModuleName,
        str (AType t) getATypeAccessor,
        str (list[loc] srcs) getAccessor,
        Define (loc src) getDefine,
        list[MuExp] (loc src) getExternalRefs,
        list[Keyword] (MuFunction fun) collectKwpFormals,
        lrel[str name, AType atype, MuExp defaultExp] (MuFunction fun) collectKwpDefaults,
        list[str] (MuFunction fun) collectRedeclaredKwps,
        list[str] (MuFunction fun) collectDeclaredKwps,
        bool(AType) hasCommonKeywordFields,
        str(AType atype) shareType,
        str(AType atype) accessType,
        bool(AType atype) isSharedType,
        str(value con) shareConstant,
        str(Symbol, map[Symbol,Production]) shareReifiedConstant,
        tuple[str,str,list[value]] () getConstants,
        bool (str con) isWildCard,
        void(set[MuExp] evars) addExternalRefs,
        void(set[MuExp] lvars) addLocalRefs,
        bool(MuExp var) isRef,
        bool (MuExp var)varHasLocalScope,
        bool (MuExp var)varHasGlobalScope,
        str(str prefix) newTmp,
        void(str) addImportedLibrary,
        list[str] () getImportedLibraries,
        bool (tuple[str name, AType funType, str scope, list[loc] ofunctions, list[loc] oconstructors] overloads) usesLocalFunctions
      )
    ;
    
	
	
default list[str] transPrimArgs(str prim, AType result, list[AType] details, list[MuExp] exps, JGenie jg){
    return  [details[i]? ? transWithCast(details[i], exps[i], jg) : trans(exps[i], jg) | int i <- index(exps)];
}    


        call_code = base_call = "";
		
		
    top-down-break visit(fd){
        case (Expression) `<Type _> <Parameters _> { <Statement+ _> }`:
                /* ignore type vars in closures. This is not water tight since a type parameter of the surrounding
                  function may be used in the body of this closure */;
        case TypeVar tv: res += tv;
    }
	
	
	top-down-break visit(c) {
		case (Statement) `insert <DataTarget _> <Statement _>`: return true;
		case Visit _: ;
	}
	
	
    rprops = for(Tree p <- reverse([p | Tree p <- pats])){
                 append <nElem, nMultiVar>;
                 if(isConcreteMultiVar(p)) {nMultiVar += 1; nElem += nIter(p);} else {nElem += 1;}
             };
			 
			 import ParseTree;

/*
 * translateType: translate a concrete (textual) type description to a Symbol
 */
 
 AType translateType(Type tp) {
    return getType(tp@\loc);
}

@examples{
Import relevant libraries:
```rascal-shell,continue
import Exception;
import IO;
```
Define the map `weekend` and do a subscription with a non-existing key:
```rascal-shell,continue,error
weekend = ("saturday": 1, "sunday": 2);
weekend["monday"];
```
Repeat this, but catch the exception. We use variable `N` to track what happened:
```rascal-shell,continue
N = 1;
try {
   N = weekend["monday"];
} catch NoSuchKey(v):
  N = 100;
println(N);
```
}

@javaClass{org.rascalmpl.library.Prelude}
public java void appendToFile(loc file, value V..., str charset=DEFAULT_CHARSET, bool inferCharset=!(charset?))
throws PathNotFound, IO;


@synopsis{Apply a function to all list elements and return list of results.}
@description{
Apply a function `fn` to each element of `lst` and return the list of results.
}
@examples{
```rascal-shell
import List;
int incr(int x) { return x + 1; }
mapper([1, 2, 3, 4], incr);
```
}
list[&U] mapper(list[&T] lst, &U (&T) fn) =  [fn(elm) | &T elm <- lst];


list[TextEdit] layoutDiff(Tree original, Tree formatted, bool recoverComments = true, CaseInsensitivity ci = asIs()) {
    assert original := formatted : "nothing except layout and keyword fields may be different for layoutDiff to work correctly. <treeDiff(original, formatted)>";
}

public FormalContext[str, str] readCxt(loc input)  {
    list[str] d = readFileLines(input);
    int nRows = toInt(d[2]);
    int nCols = toInt(d[3]);
    int theStart = 5+nRows+nCols;
    list[str] e = tail(d, size(d)-theStart);
    int idx = 5;
    map [str, set[str]] vb = ();
    for (str f <- e) {
         set[str] b = {d[5+nRows+i]|int i<-[0, 1..size(f)], charAt(f,i)==88};
         vb[d[idx]] = b;
         idx = idx+1;
         }
    return toFormalContext(vb);
    }

return digraph("fca", 
      [NODE( [<"style","filled">, <"fillcolor","cornsilk">,<"fontcolor","blue">,<"shape","ellipse">])] 
         +nodes+edges); 
     
	 
	 
Graph[Symbol] symbolDependencies(GrammarDefinition d) =
  { *symbolDependencies(d.modules[m].grammar) | m <- d.modules };
  
  
public LinearExpression neg(LinearExpression exp) = 
	linearExp((n : -v  | <n,v> <- toList(exp.coefficients)),-exp.const);
	
public LinearExpression add(LinearExpression lhs, LinearExpression rhs) =
	linearExp(	(n : (lhs.coefficients[n] ? 0) + (rhs.coefficients[n] ? 0) |
				n <- domain(lhs.coefficients) + domain(rhs.coefficients)),
			  lhs.const + rhs.const);
			  
			  
			  
num variance([num hd, *num tl]) {
	if (tl == []) {
		return 0.;	
	}
	//Compensated variant of the two pass algorithm
	n = 1 + size(tl);
	mn = mean(tl + hd);
	sum2 = (pow(hd - mn, 2) | it + pow(i - mn, 2) | i <- tl); 
	sum3 = (hd - mn | it + (i - mn) | i <- tl); 
	return (sum2 - (pow(sum3,2)/n)) / (n -1);
}


    if (size(a) > 1) { // Multiple lines 
        Text T1 = \continue(A, V([]), opts, m-i);
        return vv(T, rvv(vskip(v), HVHV(T1, m-hwidth(T1), B, opts, m, H([]))));
    }
	
	
    assert [info("aTestExample(TheTestClass) started", loc _), info("aTestExample(TheTestClass) finished", _)] := results;

lexical PathChar = !([\a00-\a20\< \> : \" | ? * \\ /] - [\ ]);



    assert u := newU : "the rewritten tree matches the newly parsed";
	
	
     switch (sym) {
       case \sort(str s): a.typ = "<pkg>.<s>"; 
       case \lex(str s): a.typ = "<pkg>.<s>"; 
       case \iter(\sort(str s)): a.typ = "<l>\<<pkg>.<s>\>";  
       case \iter-star(\sort(str s)): a.typ = "<l>\<<pkg>.<s>\>";
       case \iter-seps(\sort(str s), _): a.typ = "<l>\<<pkg>.<s>\>";
       case \iter-star-seps(\sort(str s), _): a.typ = "<l>\<<pkg>.<s>\>";
       case \iter(\lex(str s)): a.typ = "<l>\<<pkg>.<s>\>";  
       case \iter-star(\lex(str s)): a.typ = "<l>\<<pkg>.<s>\>";
       case \iter-seps(\lex(str s), _): a.typ = "<l>\<<pkg>.<s>\>";
       case \iter-star-seps(\lex(str s), _): a.typ = "<l>\<<pkg>.<s>\>";
       case \parameterized-sort(str s, [Symbol _:str _(str z)]): a.typ = "<pkg>.<s>_<z>";
       case \parameterized-lex(str s, [Symbol _:str _(str z)]): a.typ = "<pkg>.<s>_<z>";
       case \iter(\parameterized-sort(str s, [Symbol _:str _(str z)])): a.typ = "<l>\<<pkg>.<s>_<z>\>";  
       case \iter-star(\parameterized-sort(str s, [Symbol _:str _(str z)])): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       case \iter-seps(\parameterized-sort(str s, [Symbol _:str _(str z)]), _): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       case \iter-star-seps(\parameterized-sort(str s, [Symbol _:str _(str z)]), _): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       case \iter(\parameterized-lex(str s, [Symbol _:str _(str z)])): a.typ = "<l>\<<pkg>.<s>_<z>\>";  
       case \iter-star(\parameterized-lex(str s, [Symbol _:str _(str z)])): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       case \iter-seps(\parameterized-lex(str s, [Symbol _:str _(str z)]), _): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       case \iter-star-seps(\parameterized-lex(str s, [Symbol _:str _(str z)]), _): a.typ = "<l>\<<pkg>.<s>_<z>\>";
       
     }
	 
public Graph[Symbol] symbolDependencies(GrammarDefinition d) =
  { *symbolDependencies(d.modules[m].grammar) | m <- d.modules };
    
	
	
  top-down-break visit (\mod) {
    case SyntaxDefinition s : result += s; 
    case Body b => b
  }
  
  
public tuple[set[Production] prods, Maybe[Symbol] \start] rule2prod(SyntaxDefinition sd) {  
    switch (sd) {
      case \layout(_, nonterminal(Nonterminal n), Prod p) : 
        return <{prod2prod(\layouts("<n>"), p)},nothing()>;
      case \language(present() /*start*/, nonterminal(Nonterminal n), Prod p) : 
        return < {prod(\start(sort("<n>")),[label("top", sort("<n>"))],{})
                ,prod2prod(sort("<n>"), p)}
               ,just(\start(sort("<n>")))>;
      case \language(absent(), parametrized(Nonterminal l, {Sym ","}+ syms), Prod p) : 
        return <{prod2prod(\parameterized-sort("<l>",separgs2symbols(syms)), p)}, nothing()>;
      case \language(absent(), nonterminal(Nonterminal n), Prod p) : 
        return <{prod2prod(\sort("<n>"), p)},nothing()>;
      case \lexical(parametrized(Nonterminal l, {Sym ","}+ syms), Prod p) : 
        return <{prod2prod(\parameterized-lex("<l>",separgs2symbols(syms)), p)}, nothing()>;
      case \lexical(nonterminal(Nonterminal n), Prod p) : 
        return <{prod2prod(\lex("<n>"), p)}, nothing()>;
      case \keyword(nonterminal(Nonterminal n), Prod p) : 
        return <{prod2prod(keywords("<n>"), p)}, nothing()>;
      default: { iprintln(sd); throw "unsupported kind of syntax definition? <sd> at <sd@\loc>"; }
    }
} 
   
   
test bool asciiEscape() = \char-class([range(0,127)]) == #[\a00-\a7F].symbol;
test bool utf16Escape() = \char-class([range(0,65535)]) == #[\u0000-\uFFFF].symbol;
test bool utf32Escape() = \char-class([range(0,1114111)]) == #[\U000000-\U10FFFF].symbol;
test bool highLowSurrogateRange1() = \char-class([range(9312,12991)]) == #[①-㊿].symbol;
test bool highLowSurrogateRange2() = \char-class([range(127829,127829)]) == #[🍕].symbol;
test bool differentEscapesSameResult1() = #[\a00-\a7F] == #[\u0000-\u007F];
test bool differentEscapesSameResult2() = #[\a00-\a7F] == #[\U000000-\U00007F];



 println("INT - COMP:");
 iprintln(INT-COMP);
 
 println("COMP - INT:");
 iprintln(COMP - INT);
 
 
 
 @ignoreInterpreter{gives wrong answer 1186}
test bool cntStr1()         {cnt = 0; visit(Pico){ case str _: cnt += 1; }; return cnt == 187; }
test bool cntStr2()         = size([x | /x:str _ := Pico]) == 187;


@ignoreInterpreter{gives wrong answer 1186}
test bool cntStr1()         {cnt = 0; visit(Rascal){ case str _: cnt += 1; }; return cnt == 3967; }
test bool cntStr2()         = size([x | /x:str _ := Rascal]) == 3967;


    if(v@l? && [*int x,*int y] := v@l) {
       res = res + [ x, y ];
       fail;
    }
	
	
test bool canonicalTypesRegression1() = canonicalTypes(0.0, 0);
test bool canonicalTypesRegression2() = canonicalTypes(0r, 0);
test bool canonicalTypesRegression3() = canonicalTypes(0r, 0.0);
  
  
  
test bool untypedCatch1() {
    x = 1;
	try {
		throw "exception";
	} 
	catch _: x += 1;
	return x == 2;
}



    assert int(int)(int) _ := func;


import Type;

// Operators
  
 test bool product(list[&A]X, list[&B] Y) =
  isEmpty(X) ? isEmpty(X * Y) 
             : (isEmpty(Y) ? isEmpty(X * Y) 
                           : all(x <- X, x in domain(X * Y)) &&
                             all(y <- Y, y in range(X * Y)) &&
                             all(<x, y> <- X * Y, x in X, y in Y));
  
  
  
test bool sliceFirstNegative(list[int] L) {
  if(isEmpty(L)) return true;
  f = 1;
  return L[-f..] == makeSlice(L, size(L) - f,  size(L) - f + 1, size(L));
}

test bool sliceEndNegative(list[int] L) {
  if(isEmpty(L)) return true;
  e = arbInt(size(L));
  return L[..-e] == makeSlice(L, 0, 1, e == 0 ? e : size(L) - e);
}



// Build a location for an area from index f to index t.
loc buildLoc(int f, int t, str base = "base.src"){
    return |test:///<base>|(f, t-f, getLineAndColumn(f), getLineAndColumn(t));
}

// Restrict i to legal index values
int restrict(int i){
    if(i < 0) i = -i;
    if(i > maxIndex) return arbInt(maxIndex);
    return i;
}



test bool sliceFirstNegative(node N) {
  L = getChildren(N);
  if(isEmpty(L)) return true;
  f = 1;
  return N[-f..] == makeSlice(L, size(L) - f,  size(L) - f + 1, size(L));
}

test bool sliceEndNegative(node N) {
  L = getChildren(N);
  if(isEmpty(L)) return true;
  e = arbInt(size(L));
  return N[..-e] == makeSlice(L, 0, 1, e == 0 ? e : size(L) - e);
}



	return <f([1,2,3,4,5,6]), g([1,2,3,4,5,6]), g([1,2,3,4,5]), h([1,2,3,4,5,6]) > ==
		   <-1000,            -2000,            -3000,          -3000>;
		   
		   
private list[loc] collect(Tree t) = [s@\loc | /Tree s := t, s@\loc?];



test bool sliceFirstNegative(str L) {
  if(isEmpty(L)) return true;
  f = 1;
  return L[-f..] == makeSlice(L, size(L) - f,  size(L) - f + 1, size(L));
}

test bool sliceEndNegative(str L) {
  if(isEmpty(L)) return true;
  e = arbInt(size(L));
  return L[..-e] == makeSlice(L, 0, 1, e == 0 ? e : size(L) - e);
}



lexical C = C C C | "a"@2 | "b";



test bool singleA() = check(#[A], char(65));
test bool singleB() = check(#[B], char(66));
test bool notSingleB() = !check(#[A], char(66));
test bool singleAB1() = check(#[A-B], char(65));
test bool singleAB2() = check(#[A-B], char(66));
test bool notSingleAB() = !check(#[A-B], char(67));

test bool charclassLUB() = set[[A-D]] _ := {char(65), char(66), char(67), char(68)};
test bool charclassLUB2() = set[[a-z]] _ := {char(i) | i <- [97..122]};


						   
test bool concreteMatch231() {
	res = [];
	visit([Stat] "if x then a := 1;b:=2 else c:=3 fi"){
		case Identifier ident: res += "<ident>";
	}
	return res == ["x", "a", "b", "c"];
}						   
 		
		
		
test bool keywordParam5() {
    return <f5(0,print = true), f5(1,color = "grey")> == 
     <<point(0),point(1,color="blue")>,<point(1),point(2,color="blue")>>;
}



test bool matchInLoop1(){
	lst = [1, 2, 3];
	cnt = 0;
	for(int x <- lst){
		switch(x){
			case int n: cnt += n;
		}
	}
	return cnt == (0 | it + x | x <- lst);
}


 
 int sw5(value v){
    int n = 0;
    switch(v){
        case "abc":                             n = 1;
        case e(/<s:^[A-Za-z0-9\-\_]+$>/, 2):     { n = 2; if (str _ := s /* just use the s to avoid warning */) true; }
        case e(/<s:^[A-Za-z0-9\-\_]+$>/, 3):     { n = 3; if (str _ := s) true; }
        case 4:                                 n = 4;
        case e():                               n = 5;
        case e(int _):                          n = 6;
        case str _(7):                          n = 7;
        case [1,2,3]:                           n = 8;
        case [1,2,3,4]:                         n = 9;
        case e("abc", 10):                      n = 10;
        case e("abc", int _):                   n = 11;
        case node _:                            n = 12;
        default:                                n = 13;
    }
    return n;
}



test bool afterCatch(){
    try f(); catch _: x=3;
    return true;
}



test bool visit10() {
	return visit({ "a"(1,1), "b"(2,2), "c"(3,3) }) {
				case set[node] s => s + { "d"(4,5) }
				case node n:str s(int _,int _) => { elem = ( 0 | it + i | int i <- n); (s + "_been_here")(elem,elem); }
				case int i => i + 100
			} 
			==
			{ "a_been_here"(202,202),
  			  "b_been_here"(204,204),
  			  "d"(4,5),
  			  "c_been_here"(206,206)
			}
			;
}



test bool cntInt()    {cnt = 0; visit(G0){ case int _: cnt += 1; } return cnt == 11; } // visit does go into kw params



// abs
  
test bool abs1() = abs(0) == 0;
test bool abs2() = abs(0r) == 0r;
test bool abs3() = abs(-1) == 1;
test bool abs4() = abs(-1r1) == 1r1;
test bool abs5() = abs(1) == 1;
test bool abs6() = abs(1.5) == 1.5;
test bool abs7() = abs(3r2) == 3r2;
test bool abs8() = abs(-1.5) == 1.5;
test bool abs9() = abs(-3r2) == 3r2;
  
  
  
// compare
  
test bool compare1() = 1r1 == 1;
test bool compare2() = 1r1 == 1.0;
test bool compare3() =  -1r1 == -1;
  
  
  
@synopsis{Specification of what it means for `treeDiff` to be syntactically correct}
@description{
TreeDiff is syntactically correct if:
* The tree after rewriting _matches_ the tree after applying the edits tot the source text and parsing that.
* Note that _matching_ ignores case-insensitive literals and layout, indentation and comments
}
bool editsAreSyntacticallyCorrect(type[&T<:Tree] grammar, str example, (&T<:Tree)(&T<:Tree) transform, list[TextEdit](Tree, Tree) diff) {
    orig        = parse(grammar, example);
    transformed = transform(orig);
    edits       = diff(orig, transformed);
    edited      = executeTextEdits(example, edits);

    try {
        if (transformed := parse(grammar, edited)) {
            return true;
        }
        else {
            println("The edited result is not the same:");
            println(edited);
            println("As the transformed:");
            println(transformed);
            return false;
        }
    }
    catch ParseError(loc l): {
        println("<transform> caused a parse error <l> in:");
        println(edited);
        return false;
    }
}



bool eq(num a, num b) {
	error = 1 / pow(10, min(scale(a), scale(b)) - 1);
	return abs(a-b) <= error;
}


    value mapToSet(value _:map[value, value] m) = {{k,m[k]} | value k <- m};
	
	
set[Production] fixParameters(set[Production] input) {
  return innermost visit(input) {
    case prod(\parameterized-sort(str name, [*pre, sort(str x), *post]),lhs,  as) =>
         prod(\parameterized-sort(name,[*pre,\parameter(x,adt("Tree",[])),*post]),visit (lhs) { case sort(x) => \parameter(x,adt("Tree",[])) }, as)
  }
}


data RascalRuntime
  = evaluator(
      PathConfig pcfg,
      void () reset,
      Result[&T] (type[&T] typ, str command) eval,
      type[value] (str command) staticTypeOf,
      void (int duration) setTimeout 
  );



data REPL
  = repl(
     str title = "", 
     str welcome = "", 
     str prompt = "\n\>",
     str quit = "", 
     loc history = |home:///.term-repl-history|, 
     Content (str command) handler = echo,
     Completion(str line, str word) completor = noSuggestions,
     str () stacktrace = str () { return ""; }
   );



@synopsis{Skip double quoted blocks}
list[Output] compileMarkdown([str first:/^\s*``````/, *block, str second:/^``````/, *str rest], int line, int offset, PathConfig pcfg, CommandExecutor exec, Index ind, list[str] dtls, int sidebar_position=-1)
  = [ 
      out(first), 
      *[out(b) | b <-block], 
      out(second), 
      *compileMarkdown(rest, line, offset, pcfg, exec, ind, dtls, sidebar_position=sidebar_position)
  ];



    // read indices from projects we depend on, if present
    ind += {*readBinaryValueFile(#rel[str,str], inx) | l <- pcfg.libs, inx := l + "docs" + "index.value", exists(inx)};



int countGenAndUse((Cmd) `<EvalCmd c>`){
    n = 0;
    visit(c){ case GenCmd _: n += 1; 
              case UseCmd _: n += 1;
             }
    return n;
}



public str generateTuple({Type ","}+ ets){
   return intercalate(", ", [generateValue(et) | et <-ets]);
}

public str generateTuple(list[Type] ets){
   return intercalate(", ", [generateValue(et) | et <-ets]);
}



  assert /ok[\r\n]+/ := exec.eval("import IO;")["text/plain"] : "result of import should be ok";

bool isSubset(set[set[&T]] candidate, set[&T] s ) {
         for (set[&T] c <- candidate) 
         if (s<c) return true;
         return false;
     }   


private str learnComments(Tree original, Tree replacement) {
    originalComments = ["<c>" | /c:appl(prod(_,_,{\tag("category"(/^[Cc]omment$/)), *_}), _) := original];
	}
	
  if ([①-㊿] circled := t) {
    assert [⑭] _ := circled;
    assert NotAZ _ := circled;
    return true;
  }



tuple[str quoted, str execute, bool hasHoles, map[str,str] bindings] preprocessCode(int questionId, 
                                                                                TokenOrCmdList q, 
                                                                                str setup, 
                                                                                map[str,str] initialEnv, 
                                                                                PathConfig pcfg){
    <qt, ex> = handle(q);
    return <qt, ex, nholes > 0, env>;
																				}
																				
																				
																				
Grammar G0 = grammar(
  {sort("S")[
      @id=2
    ]},
  (
    sort("S")[
      @id=3
    ]:choice(
      sort("S")[
        @id=4
      ],
      {prod(
          sort("S")[
            @id=5
          ],
          [lit("0")[
              @id=6
            ]],
          {})}),
    lit("0")[
      @id=7
    ]:choice(
      lit("0")[
        @id=8
      ],
      {prod(
          lit("0")[
            @id=9
          ],
          [\char-class([range(48,48)])[
              @id=10
            ]],
          {})})
  ));


test bool repositionSimulatesReparse() {
    t1 = parse(#start[Program], facPico);
    t2 = reposition(t1); // defaults set
    assert t1 := t2; // but that skips keyword parameters and layout
    return collect(t1) == collect(t2);
}

module lang::rascal::tests::basic::ListRelations

import List;
import ListRelation;
import Type;

// Operators
 test bool product(list[&A]X, list[&B] Y) =
  isEmpty(X) ? isEmpty(X * Y) 
             : (isEmpty(Y) ? isEmpty(X * Y) 
                           : all(x <- X, x in domain(X * Y)) &&
                             all(y <- Y, y in range(X * Y)) &&
                             all(<x, y> <- X * Y, x in X, y in Y));
  
list[num] toLLCoefficients(Coefficients coefficients, list[str] indexVar) =
	[coefficients[i] ? zero | i <- indexVar];


list[str] transSliceArgs(MuExp first, MuExp second, MuExp end, JGenie jg) =  [ first == muNoValue() ? "null" : trans2NativeInt(first,jg),
                                                                               second == muNoValue() ? "null" : trans2NativeInt(second,jg), 
                                                                               end == muNoValue() ? "null" : trans2NativeInt(end,jg) ];

module lang::rascalcore::compile::Rascal2muRascal::RascalType

import lang::rascalcore::check::AType;
import lang::rascalcore::compile::Rascal2muRascal::TypeUtils;
import lang::rascal::\syntax::Rascal;
import ParseTree;

/*
 * translateType: translate a concrete (textual) type description to a Symbol
 */
 
 AType translateType(Type tp) {
    return getType(tp@\loc);
}

// Note that all subscriptions are of the form X[{a}] to avoid that a is interpreted as an integer index.  
test bool subscription1(lrel[&A, &B, &C] X) =
  isEmpty(X) ||
  all(&A a <- domain(X), any(<&B b, &C c> <- X[{a}], <a, b, c> in X)) &&
  all(<&A a, &B b, &C c> <- X, <b, c> in X[{a}]);

test bool unicodeCharacterClassSubtype2() {
  Tree t = char(charAt("🍕", 0));

  if ([🍕] pizza := t) {
    assert [\a00-🍕] _ := pizza;
    assert NotAZ _ := pizza;
    return true;
  }

  return false;
}


@synsopsis{Defines three example commands that can be triggered by the user (from a code lens, from a diagnostic, or just from the cursor position)}
data Command
  = renameAtoB(start[Program] program)
  | removeDecl(start[Program] program, IdType toBeRemoved)
  ;

@synopsis{Adds an example lense to the entire program.}
lrel[loc,Command] picoCodeLenseService(start[Program] input)
    = [<input@\loc, renameAtoB(input, title="Rename variables a to b.")>];

            for (/(KeywordArgument[Expression]) `<Name n> = <Expression _>` := kwArgs) addFieldUse(e, n);

    visit (tr) {
        case (Expression) `<Expression e>(<{Expression ","}* _> <KeywordArguments[Expression] kwArgs>)`: {
            funcKwDefs = keywordFormalDefs[tm.useDef[e.src]];
            // Only visit uses of our keyword arguments - do not go into nested calls
            top-down-break visit (kwArgs) {
                case (KeywordArgument[Expression]) `<Name kw> = <Expression _>`: {
                    for (loc d <- funcKwDefs["<kw>"]) {
                        tm = tm[useDef = tm.useDef + <kw.src, d>];
                    }
                }
            }
        }
    }
	
            if (func has conditions) <tm, funcDefs> = augmentTypeParams(func.conditions, <tm, funcDefs>);
            if (func has expression) <tm, _> = augmentTypeParams(func.expression, <tm, funcDefs>);
            else if (func has body) <tm, _> = augmentTypeParams(func.body, <tm, funcDefs>);
			
			
private bool check(list[Actual] actuals, expectNth(n, string, tokenType)) {
    actuals = filterByString(actuals, string);
    assert [] != actuals[n..(n + 1)] : "Unexpected string: \"<string>\"";
    assert n >= 0 : "Expected `n` to be non-negative. Actual: `<n>`.";
    assert <<_, _, _, tokenType, _>, _, _> := actuals[n] : "Expected token type of \"<string>\": <tokenType>. Actual: <actuals[n].token.tokenType>.";
    return true;
}

syntax A = : /* C */ B;

module CFErrors

import util::ResourceMarkers;
import Message;
import IO;
import String;

public loc LOG = |home:///git/vallang/LOG11|;

int offset(loc file, int l) 
  = ( 0 | it + size(line) | line <- readFileLines(file)[..l-1]);

loc path(str path, str l, str c) {
  p = |project://vallang| + path;
  return p(offset(p, toInt(l)) + toInt(c), 1); 
}

set[Message] messages(loc log) 
  = { warning(m + "@<l>, <c>", path(p, l, c)) 
    | /\[ERROR\] .*\/git\/vallang\/<p:.*>:\[<l:[0-9]+>,<c:[0-9]+>\] <m:.*>$/ <- readFileLines(log) 
    };

void setCFerrors() {
  addMessageMarkers(messages(LOG));
}

void clearCFerrors() {
   removeMessageMarkers(|project://vallang/src|);
}


  return   "<license>
           '
           '// This code was generated by lang::cpp::ASTgen
           'package lang.cpp.internal;
           '
           'import io.usethesource.vallang.type.Type;
           'import io.usethesource.vallang.type.TypeFactory;
           'import io.usethesource.vallang.type.TypeStore;
           'import io.usethesource.vallang.*;
           'import java.util.Map;
           'import java.util.HashMap;
           '
           '@SuppressWarnings(\"deprecation\")
           'public class <apiName> {
           '  private static TypeStore typestore = new TypeStore();
           '  private static TypeFactory tf = TypeFactory.getInstance();
           '  private IValueFactory vf;
           '
           '  public <apiName> (IValueFactory vf) {
           '    this.vf = vf;
           '  }
           '
           '  <for(type[value] t <- allTypes, adt(str name, _) := t.symbol) {>private static final Type _<name> = tf.abstractDataType(typestore, \"<name>\");
           '  <}> 
           '  <for(type[value] t <- allTypes) {>
           '  <declareType(t.symbol, t.definitions[t.symbol])>
           '  <}>
           '  <for(type[value] t <- allTypes, t.symbol in t.definitions, choice(_,cs) := t.definitions[t.symbol]) {> 
           '  <declareMakers(t.symbol,cs)> <}>
           '  
           '}";


    // nothing in the AST that has a decl is not declared
    assert all(/node n := t && n.decl? && n.decl in decls);

    // all nodes have a .src attribute
    assert all(/node n := t && loc _ := n.src?|unknown:///|);

    // helper function for getting src location of a node
    loc \loc(node n) = loc f := (n.src?|unknown:///|(0,0)) ? f : |unknown:///|(0,0);
 
    // all sibling ast's are next to each other in the right order
    for(/[*_,node a, node b, *_] := t) {
        assert \loc(a).offset + \loc(a).length <= \loc(b).offset;
    }

// TODO: /regex/(param)
@synopsis{marks jump targets with the jumpTarget=true field, for later use by label removal and detection of structured statements}
list[Instruction] jumps([*Instruction pre, Instruction jump:/IF|GOTO|IFNULL|IFNONNULL|JSR/(str l1), *Instruction mid, LABEL(l1, jumpTarget=false), *Instruction post]) 
  = jumps([*pre, jump, *mid, LABEL(l1, jumpTarget=true), *post]);  
  
  
  
Stat stat(s:(Statement) 
                 `if <Expression cond> then 
                 '  <{Statement ";"}* thenPart> 
                 'else 
                 '  <{Statement ";"}* elsePart> 
                 'fi`)                
   = \if(ne(expr(cond), iconst(0)), stats(thenPart), stats(elsePart)) when /Id _ := thenPart;


@license{
Copyright (c) 2009-2025, NWO-I Centrum Wiskunde & Informatica (CWI)
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module Pre

import Prelude;

int calc(int y) = y * 2;

@license{
Copyright (c) 2009-2025, NWO-I Centrum Wiskunde & Informatica (CWI)
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module Example

import Pre;

// import IO;

int main() {
  str s = calc(3); // not a string!
  int x = "not an int";
  // println("println should be resolved by the MOJO somehow...");
  return x;
}

module Main

import String;
import IO;
import List;
import Location;
import util::Reflective;
import util::SystemAPI;
import util::FileSystem;
import analysis::graphs::Graph;
import util::ShellExec;
import util::Benchmark;

data Project
    = project(
        loc repo, // git clone url
        set[str] dependencies, // other project this depends on (at a rascal level)
        bool rascalLib=false, // instead of rascal as a regular "project" dependency, us the tpls that came with the chosen rascal-version
        str branch="main", // branch to checkout from the remote
        str subdir="", // if the rascal project is not at the root of the repo
        list[str] srcs = [], // override source calculation
        set[str] ignores = {} // directories to ignore
    );

alias Projects = rel[str name, Project config];

Projects projects = {
    <"rascal", project(|https://github.com/usethesource/rascal.git|, {}, branch="compiled-parser-generator", srcs = ["src/org/rascalmpl/library"], ignores={"experiments", "resource", "lang/rascal/tests", "lang/rascal/syntax/test"})>,
    <"rascal-all", project(|https://github.com/usethesource/rascal.git|, {}, branch="compiled-parser-generator")>,
    <"typepal", project(|https://github.com/usethesource/typepal.git|, {"rascal"}, ignores={"examples"})>,
    <"typepal-boot", project(|https://github.com/usethesource/typepal.git|, {}, rascalLib=true, ignores={"examples"})>,
    <"salix-core", project(|https://github.com/usethesource/salix-core.git|, {"rascal"})>,
    <"salix-contrib", project(|https://github.com/usethesource/salix-contrib.git|, {"rascal", "salix-core"})>,
    <"flybytes", project(|https://github.com/usethesource/flybytes.git|, {"rascal"})>,
    <"drambiguity", project(|https://github.com/cwi-swat/drambiguity.git|, {"rascal", "salix-core"})>,
    <"rascal-git", project(|https://github.com/cwi-swat/rascal-git.git|, {"rascal"})>,
    <"php-analysis", project(|https://github.com/cwi-swat/php-analysis.git|, {"rascal", "rascal-git"})>,
    <"rascal-lsp-all", project(|https://github.com/usethesource/rascal-language-servers.git|, {"rascal-all"}, subdir="rascal-lsp", srcs=["src/main/rascal/library","src/main/rascal/lsp"])>,
    <"rascal-lsp", project(|https://github.com/usethesource/rascal-language-servers.git|, {"rascal"}, srcs=["src/main/rascal/library"], subdir="rascal-lsp")>
};

bool isWindows = /win/i := getSystemProperty("os.name");

str buildFSPath(loc l) {
    l = resolveLocation(l);
    if (l.scheme != "file") {
        throw "Only file schemes are supported, <l> is invalid";
    }
    path = l.path;
    if (isWindows) {
        // for windows we have to flip the \\ and remove the prefix /
        if (startsWith(path, "/")) {
            path = path[1..];
        }
        path = replaceAll(path, "/", "\\");
    }
    return path;
}

str buildCP(loc entries...) = intercalate(getSystemProperty("path.separator"), [ buildFSPath(l) | l <- entries]);



loc tplPath(loc repoFolder, str name) = (repoFolder + name) + "target/classes";

loc projectRoot(loc repoFolder, str name, Project proj) = (repoFolder + name) + proj.subdir;


tuple[list[loc], list[loc]] calcSourcePaths(str name, Project proj, loc repoFolder) {
    srcs = proj.srcs != [] ? [projectRoot(repoFolder, name, proj) + s |  s <- proj.srcs ] : getProjectPathConfig(projectRoot(repoFolder, name, proj)).srcs;
    ignores = [ s + i |  s<- srcs, s.scheme != "jar+file",  i <- proj.ignores];
    return <srcs, ignores>;
}

PathConfig generatePathConfig(str name, Project proj, loc repoFolder, false) {
    <srcs, ignores> = calcSourcePaths(name, proj, repoFolder);
    for (str dep <- proj.dependencies, <dep, projDep> <- projects) {
        <nestedSrcs, nestedIgnores> = calcSourcePaths(dep, projDep, repoFolder);
        srcs += nestedSrcs;
        ignores += nestedIgnores;
    }
    return pathConfig(
        projectRoot = projectRoot(repoFolder, name, proj),
        srcs = srcs,
        ignores = ignores,
        bin = repoFolder + "shared-tpls",
        libs = [repoFolder + "shared-tpls"] + (proj.rascalLib ? [|std:///|] : [])
    );
}
PathConfig generatePathConfig(str name, Project proj, loc repoFolder, true) {
    <srcs, ignores> = calcSourcePaths(name, proj, repoFolder);
    result = pathConfig(
        projectRoot = projectRoot(repoFolder, name, proj),
        srcs = srcs,
        ignores = ignores,
        bin = tplPath(repoFolder, name),
        libs = [ tplPath(repoFolder, dep) | dep <- proj.dependencies ] + (proj.rascalLib ? [|std:///|] : [])
    );
    /*
    if (name == "rascal-lsp-all" || name == "rascal-all") {
        // we have to add typepal to the lib path
        rascalPcfg = getProjectPathConfig(repoFolder + "rascal-all");
        result.libs += [l | l <- (rascalPcfg.srcs + rascalPcfg.libs), l.scheme == "mvn", /typepal/ := l.authority];
        if (name == "rascal-all") {
            // and remove typepal from the srcs
            result.srcs = [s | s <- result.srcs, s.scheme != "mvn", /typepal/ !:= s.authority];
        }
    }
    */
    return result;
}

int updateRepos(Projects projs, loc repoFolder, bool full) {
    int result = 0;
    void checkOutput(str name, <str output, int exitCode>) {
        if (exitCode != 0) {
            result += 1;
            println("!!<name> failed: ");
            println(output);
        }
    }
    for (<n, proj> <- projs) {
        targetFolder = repoFolder + n;
        if (exists(targetFolder)) {
            println("**** Updating <n>");
            checkOutput("fetch", execWithCode("git", args=["fetch"], workingDir=targetFolder));
            checkOutput("reset", execWithCode("git", args=["reset", "--hard", "origin/<proj.branch>"], workingDir=targetFolder));
        }
        else {
            println("**** Cloning <n>");
            extraArgs = full ? [] : ["--single-branch", "--branch", proj.branch, "--depth", "1"];
            checkOutput("clone", execWithCode("git", args=["clone", *extraArgs, proj.repo.uri, n], workingDir=repoFolder));
        }
    }
    return result;
}

bool isIgnored(loc f, list[loc] ignores)
    = size(ignores) > 0 && any(i <- ignores, relativize(i, f) != f);


int main(
    str memory = "4G",
    bool libs=true, // put the tpls of dependencies on the lib path
    bool update=false, // update all projects from remote
    bool full=true, // do a full clone
    bool clean=true, // do a clean of the to build folders
    loc repoFolder = |tmp:///repo/|,
    loc rascalVersion=|home:///.m2/repository/org/rascalmpl/rascal/0.41.0-RC46/rascal-0.41.0-RC46.jar|,
    set[str] tests = {/*all*/}
    ) {
    mkDirectory(repoFolder);
    int result = 0;
    toBuild = (tests == {}) ? projects : { p | p <- projects, p.name in tests};

    if (update || any(<n, _> <- toBuild, !exists(repoFolder + n))) {
        println("*** Downloading repos ***");
        result += updateRepos(toBuild, repoFolder, full);
        if (result > 0) {
            return result;
        }
    }
    else {
        println("Not downloading any dependencies");
    }


    // calculate topological order of dependency graph)
    buildOrder = order({ *(proj.dependencies * {n}) | <n, proj> <- projects, proj.dependencies != {}});
    println("*** Calculate dependency based build order: <buildOrder>");
    // filter out things that weren't requested (so we assume already build)
    buildOrder = [p | p <- buildOrder, p in toBuild.name] ;
    // and also add stuff not part of the graph (projects without any depencencies or dependants)
    buildOrder += [p.name | p <- toBuild, p.name notin buildOrder];
    println("*** Actually building: <buildOrder>");

    // prepare path configs
    println("*** Calculating class paths");
    pcfgs = [<n, generatePathConfig(n, proj, repoFolder, libs)> | n <- buildOrder, proj <- toBuild[n]];


    if (clean) {
        for (<_, p> <- pcfgs) {
            for (f <- find(p.bin, "tpl")) {
                remove(f);
            }
        }
    }

    result = 0;

    lrel[str, int, int] stats = [];

    for (n <- buildOrder, proj <- toBuild[n]) {
        println("*** Preparing: <n>");
        p = generatePathConfig(n, proj, repoFolder, libs);
        if (clean) {
            for (f <- find(p.bin, "tpl")) {
                remove(f);
            }
        }
        println(p);
        loc projectRoot = repoFolder + n;
        rProjectRoot = resolveLocation(projectRoot);
        rascalFiles = [*find(s, "rsc") | s <- p.srcs, (startsWith(s.path, projectRoot.path) || startsWith(s.path, rProjectRoot.path))];
        rascalFiles = sort([f | f <- rascalFiles, !isIgnored(f, p.ignores)]);
        println("*** Starting: <n> (<size(rascalFiles)> to check)");
        startTime = realTime();
        runner = createProcess("java", args=[
            "-Xmx<memory>",
            "-Drascal.monitor.batch", // disable fancy progress bar
            "-Drascal.compilerClasspath=<buildFSPath(rascalVersion)>",
            "-cp", buildFSPath(rascalVersion),
            "org.rascalmpl.shell.RascalCompile",
            "-srcs", *[ "<s>" | s <- p.srcs],
            *["-libs" | p.libs != []], *[ "<l>" | l <- p.libs],
            "-bin", "<p.bin>",
            "-modules", *[ "<f>" | f <- rascalFiles]
        ]);
        try {
            while (isAlive(runner)) {
                stdOut = readWithWait(runner, 500);
                if (stdOut != "") {
                    print(stdOut);
                }
                stdErr = readFromErr(runner);
                while (stdErr != "") {
                    println(stdErr);
                    stdErr = readFromErr(runner);
                }
            }
            stopTime = realTime();
            println(readEntireStream(runner));
            println(readEntireErrStream(runner));
            code = exitCode(runner);
            result += code;
            println("*** Finished: <n> < code == 0 ? "✅" : "❌ Failed"> (<(stopTime - startTime)/1000>s)");
            stats += <n, code, (stopTime - startTime)/1000>;
        }
        catch ex :{
            println("Running the runner for <n> crashed with <ex>");
            result += 1;
        }
        finally {
            killProcess(runner);
        }
    }
    println("******\nDone running ");
    for (<n, e, t> <- stats) {
        println("- <n> <e == 0 ? "✅" : "❌"> <t>s");
    }
    return result;
}

// TODO:
str prettyAType(Keyword kw: kwField(fieldType, fieldName, _,defaultExp)) = "<prettyAType(fieldType) <fieldName> = <defaultExp>";
str prettyAType(Keyword kw: kwField(fieldType,fieldName, _)) = "<prettyAType(fieldType) <kw.fieldName> = ?";


private Controller renameEvent(Controller ctl, Id oldName, Id newName) {
  // DOES NOT WORK: parse trees are not enumerable?
  if (/Event e <- ctl, e.name == newName) {
    alert("Event <newName> already exists");
    return ctl;
  } 
  return visit (ctl) {
    case Transition t: {
      if (oldName == t.event) {
        t.event = newName;
      }
      insert t;
    }
    case Event e: {
      if (oldName == e.name) {
        e.name = newName;
      }
      insert e;
    }
    case ResetEvents rs => visit (rs) {
      case Id i => newName when oldName == i 
    }
  }
}


@doc{annotates each tree iff it contains a newline}
Tree markVertical(Tree t) {
  return visit (t) {
     case Tree u:appl(_,[*_, Tree v, *_]) : if (v@vertical?false) insert u[@vertical=true]; else fail;
     case Tree u:amb({*_, Tree v})    : if (v@vertical?false) insert u[@vertical=true]; else fail;
     case char(10) : return t[@vertical=true];
     case Tree u   : return u[@vertical=false];
  }
}

// repl view generator (helper)
void(REPLModel) repl(str id, value vals...) 
  =  void(REPLModel _) { xterm(id, [onData(xtermData)] + vals); }; 


void print(reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0] ? "no dependencies">");
    if(full) printDeps(dependsOn, indent, facts);
}

    //@memo
    AType solver_getType(value v){
        try {
            switch(v){
                case Tree tree:   return instantiate(findType(tree@\loc));
                case tvar(loc l): return facts[l];
                case AType atype: return instantiate(atype);
                case loc l:       return l in specializedFacts ? specializedFacts[l] : facts[l];
                case defType(value v) : if(AType atype := v) return atype; else if(Tree tree := v) return instantiate(findType(tree@\loc));
                case Define def:  return solver_getType(def.defInfo);
                case defTypeCall(list[loc] _, AType(Solver s) getAType):
                    return getAType(thisSolver);
                case defTypeLub(list[loc] _, list[loc] _, list[AType(Solver s)] getATypes):
                    return solver_lubList([getAType(thisSolver) | AType(Solver s) getAType <- getATypes]); //throw "Cannot yet handle defTypeLub in getType";
                default:
                    throw "getType cannot handle <v>";
            }

        } catch NoSuchKey(_):
           throw TypeUnavailable();
        throw "getType cannot return type for <v>";
    }


void collect(current: (Expression) `<Expression exp1> in <Expression exp2>`, Collector c){
    c.calculate("relational operator", current, [exp1, exp2], 
        AType(Solver s) { 
            switch([s.getType(exp1), s.getType(exp2)]){
                case [tau1, setType(tau2)]: if(pascalIsSubType(tau1, tau2)) return booleanType(); else fail;
                default:{
                    s.report(error(current, "`in` not defined on %t and %t", exp1, exp2));  
                    return voidType();
                  }
            }
        });
     collect(exp1, exp2, c);
}



            // if(getName(currentTree.prod.def.symbol) == "lex")  collectArgs1(currentTree.args, c); else collectArgs2(currentTree.args, c);


private MuExp translateStringLiteral(s: (StringLiteral) `<PreStringChars pre> <Expression expression> <StringTail tail>`) {
    preIndent = computeIndent(pre);
    return muBlock( [ muCallPrim3("template_open", translatePreChars(pre), pre@\loc),
    				  *translateExpInStringLiteral(preIndent, expression),
    				  *translateTail(preIndent, tail),
    				  muCallPrim3("template_close", [], tail@\loc)
					]   );
}



// comment 1

n = 1;  // comment 3
l = [1, // comment 3: non highlighted
     2, 
     3];


start[Program] addDeclarationToMiddle(start[Program] p) = visit(p) {
    case (Program) `begin declare <{IdType ","}* pre>, <IdType middle>, <{IdType ","}* post>; <{Statement  ";"}* body> end`
        => (Program) `begin
                     '  declare
                     '    <{IdType ","}* pre>,
                     '    <IdType middle>,
                     '    middle : natural,
                     '    <{IdType ","}* post>;
                     '  <{Statement  ";"}* body>
                     'end`
};

start[Program] addDeclarationToMiddle(start[Program] p) = visit(p) {
    case (Program) `begin declare <{IdType ","}+ pre>, <IdType middle>, <{IdType ","}+ post>; <{Statement  ";"}* body> end`
        => (Program) `begin
                     '  declare
                     '    <{IdType ","}+ pre>,
                     '    <IdType middle>,
                     '    middle : natural,
                     '    <{IdType ","}+ post>;
                     '  <{Statement  ";"}* body>
                     'end`
};

loc working = |scheme://normal/as/it/should/be|;
loc broken = |scheme://with-dashes-in-authority/breaks/it|;


@license{
  BSD-2 License
}
module A

@doc{
   Textile markup for the documentation
}
@javaClass{org.rascalmpl.library.X}
public java str doStuff(int x);


int main(
	list[loc] modules = [],
	list[loc] libs = []) {
}

main(#Foo, "source.foo", |home:///Desktop/foo.json|)

// FOO:
/*/
