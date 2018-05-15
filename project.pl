
% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
% 		1.1 Reading an input string and convert it to a tokenized list
% 		1.2 Processing tokenized list
% ===========================================================

chat:-
 repeat,
   readinput(Input),
   process(Input),
  (Input = [bye| _] ),!.


% ===========================================================
% Read input:
% 1. Read char string from keyboard.
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
	parse(Input,SemanticRepresentation),
	modelchecker(SemanticRepresentation,Evaluation),
	respond(Evaluation),!,
	nl,nl.

process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

%parse(Input, SemanticRepresentation):-
% ...

sr_parse(Sentence):-
        srparse([],Sentence).

srparse([X],[]):-
  numbervars(X,0,_),
  write(X).

srparse([Y,X|MoreStack],Words):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words).

srparse([X|MoreStack],Words):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words).

srparse(Stack,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],Words).


% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================

% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------

% determiners
lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).
lemma(the,dtforthe).
lemma(no,dtfornone).

% this, these     %%


% Proper noun
lemma(tom,pn).
lemma(mia,pn).
lemma(sue,pn).
lemma(john,pn).

% noun
lemma(box, n).
lemma(burger, n).
lemma(container, n).
lemma(ham, n).
lemma(freezer, n).
lemma(egg, n).
lemma(bowl, n).
lemma(shelf, n).
lemma(sandwich, n).
lemma(meat, n).
lemma(banana, n).
lemma(bowl, n).
lemma(fridge, n).
lemma(milk, n).
lemma(book, n).
lemma(mango,n).
lemma(watermelon,n).
lemma(apple,n).
lemma(chocolate,n).
lemma(popsicle,n).
lemma(bread,n).

% be
lemma(is,be).
lemma(was,be).
lemma(are,be).
lemma(has,be).

% tv
lemma(eat, tv).
lemma(contain, tv).
lemma(arrive, iv).
lemma(belong, tv).
lemma(inside, tv).
lemma(put, tv).
lemma(read, iv).
lemma(drink,tv).

% p
lemma(in,p).
lemma(under,p).
% lemma(on,p).
% lemma(to,p).
% lemma(of,p).

% vacp
lemma(on,vacp).
lemma(to,p).
lemma(of,vacp).
lemma(at,vacp).
lemma(inside,vacp).

% aux
lemma(can,aux).
lemma(do, aux).
lemma(does, aux).
lemma(will, aux).
lemma(did, aux).
lemma(are,aux).
lemma(is,aux).

% whpr - Interogative Person
lemma(who,whpr).
lemma(whose,whpr).

lemma(what,whpr).
% lemma(what,what) %%

% whth - Interogative Thing
% lemma(which,whth).
lemma(which,which).

% adj
lemma(red,adj).
lemma(two,adj).
lemma(white,adj).
lemma(blue,adj).
lemma(green,adj).
lemma(black,adj).
lemma(orange,adj).
lemma(red,adj).
lemma(yellow,adj).
lemma(top,adj).
lemma(above,adj).
lemma(middle,adj).
lemma(bottom,adj).
lemma(empty,adj).
lemma(almond,adj).
lemma(two,adj).

% rel
lemma(that,rel).

% neg
lemma(not,neg).

% there
lemma(there,there).

% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------

removeLast([X|Xa], Y) :-
  removeLastPrev(Xa, Y, X).

removeLastPrev([], [], _).
removeLastPrev([X1|Xa], [X2|Y], X2) :-
  removeLastPrev(Xa, Y, X1).

checkWord([]).
checkWord(Word,OLemma):-
  removeLast(Word, RemovedLastList),
  atom_chars(OLemma, RemovedLastList).

lexi(Word,Stem) :- lemma(Word, _),Stem = Word,!;
      atom_chars(Word, Listword),
      checkWord(Listword, NewWord),
      lexi(NewWord,Stem).

% Lex for n
lex(n(X^P),Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,n),
	P=.. [Stem,X].

% Lex for tv
lex(tv(X^Y^P), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,tv),
  P=.. [Stem, X,Y].

% Lex for iv
lex(iv(X^P), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,iv),
	P=.. [Stem,X].

% Lex for dt
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):- lemma(Word,dtforall).
lex(dt((X^P)^(X^Q)^exists(X,imp(P,Q))),Word):- lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^the(X,imp(P,Q))),Word):- lemma(Word,dtforthe).

% Lex for adj
lex(adj((X^P)^X^and(P,Q)), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,adj),
  Q=.. [Lemma, X].

% Lex for pn
lex(pn(P^X), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,pn),
	P= (Stem^X).

% Lex for aux
lex(aux, Lemma):-
	lemma(Lemma, aux).

% Lex for p
lex(p((Y^Z)^Q^(X^P)^and(P,Q)), Lemma):-
  lemma(Lemma, p),
  Z=.. [Lemma, X].

% Lex for who - Interogative Person
lex(whpr((X^P)^exists(X,and(person(X),P))),Word):-
  lemma(Word,whpr).

% Lex for which - Interogative Thing
lex(whth((X^P)^exists(X,and(thing(X),P))),Word):-
  lemma(Word,whth).

% Lex for Rel
lex(rel(P^P),Word):-
	lemma(Word,rel).

% Other lex
lex(pn((tom^X)^X),tom).
lex(pn((sue^X)^X),sue).

lex(n(X^bus(X)),bus).
lex(n(X^weapon(X)),weapon).
lex(n(X^passenger(X)),passenger).
lex(n(X^man(X)),man).

lex(adj((X^P)^X^and(P,blue(X))),blue).
lex(adj((X^P)^X^and(P,old(X))),old).
lex(adj((X^P)^X^and(P,illegal(X))),illegal).

lex(iv(X^sneezed(X)),sneezed).
lex(tv(X^Y^saw(X,Y)),saw).
lex(tv(X^Y^have(X,Y)),had).

lex(X,drank):-lex(X,drink).
lex(X,drunk):-lex(X,drink).

% ...

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

% N -> ADJ N
rule(n(Y),[adj(X^Y),n(X)]).

% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).

% N -> N RC
rule(n(X^Z),[n(X^Y),rc((X^Y)^Z)]).    %%

% NP -> PN
rule(np(X),[pn(X)]).

% NP -> N
rule(np(X),[n(X)]).

% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).

% VP -> TV NP
rule(vp(X^W),[tv(X^Y),np(Y^W)]).

% VP -> IV      % rule()
rule(vp(X),[iv(X)]).

% VP -> AUX VERB
rule(vp(X),[aux(X)]).   %%

% VP -> AUX VP
rule(vp(X^Y,[]),[aux(_),vp(X^Y,[])]).
% rule(vp(X^Y),[aux(X),vp(X^Y)]).

% S -> NP VP
rule(s(Y),[np(X^Y),vp(X)]).

% Questions
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).

rule(Y,[whpr(X^Y),vp(X,[])]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

% RC -> NP REL VP                      %%
rule(rc(Y),[np(X^Y),rel,vp(X,[])]).


% ...


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================


model([a,b,c,r],
           [ [cat, [a,b]], [dog,[c]], [die, [c,r,d]], [chase, [ [a,b], [c,a], [c,b] ]] ]).



% ==================================================
% Function i
% Determines the value of a variable/constant in an assignment G
% ==================================================

i(Var,G,Value):-
    var(Var),
    member([Var2,Value],G),
    Var == Var2.

i(C,_,Value):-
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a Predicate/Relation
% ==================================================

f(Symbol,Value):-
   model(_,F),
    member([Symbol,ListOfValues],F),
    member(Value,ListOfValues).


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).


% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).


% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value),
   \+ ( ( sat(G1,exists(X,A),G2), i(X,G2,Value2), \+(Value = Value2)) ).




% ==================================================
% Negation
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).

% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2),
  sat(G2,Formula2,G3).


% ==================================================
% Disjunction
% ==================================================


sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% ==================================================

sat(G,Predicate,G):-
   Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).

% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :-
		Evaluation = [true_in_the_model],
		write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :-
		Evaluation = [not_true_in_the_model],
		write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :-
		Evaluation = [yes_to_question],
		write('yes').

% Yes-No interrogative false in the model
respond(Evaluation) :-
		Evaluation = [no_to_question],
		write('no').

% wh-interrogative true in the model
% ...

% wh-interrogative false in the model
% ...
