
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

parse(Input, SemanticRepresentation):-
  srparse([], Input, SemanticRepresentation).
%sr_parse(Sentence):-
%        srparse([],Sentence).

srparse([X],[], X):-
  numbervars(X,0,_),
  write(X).

srparse([Y,X|MoreStack],Words,Parse):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words,Parse).

srparse([X|MoreStack],Words,Parse):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words,Parse).

srparse(Stack,[Word|Words],Parse):-
        lex(X,Word),
        srparse([X|Stack],Words,Parse).

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

lemma(what,whth).
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




removeLast([X|Xa], Y) :-
  removeLastPrev(Xa, Y, X).

removeLastPrev([], [], _).
removeLastPrev([X1|Xa], [X2|Y], X2) :-
  removeLastPrev(Xa, Y, X1).

checkWord([]).
checkWord(Word,OLemma):-
  removeLast(Word, RemovedLastList),
  atom_chars(OLemma, RemovedLastList).


% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------



% --------------------------------------------------------------------

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
lex(tv(X^Y^P,[]), Lemma):-
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
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),a).
lex(dt((X^P)^(X^Q)^exists(X,imp(P,Q))),Word):- lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^exists(X,imp(P,Q))),Word):- lemma(Word,dtforthe).

% Lex for adj
lex(adj((X^P)^X^and(P,Q)), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,adj),
  Q=.. [Stem, X].

% Lex for pn
lex(pn(P^X), Lemma):-
  lexi(Lemma, Stem),
	lemma(Stem,pn),
	P= (Stem^X).
\
% Lex for aux
lex(aux, Lemma):-
	lemma(Lemma, aux).

% Lex for p
lex(p((Y^Z)^Q^(X^P)^and(P,Q)), Lemma):-
  lemma(Lemma, p),
  Z=.. [Lemma, X].

% Lex for who - Interogative Person
lex(whpr((X^P)^q(X,and(person(X),P))),Word):-
  lemma(Word,whpr).

% Lex for which - Interogative Thing
lex(whth((X^P)^q(X,and(thing(X),P))),Word):-
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
lex(tv(X^Y^saw(X,Y),[]),saw).
lex(tv(X^Y^have(X,Y,[])),had).

lex(X,drank):-lex(X,drink).
lex(X,drunk):-lex(X,drink).

% ...+++++++++++++++++++++++++++++++++++++++++++++

lex(not(P^P),Word):-
	lemma(Word,neg).

lex(rel(P^P),Word):-
	lemma(Word,rel).

lex(whth((X^P)^exists(X,and(thing(X),P))),Word):-
	lemma(Word,whth).

% lex(what((X^P)^(X^Q)^exists(X,and(P,Q)),[X]),Word):-
	% lemma(Word,what).

lex(ve(P^P),Word):-
	lemma(Word,be).

lex(vacp(P^P),Word):-
	lemma(Word,vacp).

lex(there(P^P),Word):-
	lemma(Word,[]).

lex(aux,Lemma):-
	lemma(Lemma,aux).

lex(vacp((Y^in(X,Y))^Q^(X^P)^and(P,Q)),Word):-
                lemma(Word,vacp).

lex(dt((X^P)^(X^Q)^not(exists(X,P^Q))),Word):-
                lemma(Word,dtfornone).

lex(whth((X^P)^exists(X,and(thing(X),P))),Word):-
  lemma(Word,whth).

lex(whpr((X^P)^q(X,and(person(X),P))),Word):-
  lemma(Word,whpr).

lex(rel(P^P),Word):-
	lemma(Word,rel).

lex(rel(P^P),Word):-
	lemma(Word,rel).

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

rule(s(B),[np(A^B),vp(A)]).
rule(s(Y,WH),[np(X^Y),vp(X,WH)]). % original
rule(s(Y), [np(Y),vp(Y)]). %%%%
rule(s(X,[WH]),[vp(X,[WH])]).

% S -> NP VP
rule(s(Y),[np(X^Y),vp(X)]).
% NP -> PN
rule(np(X),[pn(X)]).
% NP -> N
% rule(np(A),[n(A^C)]).

rule(np(X),[n(X)]).
% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).
% N -> ADJ N
rule(n(Y),[adj(X^Y),n(X)]).
% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).




rule(vp(X^Y,[]),[aux(_),vp(X^Y,[])]).
% rule(vp(X^not(Y),[]),[not(_),vp(X^Y,[])]).
% VP -> TV NP
% rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(A^D,[]),[tv(A^C^D,[]),np(C^B)]).

% VP -> IV      % rule()
rule(vp(X),[iv(X)]).
% VP -> AUX VERB
% rule(vp(X),[aux(X)]).   %%



% S -> Aux NP VP
% S -> VP
% S -> Wh-NP VP          : Which, What, Whose
% S -> Wh-NP Aux NP VP
% S -> BE NP AP
% S -> BE NP PP
% S -> BE NP NP
% RC -> NP REL VP






% N -> N RC
% rule(n(X^Z),[n(X^Y),rc((X^Y)^Z)]).    %%

% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

% RC -> NP REL VP                      %%
rule(rc(Y),[np(X^Y),rel,vp(X,[])]).

% VP -> TV WHPR
% rule(vp(X^W),[whpr((X^Y)^W),tv(X^Y)]).

rule(Y,[whpr(X^Y),vp(X,[])]).

% rule(q(A),[exists(A,and(person(A),saw(A,tom))),who()]).
% rule(q(X),[whpr((X^P)^exists(X,and(person(X),P)))]).

% change

rule(vp(A^D,[]),[tv(A^C^D,[]),np(C^B)]).

% lex(A,who), lex(B,saw), lex(C,tom), rule(D,[A,B]), rule(E,[C])., rule(F,[D,E]).
% D = vp(A^exists(A, and(person(A), B^saw(A, B))))
rule(iv(X,[Y]),[tv(X^Y,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).


% A = dt((_10246^ham(_10246))^(_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))),
% B = n(_10246^ham(_10246)),
% L = [dt((_10246^ham(_10246))^(_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))), n(_10246^ham(_10246))],
% X = np((_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))) ;

% rule(np((X^some)^exists(X, imp(P, some))), [dt((P)^(X^some)^exists(X, imp(P, some))), n(P)]).
% rule(np((_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))), n(P)).

% rule(np(X^Y),[lex(Y,some),n(X)]).

% rule(np(Y),[tv(X^Y),lex(Y,some),n(X)]).
% ?- sr_parse([ham]).
% n(A^ham(A))
% true .

% ?- sr_parse([some, ham]).
% np((A^B)^exists(A,imp(ham(A),B)))
% true .

% ?- sr_parse([some]).
% dt((A^B)^(A^C)^exists(A,imp(B,C)))

% S -> VP
% rule(s(X,[wh]),[vp(X,[wh])]).

 %rule(np(X),[n(X)]).  :- lex(A,some).
%rule(np(A),lex(dt((X^P)^(X^Q)^exists(X,imp(P,Q))),Some), n(B)).
% rule(np(Y),[X^some(Y),n(X)]).
% ...

rule(rs(Y,[WH]),[np(X^Y),vp(X,[WH])]).
rule(rc(X^Y,[]),[rel(_),vp(X^Y,[])]).
rule(rc(P,[K]),[rel(_),rs(P,[K])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================



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
