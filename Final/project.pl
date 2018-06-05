
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
    numbervars(X,0,_).

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
% lemma(inside, tv).
lemma(put, tv).
lemma(read, iv).
lemma(drink,tv).

% p
lemma(in,p).
lemma(under,p).
lemma(on,p).
% lemma(to,p).
% lemma(of,p).

% vacp
% lemma(on,vacp).
lemma(to,to).
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
lemma(one,adj).
lemma(two,adj).
lemma(three,adj).
lemma(four,adj).
lemma(five,adj).
lemma(six,adj).
lemma(seven,adj).
lemma(eight,adj).
lemma(nine,adj).
lemma(ten,adj).

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
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),an).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),some).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),each).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),every).
lex(dt((X^P)^(X^Q)^the(X,(and(P,Q)))),the).
lex(dt((X^P)^(X^Q)^exists(X,imp(P,Q))),Word):- lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^the(X,imp(P,Q))),Word):- lemma(Word,dtforthe).

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
lex(whth(q(X,and(thing(X),P))),Word):-
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
% lex(tv(X^Y^contain(X,Y,[])),inside).
lex(X,inside):-lex(X,contain).

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

lex(be(P^P),Word):-
	lemma(Word,be).

lex(vacp(P^P),Word):-
	lemma(Word,_).

lex(there(P^P),Word):-
	lemma(Word,_).

lex(to(P^P),Word):-
    lemma(Word,_).

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


% NP -> PN
rule(np(X),[pn(X)]).
% rule(np(X^Y),[n(X)]). change
rule(np(X),[n(X)]).
% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).
% rule(np(B),[to(A^A),pn(B^B]).


% N -> ADJ N
rule(n(Y),[adj(X^Y),n(X)]).
% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).


rule(temp(belong(P,sue)),[tv(X^Y^Z, []),pp(A)]).
rule(temp(Z^A),[tv(X^Y^Z, []),pp(A)]).

rule(vp(X^Y),[aux(_),vp(X^Y,[])]).
% VP -> IV      % rule()
rule(vp(X),[iv(X)]).
rule(vp(X^Z),[tv(X^Y^Z, [])]). % change
rule(vp(X),[tv(X^Y),n(X^Y)]).


rule(vp(A^exists(B,and(C,D)),[]),[tv(A^B^D,[]),np((B^A)^exists(B,and(C,A)))]).
rule(vp(A^exists(B,and(E,D)),[]),[tv(A^B^D,[]),np((B^E))]).
rule(iv(X^Z, [Y]), [tv(X^Y^Z, [])]). % change
rule(tv(Y^Z, [X]), [tv(X^Y^Z, [])]). % change


rule(vp(Z^belong(B,sue)),[tv(X^Y^Z, []),temp(belong(P,sue))]).


% lex(A,what), lex(B,does), lex(C,tom)

rule(ynq(Y),[aux, np(X^Y),vp(X^Z)]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
% rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).
rule(inv_s(Y,[WH]),[aux, s(X,[WH])]).

% np((A^B)^the(A, and(and(box(A), white(A)), B)))
%pp
rule(pp(A),[vacp(P),np(A)]).
% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).



rule(rs(Y,[WH]),[np(X^Y),vp(X,[WH])]).
rule(rc(X^Y,[]),[rel(_),vp(X^Y)]).
rule(rc(P,[K]),[rel(_),rs(P,[K])]).
% RC -> NP REL VP                      %%
rule(rc(Y),[np(X^Y),rel,vp(X)]).

rule(np(Y^A^B), [rc(A^B^Y),np(A^B)]).
rule(rc(Y),[np(X^Y),rel(A)]).


%questions
rule(q(J,and(Y,forall(A,imp(P,the(C,O,put(J,A,C)))))),  [q(J, and(Y, put(J, W))),np((A^B)^forall(A, imp(and(P, the(C, and(O, K))), B)))]).

rule(Y,[whpr(X^Y),vp(X)]).
% rule(Y, [whth(X^Y),aux,np(X,[]),vp(X,[])]).
rule(qp(Y), [(whth(Y)),aux]).
rule(A^Y, [qp(A), s(Y)]).

rule(qp1(A),[be(A^A),there(A^A)]).

rule(qp1(A),[be(A^A),there(A^A)]).
rule(ynq(B),[qp1(A),s(B,[])]).
rule(ynq(B),[qp1(A),n(B)]).
rule(ynq(A^B^C),[qp1(A),np(B^C)]).
% rule()
rule((A^C^D), [qp(A^B),np(C^D^E)]).
% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================


is_a(ham(X), meat(X)).
is_a(box(X), blue(X)).
is_a(box(X), white(X)).
is_a(box(X), green(X)).
is_a(box(X), yellow(X)).
is_a(bowl(X), white(X)).
is_a(shelf(X), top(X)).
is_a(shelf(X), middle(X)).
is_a(shelf(X), bottom(X)).


model([p1, p2, box, m, m1, m2, c1, c2, c3, b1, b2, b3, b4, b5, b6, b7, h, f, e1, e2, sh1, sh2, sh3, fb, f1, f2, f3, w1, w2, fr],
  [sue, [p1]],
  [person, [p1, p2]],
  [fridge, [fr]],
  [milk, [m1, m2]],
  [sandwich, [sd1, sd2, sd3, sd4]],
  [container, [c1, c2,c3]],
  [watermelon, [w1, w2]],
  [box, [b1, b2, b4, b5, b6]],
  [bowl, [b3, b7]],
  [ham, [h]],
  [meat, m],
  [fruitbasket, [fb]],
  [banana, [f1, f2]],
  [apple, [f2]],
  [grapes, [f3]],
  [blue, [b1,b2,c1]],
  [white, [b3, b4, c1, c2]],
  [freezer, [f]],
  [popsicle, [box]],
  [belongs, [b4, n1]],
  [egg, [e1, e2]],
  [inside, [e1,b2], [e2,b2]],
  [shelf, [s1,s2,s3]],
  [green, [b5]],
  [yellow, [b6, b7]],
  [on, [b3, b6], [b4, b6], [c1,s1], [b7, s2]],
  [contain, [b1,h], [f,b4], [fb,f1], [fb,f2], [fb,f3], [s3,f1], [c2,f1], [c3,f2], [sd1, m], [sd2, m]],
  [in, [fr,w1], [fr, w2], [fr, w3], [fr, m], [box, f]],
  [almond, [m2]],
  [drink, [p1, m1], [p1, m2]]).

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = s(X,[]),Evaluation=[true_in_the_model].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = s(Declaration,[]),sat([],Declaration,_),Evaluation=[true_in_the_model].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = s(_,[]),Evaluation=[not_true_in_the_model].

modelchecker(SemanticRepresentation,Evaluation):-
    writeln(X),
    SemanticRepresentation = ynq(X),Evaluation=[yes_to_question].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = ynq(YesorNo),sat([],YesorNo,_),Evaluation=[yes_to_question].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = ynq(_),Evaluation=[no_to_question].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = q(X),Evaluation=[yes_to_question].

modelchecker(SemanticRepresentation,Evaluation):-
    SemanticRepresentation = q(_),Evaluation=[no_to_question].


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
           is_a(Result, Formula),
           extend(G1,X,G2),
           sat(G2,Result,G3).


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




% lex(A,who), lex(B,saw), lex(C,tom), rule(D,[A,B]), rule(E,[C])., rule(F,[D,E]).
% D = vp(A^exists(A, and(person(A), B^saw(A, B))))


% A = dt((_10246^ham(_10246))^(_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))),
% B = n(_10246^ham(_10246)),
% L = [dt((_10246^ham(_10246))^(_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))), n(_10246^ham(_10246))],
% X = np((_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))) ;

% rule(np((X^some)^exists(X, imp(P, some))), [dt((P)^(X^some)^exists(X, imp(P, some))), n(P)]).
% rule(np((_10246^_10260)^exists(_10246, imp(ham(_10246), _10260))), n(P)).



% rule(vp(X^not(Y),[]),[not(_),vp(X^Y,[])]).
% VP -> TV NP
% rule(vp(X^W),[tv(X^Y),np(Y^W)]).
% rule(vp(A^D,[]),[tv(A^C^D,[]),np(C^B)]).

% X = ynq(exists(_G406,and(egg(_G406),the(_G419,and(box(_G419),blue(_G419
  %         ),contain(_G419,_G406))))))


    %       X = vp(A^exists(B^C, and(the(B, and(and(box(B), blue(B)), C)), inside(A, B^C))), []) .

      %  X = s(exists(A, and(egg(A), exists(B^C, and(the(B, and(and(box(B), blue(B)), C)), inside(A, B^C))))), []) ;
