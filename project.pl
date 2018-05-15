
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
lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).
lemma(the,dtforthe).

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

% be
lemma(is,be).
lemma(was,be).
lemma(are,be).

% tv
lemma(eat, tv).
lemma(contain, tv).
lemma(arrive, iv).
lemma(belong, tv).
lemma(inside, tv).
lemma(put, tv).
lemma(read, iv).

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

% aux
lemma(can,aux).
lemma(do, aux).
lemma(does, aux).
lemma(will, aux).
lemma(did, aux).

% whpr - Interogative Person
lemma(who,whpr).
lemma(whose,whpr).

lemma(what,whpr).
% lemma(what,what) %%

% whth - Interogative Thing
lemma(which,whth).

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

% rel
lemma(that,rel).

% ===========================================================
%
%lemma(that,wdt).  %Check
lemma(has,be).  %Check
lemma(no,dtfornone).  %Check
lemma(what,what).
% lemma(does,be).  %Check
lemma(the,dtexists). %Check

lemma(there,there).  %Check
lemma(two,adj).  %Check
lemma(watermelon,n).  %Check
lemma(who,wh).
lemma(almond,n).  %Check
lemma(almond,adj).
% lemma(drank,tv).
lemma(which,whth).
lemma(did,be).
lemma(sam,pn).
lemma(drink,tv).  %Check
lemma(not,dtfornone).  %Check
lemma(of,p).  %Check if it is vacp
lemma(popsicle,n).  %Check
lemma(popsicles,n).  %Check
% ===========================================================


% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------


lex(n(X^P),Lemma):-
	lemma(Lemma,n),
	P=.. [Lemma,X].

lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-
		lemma(Word,dtforall).

% ...

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).

% ...


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

% model(...,...)

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
