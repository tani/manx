% vim: ft=prolog

:- op(600, fx, forall).
:- op(600, fx, exists).
:- op(650, xfy, :).
:- op(500, xfy, /\).
:- op(500, xfy, \/).
:- op(550, xfy, =>).
:- op(450, fy, ~).
:- op(700, xfx, --).

% substitute(A, B, C, D)
% Cの中のAをBに置き換えたものをDとする
subsitute(Var, NewVar, Var, NewVar) :- !.
subsitute(_, _, Term, Term) :- atom(Term), !.
subsitute(Var, NewVar, Term, NewTerm) :-
  Term =.. [Name | Args],
  maplist(subsitute(Var, NewVar), Args, NewArgs),
  NewTerm =.. [Name | NewArgs].

% duplicate(Item, N, List)
% ItemをN個並べたリストをListとする
duplicate(_, 0, []).
duplicate(Item, N, [Item | Rest]) :-
  N > 0,
  N1 is N - 1,
  duplicate(Item, N1, Rest).

% join(List, Op, Result)
% Listの要素をOpでつなげたものをResultとする
join([], _, []).
join([X], _, X).
join([X, Y | Rest], Op, Result) :-
  join([Y | Rest], Op, RestResult),
  Result =.. [Op, X, RestResult].

% eliminate(Term, Univ, Result)
% Termの中の量化子を消去したものをResultとする
% 量化された変数のドメインはUnivとする (エルブラン領域)
eliminate(exists Var: Body, Univ, Result) :- !,
  eliminate(Body, Univ, NewBody),
  length(Univ, N),
  duplicate(Var, N, VarList),
  duplicate(NewBody, N, NewBodyList),
  maplist(subsitute, VarList, Univ, NewBodyList, List),
  join(List, \/, Result).

eliminate(forall Var: Body, Univ, Result) :- !,
  eliminate(Body, Univ, NewBody),
  length(Univ, N),
  duplicate(Var, N, VarList),
  duplicate(NewBody, N, NewBodyList),
  maplist(subsitute, VarList, Univ, NewBodyList, List),
  join(List, /\, Result).

eliminate(A /\ B, Univ, Result) :- !,
  eliminate(A, Univ, NewA),
  eliminate(B, Univ, NewB),
  Result = NewA /\ NewB.

eliminate(A \/ B, Univ, Result) :- !,
  eliminate(A, Univ, NewA),
  eliminate(B, Univ, NewB),
  Result = NewA \/ NewB.

eliminate(A => B, Univ, Result) :- !,
  eliminate(A, Univ, NewA),
  eliminate(B, Univ, NewB),
  Result = NewA => NewB.

eliminate(~A, Univ, Result) :- !,
  eliminate(A, Univ, NewA),
  Result = ~NewA.

eliminate(A, _, A).

% fol_cpl(FOL, CPL)
% 1階述語論理の式FOLを古典命題論理の式CPLに変換する
:- retractall(dict(_, _)).
fol_cpl(X/\Y, A/\B) :- !,
  fol_cpl(X, A),
  fol_cpl(Y, B).
fol_cpl(X\/Y, A\/B) :- !,
  fol_cpl(X, A),
  fol_cpl(Y, B).
fol_cpl(X=>Y, A=>B) :- !,
  fol_cpl(X, A),
  fol_cpl(Y, B).
fol_cpl(~X, ~A) :- !,
  fol_cpl(X, A).
fol_cpl(X, A) :-
  call(dict(X, A)), !.
fol_cpl(X, A) :-
  gensym(x, A),
  assertz(dict(X, A)).

% universe(Constants, Functors, Univ, Depth, Arity).
% Constantsの中の定数とFunctorsの中の関数記号を用いて
% 生成できる項をUnivとする (エルブラン領域 $H_{Depth}$)
% 項の深さはDepth以下とする (Depth = 0ならば定数のみ, Default: 1)
% 項の引数の数はArity以下とする (Default: 2)
universe(Univ, _, Univ, 0, _) :- !.
universe([C|CS], Functors, Univ, 1, 1) :- !,
  universe(CS, Functors, UnivA, 1, 1),
  universe(C, Functors, UnivB, 1, 1),
  append(UnivA, UnivB, Univ).
universe([], _, [], 1, 1) :- !.
universe(C, [F|FS], Univ, 1, 1) :- !,
  universe(C, FS, UnivA, 1, 1),
  universe(C, F, UnivB, 1, 1),
  append(UnivA, UnivB, Univ).
universe(C, [], [C], 1, 1) :- !.
universe(C, F, [T], 1, 1) :- !,
  F =.. G,
  append(G, [C], H),
  T =.. H.
universe(Constants, Functors, Univ, 1, Arity) :- !,
  Arity1 is Arity - 1,
  universe(Constants, Functors, UnivA, 1, 1),
  append(Constants, UnivA, UnivB),
  exclude(atom, UnivB, UnivC),
  universe(Constants, UnivC, UnivD, 1, Arity1),
  append(UnivB, UnivD, UnivE),
  sort(UnivE, Univ).
universe(Constants, Functors, Univ, Depth, Arity) :-
  Depth1 is Depth - 1,
  universe(Constants, Functors, UnivA, 1, Arity),
  append(Constants, UnivA, UnivB),
  universe(UnivB, Functors, UnivC, Depth1, Arity),
  append(UnivB, UnivC, UnivD),
  sort(UnivD, Univ).
universe(Constants, Functors, Univ) :-
  universe(Constants, Functors, Univ, 1, 2).

% tableaux(Props, Path).
% タブロー法による証明探索
tableaux([A => B|C], P) :-
  tableaux([~ A|C], P);
  tableaux([B|C], P).
tableaux([~ (A => B)|C], P) :-
  tableaux([A, ~ B|C], P).
tableaux([A \/ B|C], P) :-
  tableaux([A|C], P);
  tableaux([B|C], P).
tableaux([~ (A \/ B)|C], P) :-
  tableaux([~ B, ~A|C], P).
tableaux([~ ~ A|B], P) :-
  tableaux([A|B], P).
tableaux([A /\ B|C], P) :-
  tableaux([A,B|C], P).
tableaux([~ (A /\ B)|C], P) :-
  tableaux([~ A|C], P);
  tableaux([~ B|C], P).
tableaux([A|B], [A|P]) :-
  atom(A),
  tableaux(B, P).
tableaux([~ A|B], [~ A|P]) :-
  atom(A),
  tableaux(B, P).
tableaux([], []).

% inconsistent(P)
% Pが矛盾しているかどうかを判定する
inconsistent(P) :-
  member(A, P),
  member(~ A, P).

% entail_tbl(Assum, Concl).
% AssumがConclを導出できるかどうかを判定する
entail_tbl(Assum, Concl) :-
  universe([dog, john, apple, animal, fruit], [white, cute], Univ),
  entail_tbl(Assum, Concl, Univ).

entail_tbl(Assum, Concl, Univ) :-
  eliminate(Assum, Univ, NewAssum),
  eliminate(Concl, Univ, NewConcl), !,
  fol_cpl(NewAssum, NewAssumCPL),
  fol_cpl(NewConcl, NewConclCPL),
  forall(tableaux([~ NewConclCPL, NewAssumCPL], P), inconsistent(P)).

:- use_module(library(clpb)).

cpl_clpb(A /\ B, X * Y) :- !,
  cpl_clpb(A, X),
  cpl_clpb(B, Y).
cpl_clpb(A \/ B, X + Y) :- !,
  cpl_clpb(A, X),
  cpl_clpb(B, Y).
cpl_clpb(A => B, ~ X + Y) :- !,
  cpl_clpb(A, X),
  cpl_clpb(B, Y).
cpl_clpb(~ A, ~ X) :- !,
  cpl_clpb(A, X).
cpl_clpb(A, A).

% entail_clpb(Assum, Concl).
% AssumがConclを導出できるかどうかを判定する
entail_clpb(Assum, Concl, Univ) :-
  eliminate(Assum, Univ, NewAssum),
  eliminate(Concl, Univ, NewConcl), !,
  fol_cpl(NewAssum, NewAssumCPL),
  fol_cpl(NewConcl, NewConclCPL),
  cpl_clpb(NewAssumCPL, NewAssumCLPB),
  cpl_clpb(NewConclCPL, NewConclCLPB),
  taut((~ NewAssumCLPB) + NewConclCLPB, 1).

entail_clpb(Assum, Concl) :-
  universe([dog, john, apple, animal, fruit], [white, cute], Univ),
  entail_clpb(Assum, Concl, Univ).

:- use_module(library(http/http_server)).

:- http_handler(root(.), http_reply_file('index.html', []), []).
:- http_handler(root(entail), entail_handler, []).

% split(String, List)
% this predicate splits String by ',' and returns List
split(String, List) :-
  split_string(String, ',', '\s\t\n', StringList),
  maplist(atom_string, List, StringList).

entail_handler(Request) :-
  http_parameters(Request, [
    const(Const, [string]),
    funct(Funct, [string]),
    arity(Arity, [integer]),
    depth(Depth, [integer]),
    assum(Assum, [string]),
    concl(Concl, [string])
  ]),
  split(Const, ConstList),
  split(Funct, FunctList),
  universe(ConstList, FunctList, Univ, Depth, Arity),
  atom_to_term(Assum, AssumTerm, _),
  atom_to_term(Concl, ConclTerm, _),
  entail_clpb(AssumTerm, ConclTerm, Univ) -> (
    format('Content-type: text/plain~n~n'),
    format('true~n')
  ); (
    format('Content-type: text/plain~n~n'),
    format('false~n')
  ).

:- http_server(http_dispatch, [port(3000)]).
