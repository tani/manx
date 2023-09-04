% -*- mode: prolog -*-
% 範疇文法による英文解析器
% Copyright (C) 2023, TANIGUCHI Masaya
% このプログラムは, MITライセンスのもとで配布されています.
% https://git.io/mit-license

:- op(600, xfx, #). % 文法規則 (意味表現 # 構文規則)
:- op(550, xfy, -->). % 意味表現における関数: 引数 --> 結果
:- op(550, xfx, /). % 左関数範疇
:- op(550, xfx, \). % 右関数範疇

:- op(600, fx, forall).
:- op(600, fx, exists).
:- op(650, xfy, :).
:- op(500, xfy, /\).
:- op(500, xfy, \/).
:- op(550, xfy, =>).
:- op(450, fy, ~).

:- [vocab].

% メモ化のための設定.
%:- table parse/2 as private.
%:- table parse_/2 as private.
% メモに使うメモリ領域
%:- set_prolog_flag(table_space, 8000000000).
% 同時実行数
%:- set_prolog_flag(cpu_count, 8).

% 以下, パーザの定義.

% 右適用(Right Application, RAPP)
synrapp(A, A \ B, B).
semrapp(A, A --> B, B).
rapp(SemA # SynA, SemB # SynB, SemC # SynC) :-
    synrapp(SynA, SynB, SynC),
    semrapp(SemA, SemB, SemC).

% 左適用(Left Application, LAPP)
synlapp(A / B, B, A).
semlapp(A --> B, A, B).
lapp(SemA # SynA, SemB # SynB, SemC # SynC) :-
    synlapp(SynA, SynB, SynC),
    semlapp(SemA, SemB, SemC).

% 単項規則 (Single Application)
sapp(X # Y, X # Y).
sapp(X # n(pl, _), X # np(3, pl)).

% リストを２つの非空リストに分割する.
append1([X|XS], [Y|YS], Z) :-
    append([X|XS], [Y|YS], Z).

% パーザ
% 列を２つの非空リストに分割し, それぞれをパーズしてから結合する.
% 分割した結果は保存されDPによって再利用される. (分割統治, メモ化)
parse([], _) :- !, fail.
parse([X], Y) :- !, sapp(X, Y).
parse(Seq, Res) :-
    append1(LS, RS, Seq),
    parse(LS, LT),
    parse(RS, RT),
    (lapp(LT, RT, Res);
     rapp(LT, RT, Res)).

% 意味表現における高階の述語(call_)を簡約する.
simp(X, X) :-
    var(X), !.
simp(X, X) :-
    atom(X), !.
simp([call_, X], Y) :- !,
    simp(X, Y).
simp([call_, Arg --> Body, Arg | Args], Res) :- !,
    simp([call_, Body| Args], Res).
simp([exists_, Arg --> Body, pl(Arg1) | Args], Res) :- !,
  gensym(x, Arg),
  %  simp([exists Arg: be(Arg, Arg1) /\ Body | Args], Res).
% some cats loves dog: exist(cats, love(cats, dogs)).
   simp([exist, Arg, be(Arg, Arg1) /\ Body | Args], Res).
% some cats loves dog: exist(cats, love(cats, dogs))
simp([forall_, Arg --> Body, pl(Arg1) | Args], Res) :- !,
  gensym(x, Arg),
  %simp([forall Arg: be(Arg, Arg1) => Body | Args], Res).  % every cats loves dog: forall(cats, love(cats, dogs)).
  simp([forall, Arg, be(Arg, Arg1) => Body | Args], Res).  % every cats loves dog: forall(cats, love(cats, dogs)).
simp(XX, Y) :-
    is_list(XX), !,
    maplist(simp, XX, YY),
    Y =.. YY.
simp(X, Y) :-
    X =.. XX,
    simp(XX, Y).

comb_dup(0, _, []) :- !.
comb_dup(N, XS, [X|YS]) :-
    M is N - 1,
    member(X, XS),
    comb_dup(M, XS, YS).

%writeln(A) :- write(A), nl.

%for swi
g_assign(X, Y) :- nb_setval(X, Y).
g_read(X, Y) :- nb_getval(X, Y).

generate(N) :-
    findall(Word, term(Word, _), Words),
    length(Words, C),
    M is C ** N,
    g_assign(i, 0),
    findall(Sen # Sem, (
       length(Seq, N),
       length(Sen, N),
       maplist(term, Sen, Seq),
       g_read(i, I),
       J is I + 1,
       g_assign(i, J),
       P is I * 100 / M,
       format(user_error, '~f %%~n', [P]),
       parse(Seq, Res # s(_)),
       simp(Res, Sem),
       write(Sen), write(' # '), write(Sem), nl
     ), Res),
    maplist(writeln, Res).

semparse(X, Z) :-
  split_string(X, " ", '\s\t\n', Xs),
  maplist(string_lower, Xs, Xs1),
  maplist(atom_string, Xs2, Xs1),
  maplist(term, Xs2, Xs3),
  parse(Xs3, Y # s(_)),
  simp(Y, Z).

entail(X, Y) :- X -> Y.

%:-
%  current_prolog_flag(argv, [A]),
%  atom_number(A, N),
%  generate(N),
%  halt(0);
%  halt(1).
