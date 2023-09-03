% -*- mode: prolog -*-
% 範疇文法による英文解析器
% Copyright (C) 2023, TANIGUCHI Masaya
% このプログラムは, MITライセンスのもとで配布されています.
% https://git.io/mit-license

:- op(600, xfx, #). % 文法規則 (意味表現 # 構文規則)
:- op(550, xfy, =>). % 意味表現における関数: 引数 => 結果
:- op(550, xfx, /). % 左関数範疇
:- op(550, xfx, \). % 右関数範疇

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
semrapp(A, A => B, B).
rapp(SemA # SynA, SemB # SynB, SemC # SynC) :-
    synrapp(SynA, SynB, SynC),
    semrapp(SemA, SemB, SemC).

% 左適用(Left Application, LAPP)
synlapp(A / B, B, A).
semlapp(A => B, A, B).
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
simp([call_, Arg => Body, Arg | Args], Res) :- !,
    simp([call_, Body| Args], Res).
simp([exist_, Arg => Body, Arg | Args], Res) :- !,
  simp([exist, Arg, Body | Args], Res).  % some cats loves dog: exist(cats, love(cats, dogs))
simp([forall_, Arg => Body, Arg | Args], Res) :- !,
  simp([forall, Arg, Body | Args], Res).  % every cats loves dog: forall(cats, love(cats, dogs))
simp(XX, Y) :-
    is_list(XX), !,
    maplist(simp, XX, YY),
    Y =.. YY.
simp(X, Y) :-
    X =.. XX,
    simp(XX, Y).

% 以下, 範疇文法の定義 (意味表現と対応する)
% もし、メモリが足りないときは, 以下の範疇文法を減らす.
% 基本範疇 n(単複, a/an), np(人称, 単複), s
% 人称は1, 2, 3, 単複はsg, pl, 時制は, pas, pre (過去, 現在)
%% verb like
term(like, C => A => B => call_(C, love(B, A)) # aux(N, Q, T) \ ((np(N, Q) \ s(T)) / np(_, _))).
term(like, A => B => love(B, A) # (np(1, sg) \ s(pre)) / np(_, _)).
term(like, A => B => love(B, A) # (np(2, sg) \ s(pre)) / np(_, _)).
term(likes, A => B => love(B, A) # (np(3, sg) \ s(pre)) / np(_, _)).
term(like, A => B => love(B, A) # (np(_, pl) \ s(pre)) / np(_, _)).
term(liked, A => B => love(B, A) # (np(_, pl) \ s(pas)) / np(_, _)).

%% verb run
term(run, B => A => call_(B, run(A)) # aux(N, Q, T) \ (np(N, Q) \ s(T))).
term(run, A => run(A) # np(1, sg) \ s(pre)).
term(run, A => run(A) # np(2, sg) \ s(pre)).
term(runs, A => run(A) # np(3, sg) \ s(pre)).
term(run, A => run(A) # np(_, pl) \ s(pre)).
term(ran, A => past(run(A)) # np(_, pl) \ s(pas)).

%% be not
term(not, A => not(A) # neg).
term(am, C => A => B => call_(C, be(B, A)) # ((np(1, sg) \ s(pre)) / np(_, sg)) / neg).
term(are, C => A => B => call_(C, be(B, A)) # ((np(2, sg) \ s(pre)) / np(_, _)) / neg).
term(is, C => A => B => call_(C, be(B, A)) # ((np(3, sg) \ s(pre)) / np(_, sg)) / neg).
term(are, C => A => B => call_(C, be(B, A)) # ((np(_, pl) \ s(pre)) / np(_, pl)) / neg).

%% be
term(am,  A => B => be(B, A) # (np(1, sg) \ s(pre)) / np(_, sg)).
term(are, A => B => be(B, A) # (np(2, sg) \ s(pre)) / np(_, _)).
term(is,  A => B => be(B, A) # (np(3, sg) \ s(pre)) / np(_, sg)).
term(are,  A => B => be(B, A) # (np(_, pl) \ s(pre)) / np(_, pl)).

%% Be (past)
term(was, A => B => past(be(B, A)) # (np(1, sg) \ s(pas)) / np(_, sg)).
term(were, A => B => past(be(B, A)) # (np(2, sg) \ s(pas)) / np(_, _)).
term(was, A => B => past(be(B, A)) # (np(3, sg) \ s(pas)) / np(_, sg)).
term(were, A => B => past(be(B, A)) # (np(_, pl) \ s(pas)) / np(_, pl)).

%% Be not (past)
term(was, C => A => B => call_(C, be(B, A)) # ((np(1, sg) \ s(pas)) / np(_, sg)) / neg).
term(were, C => A => B => call_(C, be(B, A)) # ((np(2, sg) \ s(pas)) / np(_, _)) / neg).
term(was, C => A => B => call_(C, be(B, A)) # ((np(3, sg) \ s(pas)) / np(_, sg)) / neg).
term(were, C => A => B => call_(C, be(B, A)) # ((np(_, pl) \ s(pas)) / np(_, pl)) / neg).

%% Do not
term(do_not, A => not(A) # aux(1, sg, pre)).
term(do_not, A => not(A) # aux(2, sg, pre)).
term(does_not, A => not(A) # aux(3, sg, pre)).
term(do_not, A => not(A) # aux(_, pl, pre)).

%% Do not
term(did_not, A => not(A) # aux(_, _, pas)).

%% conj :: (X \ X) / X
term(and, A => B => B /\ A # (X \ X ) / X).
term(or, A => B => B \/ A # (X \ X ) / X).
term(and, A => B => B /\ A # (s(_) \ s(X) ) / s(X)).
term(or, A => B => B \/ A # (s(_) \ s(X) ) / s(X)).

%% prp, subj :: s(T) / (np(3, pl) \ s(T))
term(i, A => call_(A, i) # s(T) / (np(1, sg) \ s(T))).
term(we, A => call_(A, we) # s(T) / (np(1, pl) \ s(T))).
term(you, A => call_(A, you) # s(T) / (np(2, _) \ s(T))).
term(he, A => call_(A, he) # s(T) / (np(3, sg) \ s(T))).
term(she, A => call_(A, she) # s(T) / (np(3, sg) \ s(T))).
term(they, A => call_(A, they) # s(T) / (np(3, pl) \ s(T))).

%% prp, gen :: np(3, _) / n(_, _)
term(my, A => my(A) # np(3, X) / n(X, _)).
term(our, A => our(A) # np(3, X) / n(X, _)).
term(your, A => your(A) # np(3, X) / n(X, _)).
term(his, A => his(A) # np(3, X) / n(X, _)).
term(her, A => her(A) # np(3, X) / n(X, _)).
term(their, A => their(A) # np(3, X) / n(X, _)).

%% prp, acc :: (s(T) / np(3, _)) \ s(T)
term(me, A => call_(A, me) # (s(T) / np(_, _)) \ s(T)).
term(us, A => call_(A, us) # (s(T) / np(_, _)) \ s(T)).
term(you, A => call_(A, you) # (s(T) / np(_, _)) \ s(T)).
term(him, A => call_(A, him) # (s(T) / np(_, _)) \ s(T)).
term(her, A => call_(A, her) # (s(T) / np(_, _)) \ s(T)).
term(them, A => call_(A, them) # (s(T) / np(_, _)) \ s(T)).

%% prp, pos :: (s(T) / np(3, _)) \ s(T)
term(mine, A => call_(A, mine) # (s(T) / np(_, _)) \ s(T)).
term(ours, A => call_(A, ours) # (s(T) / np(_, _)) \ s(T)).
term(yours, A => call_(A, yours) # (s(T) / np(_, _)) \ s(T)).
term(him, A => call_(A, him) # (s(T) / np(_, _)) \ s(T)).
term(hers, A => call_(A, hers) # (s(T) / np(_, _)) \ s(T)).
term(theirs, A => call_(A, theirs) # (s(T) / np(_, _)) \ s(T)).

%% n({sg, pl}, {a, an})
term(cat, cat # n(sg, a)).
term(cats, pl(cat) # n(pl, a)).
term(animal, animal # n(sg, an)).
term(animals, pl(animal) # n(pl, an)).

%% adj :: n({a, an}, {a, an}) / n({a, an}) / n({a, an})
term(beautiful, A => beautiful(A) # n(A, a) / n(A, _)).
term(white, A => white(A) # n(A, a) / n(A, _)).

%% det :: np({sg, pl}) / n({sg, pl}, {a, an})
term(a, A => a(A) # np(3, sg) / n(sg, a)).
term(an, A => a(A) # np(3, sg) / n(sg, an)).
term(the, A => the(A) # np(X) / n(X, a)).
term(the, A => the(A) # np(X) / n(X, an)).

%% quantifier :: NP/N ... np(A, a) / n(A, _)
term(a, A => a(A) # np(3, sg) / n(sg, a)).
term(all, A => B => forall_(B, A) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).
term(no, A => B => not(forall_(B, A)) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).
term(some, A => B => exist_(B, A) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).

comb_dup(0, _, []) :- !.
comb_dup(N, XS, [X|YS]) :-
    M is N - 1,
    member(X, XS),
    comb_dup(M, XS, YS).

writeln(A) :- write(A), nl.

%for swi
%g_assign(X, Y) :- nb_setval(X, Y).
%g_read(X, Y) :- nb_getval(X, Y).

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


entail(X, X).
entail(cats, animals).
entail(a(cat), an(animal)).

entail(my(cat), a(cat)).
entail(your(cat), a(cat)).
entail(his(cat), a(cat)).
entail(her(cat), a(cat)).
entail(our(cat), a(cat)).
entail(their(cat), a(cat)).

entail(my(cats), cats).
entail(your(cats), cats).
entail(his(cats), cats).
entail(her(cats), cats).
entail(our(cats), cats).
entail(their(cats), cats).

entail(be(A, B), be(C, D)) :-
    % a human is an animal, alice is a cat => ?
    % a human is a cat, alice is a animal => yes
    % alice is a cat, a human is an animal => ?
    % alice is an animal, a human is a cat => ?
    entail(A, C),
    entail(D, B).

entail(like(A, B), like(C, D)) :-
    % a human likes animal, alice likes cats => yes
    % a human likes cats, alice likes animals => ?
    % alice likes cats, human likes animals => ?
    % alice likes animals, human likes cats => ?
    entail(A, C),
    entail(B, D).

entail(run(A), run(B)) :-
    % a human run, alice run => ?
    % alice run, a human run => yes
    entail(B, A).
:- initialization((current_prolog_flag(argv, [_, A|_]), number_atom(N, A), generate(N), halt(0); halt(0))).