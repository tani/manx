% -*- mode: prolog -*-
% 範疇文法による英文解析器
% Copyright (C) 2023, TANIGUCHI Masaya
% このプログラムは, MITライセンスのもとで配布されています.
% https://git.io/mit-license

:- op(600, xfx, #). % 文法規則 (意味表現 # 構文規則)
:- op(550, xfy, =>). % 意味表現における関数: 引数 => 結果
:- op(500, yfx, @). % 意味表現における関数適用: 関数 @ 引数 (注: 左結合 a @ b @ c = a(b)(c) = a(b, c))
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
rapp(X # A, Y => Z # A \ B, ((Y => Z) @ X) # B).
% 左適用(Left Application, LAPP)
lapp(X => Y # A / B, Z # B, ((X => Y) @ Z) # A).

% 単項規則 (Single Application)
sapp(X # Y, X # Y).
sapp(X # n(pl, _), X # np(3, pl)).

% リストを２つの非空リストに分割する.
append1([X|XS], [Y|YS], Z) :-
    append([X|XS], [Y|YS], Z).

% パーザ
% 列を２つの非空リストに分割し, それぞれをパーズしてから結合する.
% 分割した結果は保存されDPによって再利用される. (分割統治, メモ化)
parse_seq([], _) :- !, fail.
parse_seq([X], Y) :- !, sapp(X, Y).
parse_seq(Seq, Res) :-
    append1(LS, RS, Seq),
    parse_seq(LS, LT),
    parse_seq(RS, RT),
    (lapp(LT, RT, Res);
     rapp(LT, RT, Res)).

parse_sen(Sen, Sem # Cat) :-
    maplist(term, Sen, Seq),
    parse_seq(Seq, Thunk # Cat),
    force(Thunk, Sem).

sub(A, A, B, B) :- !.
sub(A => B, A, _, A => B) :- !.
sub(A => B, C, D, A => E) :- !,
    sub(B, C, D, E).
sub(A @ B, C, D, E @ F) :- !,
    sub(A, C, D, E),
    sub(B, C, D, F).
sub(A, B, C, D) :-
    A =.. [X1, X2], !,
    sub(X1, B, C, Y1),
    sub(X2, B, C, Y2),
    D =.. [Y1, Y2].
sub(A, B, C, D) :-
    A =.. [X1, X2, X3], !,
    sub(X1, B, C, Y1),
    sub(X2, B, C, Y2),
    sub(X3, B, C, Y3),
    D =.. [Y1, Y2, Y3].
sub(A, _, _, A).

force(A, A) :- var(A), !.
force(A @ B, A @ C) :-
    var(A), !,
    force(B, C).
force((A => B) @ C, E) :- !,
    sub(B, A, C, D),
    force(D, E).
force((A @ B) @ C, D) :- !,
    force(A @ B, X),
    force(C, Y),
    force(X @ Y, D).
force(A @ B, C) :- !,
    A =.. [X|Y],
    force(B, Z),
    append(Y, [Z], W),
    C =.. [X|W].
force(A => B, A => C) :- !,
    force(B, C).
force(A, A).

cps(X, k_ => k_ @ X) :- var(X), !.
%cps(be, B => A => K => K @ (be @ B @ A)) :- !.
%cps(run, a_ => k_ => k_ @ (run @ a_)) :- !.
cps(X, k_ => k_ @ X) :- atom(X), !.
cps(X => Y, k_ => k_ @ (X => Z)) :- cps(Y, Z), !.
cps(X @ Y, k_ => A @ (m_ => B @ (n_ => m_ @ n_ @ k_))) :-
    cps(X, A),
    cps(Y, B).

% 以下, 範疇文法の定義 (意味表現と対応する)
% もし、メモリが足りないときは, 以下の範疇文法を減らす.
% 基本範疇 n(単複, a/an), np(人称, 単複), s
% 人称は1, 2, 3, 単複はsg, pl, 時制は, pas, pre (過去, 現在)
%% verb
term(like, a_ => b_ => love @ b_ @ a_ # (np(1, sg) \ s(pre)) / np(_, _)).
term(like, a_ => b_ => love @ b_ @ a_ # (np(2, sg) \ s(pre)) / np(_, _)).
term(likes, a_ => b_ => love @ b_ @ a_ # (np(3, sg) \ s(pre)) / np(_, _)).
term(like, a_ => b_ => love @ b_ @ a_ # (np(_, pl) \ s(pre)) / np(_, _)).
term(liked, a_ => b_ => love @ b_ @ a_ # (np(_, pl) \ s(pas)) / np(_, _)).
term(run, a_ => run @ a_ # np(1, sg) \ s(pre)).
term(run, a_ => run @ a_ # np(2, sg) \ s(pre)).
term(runs, a_ => run @ a_ # np(3, sg) \ s(pre)).
term(run, a_ => run @ a_ # np(_, pl) \ s(pre)).
term(ran, a_ => past @ run @ a_ # np(_, _) \ s(pas)).
%% be
term(am, a_ => b_ => be @ b_ @ a_ # (np(1, sg) \ s(pre)) / np(_, sg)).
term(are, a_ => b_ => be @ b_ @ a_ # (np(2, sg) \ s(pre)) / np(_, _)).
term(is, a_ => b_ => be @ b_ @ a_ # (np(3, sg) \ s(pre)) / np(_, sg)).
term(are, a_ => b_ => be @ b_ @ a_ # (np(_, pl) \ s(pre)) / np(_, pl)).
term(am_not, a_ => b_ => not @ (be @ b_ @ a_) # (np(1, sg) \ s(pre)) / np(_, sg)).
term(are_not, a_ => b_ => not @ (be @ b_ @ a_) # (np(2, sg) \ s(pre)) / np(_, _)).
term(is_not, a_ => b_ => not @ (be @ b_ @ a_) # (np(3, sg) \ s(pre)) / np(_, sg)).
term(are_not, a_ => b_ => not @ (be @ b_ @ a_) # (np(_, pl) \ s(pre)) / np(_, pl)).
%% b_e (past)
term(was, a_ => b_ => past @ (be @ b_ @ a_) # (np(1, sg) \ s(pas)) / np(_, sg)).
term(were, a_ => b_ => past @ (be @ b_ @ a_) # (np(2, sg) \ s(pas)) / np(_, _)).
term(was, a_ => b_ => past @ (be @ b_ @ a_) # (np(3, sg) \ s(pas)) / np(_, sg)).
term(were, a_ => b_ => past @ (be @ b_ @ a_) # (np(_, pl) \ s(pas)) / np(_, pl)).
term(was_not, a_ => b_ => past @ (not @ (be @ b_ @ a_)) # (np(1, sg) \ s(pas)) / np(_, sg)).
term(were_not, a_ => b_ => past @ (not @ (be @ b_ @ a_)) # (np(2, sg) \ s(pas)) / np(_, _)).
term(was_not, a_ => b_ => past @ (not @ (be @ b_ @ a_)) # (np(3, sg) \ s(pas)) / np(_, sg)).
term(were_not, a_ => b_ => past @ (not @ (be @ b_ @ a_)) # (np(_, pl) \ s(pas)) / np(_, pl)).
%% Do not
term(do_not, a_ => b_ => c_ => not @ (a_ @ c_ @ b_) # ((np(1, sg) \ s(pre)) / np(Y, Z)) / ((np(1, sg) \ s(pre)) / np(Y, Z))).
term(do_not, a_ => b_ => c_ => not @ (a_ @ c_ @ b_) # ((np(2, sg) \ s(pre)) / np(Y, Z)) / ((np(2, sg) \ s(pre)) / np(Y, Z))).
term(does_not, a_ => b_ => c_ => not @ (a_ @ c_ @ b_) # ((np(3, sg) \ s(pre)) / np(X, Y)) / ((np(3, pl) \ s(pre)) / np(X, Y))).
term(do_not, a_ => b_ => c_ => not @ (a_ @ c_ @ b_) # ((np(X, pl) \ s(pre)) / np(Y, Z)) / ((np(X, pl) \ s(pre)) / np(Y, Z))).
term(do_not, a_ => b_ => not @ (a_ @ b_) # (np(1, sg) \ s(pre)) / (np(1, sg) \ s(pre))).
term(do_not, a_ => b_ => not @ (a_ @ b_) # (np(2, sg) \ s(pre)) / (np(2, sg) \ s(pre))).
term(does_not, a_ => b_ => not @ (a_ @ b_) # (np(3, sg) \ s(pre)) / (np(3, pl) \ s(pre))).
term(do_not, a_ => b_ => not @ (a_ @ b_) # (np(3, pl) \ s(pre)) / (np(3, pl) \ s(pre))).
%% Did not
term(did_not, a_ => b_ => c_ => past @ (not @ (a_ @ c_ @ b_)) # ((np(W, X) \ s(pas)) / np(Y, Z)) / ((np(W, X) \ s(pre)) / np(Y, Z))).
term(did_not, a_ => b_ => past @ (not @ (a_ @ b_)) # (np(X, Y) \ s(pas)) / (np(X, Y) \ s(pre))).
%% not
term(not, a_ => b_ => not @ (a_ @ b_) # (n(X, Y) / n(X, Y)) / (n(X, Y) / n(X, Y))).
%% conj :: (X \ X) / X
% term(and, a_ => b_ => b_ /\ a_ # (X \ X ) / X).
% term(or, a_ => b_ => b_ \/ a_ # (X \ X ) / X).
% term(and, a_ => b_ => b_ /\ a_ # (s(_) \ s(X) ) / s(X)).
% term(or, a_ => b_ => b_ \/ a_ # (s(_) \ s(X) ) / s(X)).
%% prp, subj :: s(T) / (np(3, pl) \ s(T))
term(i, a_ => a_ @ i # s(T) / (np(1, sg) \ s(T))).
term(we, a_ => a_ @ we # s(T) / (np(1, pl) \ s(T))).
term(you, a_ => a_ @ you # s(T) / (np(2, _) \ s(T))).
term(he, a_ => a_ @ he # s(T) / (np(3, sg) \ s(T))).
term(she, a_ => a_ @ she # s(T) / (np(3, sg) \ s(T))).
term(they, a_ => a_ @ they # s(T) / (np(3, pl) \ s(T))).
%% prp, gen :: np(3, _) / n(_, _)
term(my, a_ => my @ a_ # np(3, X) / n(X, _)).
term(our, a_ => our @ a_ # np(3, X) / n(X, _)).
term(your, a_ => your @ a_ # np(3, X) / n(X, _)).
term(his, a_ => his @ a_ # np(3, X) / n(X, _)).
term(her, a_ => her @ a_ # np(3, X) / n(X, _)).
term(their, a_ => their @ a_ # np(3, X) / n(X, _)).
%% prp, acc :: (s(T) / np(3, _)) \ s(T)
term(me, a_ => a_ @ me # (s(T) / np(_, _)) \ s(T)).
term(us, a_ => a_ @ us # (s(T) / np(_, _)) \ s(T)).
term(you, a_ => a_ @ you # (s(T) / np(_, _)) \ s(T)).
term(him, a_ => a_ @ him # (s(T) / np(_, _)) \ s(T)).
term(her, a_ => a_ @ her # (s(T) / np(_, _)) \ s(T)).
term(them, a_ => a_ @ them # (s(T) / np(_, _)) \ s(T)).
%% n({sg, pl}, {a, an})
term(cat, cat # n(sg, a)).
term(cats, cats # n(pl, a)).
term(animal, animal # n(sg, an)).
term(animals, animals # n(pl, an)).
%% adj :: n({a, an}, {a, an}) / n({a, an}) / n({a, an})
term(beautiful, a_ => beautiful @ a_ # n(X, a) / n(X, _)).
term(white, a_ => white @ a_ # n(X, a) / n(X, _)).
%% det :: np({sg, pl}) / n({sg, pl}, {a, an})
term(a, a_ => a @ a_ # np(3, sg) / n(sg, a)).
term(an, a_ => a @ a_ # np(3, sg) / n(sg, an)).
term(the, a_ => the @ a_ # np(X) / n(X, a)).
term(the, a_ => the @ a_ # np(X) / n(X, an)).

% 意味解析器
%semparse(Words) :-
%  forall(member(Word, Words), term(Word, _))
%  -> length(Words, N),
%     length(Seq, N),
%     maplist(term, Words, Seq),
%     parse(Seq, Res # s(_)),
%     simp(Res, Sem),
%     write(Sem), nl
%   ; write('Error: Unknown word in sentence.'), nl.

comb_dup(0, _, []) :- !.
comb_dup(N, XS, [X|YS]) :-
    M is N - 1,
    member(X, XS),
    comb_dup(M, XS, YS).

writeln(A) :- write(A), nl.

generate(N) :-
    findall(Word, term(Word, _), Words),
    sort(Words, UniqueWords),
    length(UniqueWords, C),
    M is C ** N,
    g_assign(i, 0),
    findall(Sen # Sem, (
       comb_dup(N, UniqueWords, Sen),
       g_read(i, I),
       J is I + 1,
       g_assign(i, J),
       P is I * 100 / M,
       format(user_error, '~c~f %%', [13, P]),
       parse_sen(Sen, Sem # s(_))
     ), Res),
    maplist(writeln, Res).

:- initialization((current_prolog_flag(argv, [_, A|_]), number_atom(N, A), generate(N), halt(0); halt(0))).
