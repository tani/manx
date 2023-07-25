% -*- mode: prolog -*-

% 範疇文法による英文解析器
% Copyright (C) 2023, TANIGUCHI Masaya
% このプログラムは, MITライセンスのもとで配布されています.
% https://git.io/mit-license

:- use_module(library(clpfd)).
:- op(600, xfx, #). % 文法規則 (意味表現 # 構文規則)
:- op(550, xfy, =>). % 意味表現における関数: 引数 => 結果
:- op(500, xfy, @). % 意味表現における関数適用: 関数 @ 引数 (注: 右結合 a @ b @ [c, d] = a(b(c,d)))
:- op(550, xfx, /). % 左関数範疇
:- op(550, xfx, \). % 右関数範疇

% メモ化のための設定.
:- table parse/2 as shared.
:- table parse_/2 as shared.
% メモに使うメモリ領域
:- set_prolog_flag(table_space, 8000000000).
% 同時実行数
:- set_prolog_flag(cpu_count, 8).

% 以下, パーザの定義.

% 関数適用(Function Application, FAPP)
fapp(Params => Body, Arg, Ret) :-
    append([Arg], Rest, Params),
    (Rest = [] -> Ret = Body; Ret = Rest => Body).

% 右適用(Right Application, RAPP)
rapp(X # A, Y # A \ B, Z # B) :-
    fapp(Y, X, Z).

% 左適用(Left Application, LAPP)
lapp(X # A / B, Y # B, Z # A) :-
    fapp(X, Y, Z).

% 単項規則 (Single Application, SAPP)
sapp(X # Y, X # Y).
sapp(X # n(pl, _), X # np(3, pl)).

% リストを２つの非空リストに分割する.
append1([X|XS], [Y|YS], Z) :-
    append([X|XS], [Y|YS], Z).

% パーザ
% 列を２つの非空リストに分割し, それぞれをパーズしてから結合する.
% 分割した結果は保存されDPによって再利用される. (分割統治, メモ化)
parse_([], _) :- !, fail.
parse_([X], Y) :- !, sapp(X, Y).
parse_(Seq, Res) :-
    append1(LS, RS, Seq),
    parse_(LS, LT),
    parse_(RS, RT),
    (lapp(LT, RT, Res);
     rapp(LT, RT, Res)).

parse(Sen, Sem # Cat) :-
    maplist(term, Sen, Seq),
    parse_(Seq, Res # Cat),
    mono(Res, Sem).

% 意味表現における高階の述語(Fn @ Args)を簡約する.
simp(X, X) :-
    var(X), !.
simp(X, X) :-
    atom(X), !.
simp(Params => Body @ Args, Return) :- !,
    append(Args, Rest, Params),
    (Rest = [] -> Return = Body; simp(Rest => Body, Return)).
simp(Fn @ Args, Res) :-
    maplist(simp, [Fn|Args], [NewFn|NewArgs]),
    (atom(Fn) -> Res =.. [NewFn|NewArgs]; simp(NewFn @ NewArgs, Res)).

mono(Fn @ [Arg1], NewFn @ [NewArg1]) :- !,
    mono(Fn, NewFn),
    mono(Arg1, NewArg1).
mono([Param1|Parasm] => Body @ [Arg1|Args], Res) :- !,
    mono(Params => (Param1 => Body @ [Arg1]) @ Args, Res).
mono(Fn @ [Arg1|Args], Res) :-
    Param => Fn @ [Fn, Par]
    
%cps(X, K => K @ [X]) :- (atom(X); var(X)), !.
%cps(X => Y, K => K @ [X => Z]) :- cps(Y, Z), !.
%cps(M @ [N], K => )
    
% 以下, 範疇文法の定義 (意味表現と対応する)
% もし、メモリが足りないときは, 以下の範疇文法を減らす.
% 基本範疇 n(単複, a/an), np(人称, 単複), s
% 人称は1, 2, 3, 単複はsg, pl, 時制は, pas, pre (過去, 現在)
%% verb

term(like, [A, B] => love @ [B, A] # (np(1, sg) \ s(pre)) / np(_, _)).
term(like, [A, B] => love @ [B, A] # (np(2, sg) \ s(pre)) / np(_, _)).
term(likes, [A, B] => love @ [B, A] # (np(3, sg) \ s(pre)) / np(_, _)).
term(like, [A, B] => love @ [B, A] # (np(_, pl) \ s(pre)) / np(_, _)).
term(liked, [A, B] => love @ [B, A] # (np(_, pl) \ s(pas)) / np(_, _)).
term(run, [A] => run @ [A] # np(1, sg) \ s(pre)).
term(run, [A] => run @ [A] # np(2, sg) \ s(pre)).
term(runs, [A] => run @ [A] # np(3, sg) \ s(pre)).
term(run, [A] => run @ [A] # np(_, pl) \ s(pre)).
term(run, [A] => past @ run @ [A] # np(_, _) \ s(pas)).
%% be
term(am, [A, B] => be @ [B, A] # (np(1, sg) \ s(pre)) / np(_, sg)).
term(are, [A, B] => be @ [B, A] # (np(2, sg) \ s(pre)) / np(_, _)).
term(is, [A, B] => be @ [B, A] # (np(3, sg) \ s(pre)) / np(_, sg)).
term(are, [A, B] => be @ [B, A] # (np(_, pl) \ s(pre)) / np(_, pl)).
term(am_not, [A, B] => not @ be @ [B, A] # (np(1, sg) \ s(pre)) / np(_, sg)).
term(are_not, [A, B] => not @ be @ [B, A] # (np(2, sg) \ s(pre)) / np(_, _)).
term(is_not, [A, B] => not @ be @ [B, A] # (np(3, sg) \ s(pre)) / np(_, sg)).
term(are_not, [A, B] => not @ be @ [B, A] # (np(_, pl) \ s(pre)) / np(_, pl)).
%% Be (past)
term(was, [A, B] => past @ be @ [B, A] # (np(1, sg) \ s(pas)) / np(_, sg)).
term(were, [A, B] => past @ be @ [B, A] # (np(2, sg) \ s(pas)) / np(_, _)).
term(was, [A, B] => past @ be @ [B, A] # (np(3, sg) \ s(pas)) / np(_, sg)).
term(were, [A, B] => past @ be @ [B, A] # (np(_, pl) \ s(pas)) / np(_, pl)).
term(was_not, [A, B] => past @ not @ be @ [B, A] # (np(1, sg) \ s(pas)) / np(_, sg)).
term(were_not, [A, B] => past @ not @ be @ [B, A] # (np(2, sg) \ s(pas)) / np(_, _)).
term(was_not, [A, B] => past @ not @ be @ [B, A] # (np(3, sg) \ s(pas)) / np(_, sg)).
term(were_not, [A, B] => past @ not @ be @ [B, A] # (np(_, pl) \ s(pas)) / np(_, pl)).
%% Do not
term(do_not, [A, B, C] => not @ A @ [C, B] # ((np(1, sg) \ s(pre)) / np(Y, Z)) / ((np(1, sg) \ s(pre)) / np(Y, Z))).
term(do_not, [A, B, C] => not @ A @ [C, B] # ((np(2, sg) \ s(pre)) / np(Y, Z)) / ((np(2, sg) \ s(pre)) / np(Y, Z))).
term(does_not, [A, B, C] => not @ A @ [C, B] # ((np(3, sg) \ s(pre)) / np(X, Y)) / ((np(3, pl) \ s(pre)) / np(X, Y))).
term(do_not, [A, B, C] => not @ A @ [C, B] # ((np(X, pl) \ s(pre)) / np(Y, Z)) / ((np(X, pl) \ s(pre)) / np(Y, Z))).
term(do_not, [A, B] => not @ A @ [B] # (np(1, sg) \ s(pre)) / (np(1, sg) \ s(pre))).
term(do_not, [A, B] => not @ A @ [B] # (np(2, sg) \ s(pre)) / (np(2, sg) \ s(pre))).
term(does_not, [A, B] => not @ A @ [B] # (np(3, sg) \ s(pre)) / (np(3, pl) \ s(pre))).
term(do_not, [A, B] => not @ A @ [B] # (np(3, pl) \ s(pre)) / (np(3, pl) \ s(pre))).
%% Did not
term(did_not, [A, B, C] => past @ not @ A @ [C, B] # ((np(W, X) \ s(pas)) / np(Y, Z)) / ((np(W, X) \ s(pre)) / np(Y, Z))).
term(did_not, [A, B] => past @ not @ A @ [B] # (np(X, Y) \ s(pas)) / (np(X, Y) \ s(pre))).
%% not
term(not, [A, B] => not @ A @ [B] # (n(X, Y) / n(X, Y)) / (n(X, Y) / n(X, Y))).
%% conj :: (X \ X) / X
term(and, [A, B] => B /\ A # (X \ X ) / X).
term(or, [A, B] => B \/ A # (X \ X ) / X).
term(and, [A, B] => B /\ A # (s(_) \ s(X) ) / s(X)).
term(or, [A, B] => B \/ A # (s(_) \ s(X) ) / s(X)).
%% prp, subj :: s(T) / (np(3, pl) \ s(T))
term(i, [A] => A @ [i] # s(T) / (np(1, sg) \ s(T))).
term(we, [A] => A @ [we] # s(T) / (np(1, pl) \ s(T))).
term(you, [A] => A @ [you] # s(T) / (np(2, _) \ s(T))).
term(he, [A] => A @ [he] # s(T) / (np(3, sg) \ s(T))).
term(she, [A] => A @ [she] # s(T) / (np(3, sg) \ s(T))).
term(they, [A] => A @ [they] # s(T) / (np(3, pl) \ s(T))).
%% prp, gen :: np(3, _) / n(_, _)
term(my, [A] => my @ [A] # np(3, X) / n(X, _)).
term(our, [A] => our @ [A] # np(3, X) / n(X, _)).
term(your, [A] => your @ [A] # np(3, X) / n(X, _)).
term(his, [A] => his @ [A] # np(3, X) / n(X, _)).
term(her, [A] => her @ [A] # np(3, X) / n(X, _)).
term(their, [A] => their @ [A] # np(3, X) / n(X, _)).
%% prp, acc :: (s(T) / np(3, _)) \ s(T)
term(me, [A] => A @ [me] # (s(T) / np(_, _)) \ s(T)).
term(us, [A] => A @ [us] # (s(T) / np(_, _)) \ s(T)).
term(you, [A] => A @ [you] # (s(T) / np(_, _)) \ s(T)).
term(him, [A] => A @ [him] # (s(T) / np(_, _)) \ s(T)).
term(her, [A] => A @ [her] # (s(T) / np(_, _)) \ s(T)).
term(them, [A] => A @ [them] # (s(T) / np(_, _)) \ s(T)).
%% n({sg, pl}, {a, an})
term(cat, cat # n(sg, a)).
term(cats, cats # n(pl, a)).
term(animal, animal # n(sg, an)).
term(animals, animals # n(pl, an)).
%% adj :: n({a, an}, {a, an}) / n({a, an}) / n({a, an})
term(beautiful, beautiful # n(A, a) / n(A, _)).
term(white, white # n(A, a) / n(A, _)).
%% det :: np({sg, pl}) / n({sg, pl}, {a, an})
term(a, [A] => a @ [A] # np(3, sg) / n(sg, a)).
term(an, [A] => a @ [A] # np(3, sg) / n(sg, an)).
term(the, [A] => the @ [A] # np(X) / n(X, a)).
term(the, [A] => the @ [A] # np(X) / n(X, an)).

% 意味解析器
semparse(Words) :-
  forall(member(Word, Words), term(Word, _))
  -> length(Words, N),
     length(Seq, N),
     maplist(term, Words, Seq),
     parse(Seq, Res # s(_)),
     simp(Res, Sem),
     write(Sem), nl
   ; write('Error: Unknown word in sentence.'), nl.

% 生成可能な文をすべて出力
generate(N) :-
  findall(Sen, (
    length(Seq, N),
    length(Sen, N),
    maplist(term, Sen, Seq),
    parse(Seq, Res # s(_)),
    simp(Res, Sem),
    write(Sen), write(' # '), write(Sem), nl
  ), _),
  halt.

comb_unq(0, _, []) :- !.
comb_unq(N, [X|XS], [X|YS]) :-
    M is N - 1,
    comb_unq(M, XS, YS).
comb_unq(N, [_|XS], YS) :-
    comb_unq(N, XS, YS).

comb_dup(0, _, []) :- !.
comb_dup(N, XS, [X|YS]) :-
    M is N - 1,
    member(X, XS),
    comb_dup(M, XS, YS).

concurrent_generate(N) :-
    findall(Word, term(Word, _), Words),
    sort(Words, UniqueWords),
    concurrent_forall(
	comb_dup(N, UniqueWords, Sen),
	(parse(Sen, Sem # s(_)), writeln(Sen # Sem); true)
    ).

    

%%:- initialization(generate(3)).
