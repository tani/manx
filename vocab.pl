% 以下, 範疇文法の定義 (意味表現と対応する)
% もし、メモリが足りないときは, 以下の範疇文法を減らす.
% 基本範疇 n(単複, a/an), np(人称, 単複), s
% 人称は1, 2, 3, 単複はsg, pl, 時制は, pas, pre (過去, 現在)
%% verb like
term(like, C --> A --> B --> call_(C, like(B, A)) # aux(N, Q, T) \ ((np(N, Q) \ s(T)) / np(_, _))).
term(like, A --> B --> like(B, A) # (np(1, sg) \ s(pre)) / np(_, _)).
term(like, A --> B --> like(B, A) # (np(2, sg) \ s(pre)) / np(_, _)).
term(likes, A --> B --> like(B, A) # (np(3, sg) \ s(pre)) / np(_, _)).
term(like, A --> B --> like(B, A) # (np(_, pl) \ s(pre)) / np(_, _)).
term(liked, A --> B --> past(like(B, A)) # (np(_, pl) \ s(pas)) / np(_, _)).

%% verb run
%term(run, B --> A --> call_(B, run(A)) # aux(N, Q, T) \ (np(N, Q) \ s(T))).
%term(run, A --> run(A) # np(1, sg) \ s(pre)).
%term(run, A --> run(A) # np(2, sg) \ s(pre)).
%term(runs, A --> run(A) # np(3, sg) \ s(pre)).
%term(run, A --> run(A) # np(_, pl) \ s(pre)).
%term(ran, A --> past(run(A)) # np(_, pl) \ s(pas)).

%% be not
term(not, A --> not(A) # neg).
%term(am, C --> A --> B --> call_(C, be(B, A)) # ((np(1, sg) \ s(pre)) / np(_, sg)) / neg).
%term(are, C --> A --> B --> call_(C, be(B, A)) # ((np(2, sg) \ s(pre)) / np(_, _)) / neg).
term(is, C --> A --> B --> call_(C, be(B, A)) # ((np(3, sg) \ s(pre)) / np(_, sg)) / neg).
%term(are, C --> A --> B --> call_(C, be(B, A)) # ((np(_, pl) \ s(pre)) / np(_, pl)) / neg).

%% be
%term(am,  A --> B --> be(B, A) # (np(1, sg) \ s(pre)) / np(_, sg)).
%term(are, A --> B --> be(B, A) # (np(2, sg) \ s(pre)) / np(_, _)).
term(is,  A --> B --> be(B, A) # (np(3, sg) \ s(pre)) / np(_, sg)).
%term(are,  A --> B --> be(B, A) # (np(_, pl) \ s(pre)) / np(_, pl)).

% %% Be (past)
% term(was, A --> B --> past(be(B, A)) # (np(1, sg) \ s(pas)) / np(_, sg)).
% term(were, A --> B --> past(be(B, A)) # (np(2, sg) \ s(pas)) / np(_, _)).
% term(was, A --> B --> past(be(B, A)) # (np(3, sg) \ s(pas)) / np(_, sg)).
% term(were, A --> B --> past(be(B, A)) # (np(_, pl) \ s(pas)) / np(_, pl)).

% %% Be not (past)
% term(was, C --> A --> B --> call_(C, be(B, A)) # ((np(1, sg) \ s(pas)) / np(_, sg)) / neg).
% term(were, C --> A --> B --> call_(C, be(B, A)) # ((np(2, sg) \ s(pas)) / np(_, _)) / neg).
% term(was, C --> A --> B --> call_(C, be(B, A)) # ((np(3, sg) \ s(pas)) / np(_, sg)) / neg).
% term(were, C --> A --> B --> call_(C, be(B, A)) # ((np(_, pl) \ s(pas)) / np(_, pl)) / neg).

% %% Do not
% term(do_not, A --> not(A) # aux(1, sg, pre)).
% term(do_not, A --> not(A) # aux(2, sg, pre)).
% term(does_not, A --> not(A) # aux(3, sg, pre)).
% term(do_not, A --> not(A) # aux(_, pl, pre)).

% %% Do not
% term(did_not, A --> not(A) # aux(_, _, pas)).

%% conj :: (X \ X) / X
% term(and, A --> B --> B /\ A # (X \ X ) / X).
% term(or, A --> B --> B \/ A # (X \ X ) / X).
% term(and, A --> B --> B /\ A # (s(_) \ s(X) ) / s(X)).
% term(or, A --> B --> B \/ A # (s(_) \ s(X) ) / s(X)).

%% prp, subj :: s(T) / (np(3, pl) \ s(T))
%term(i, A --> call_(A, i) # s(T) / (np(1, sg) \ s(T))).
%term(we, A --> call_(A, we) # s(T) / (np(1, pl) \ s(T))).
%term(you, A --> call_(A, you) # s(T) / (np(2, _) \ s(T))).
%term(he, A --> call_(A, he) # s(T) / (np(3, sg) \ s(T))).
%term(she, A --> call_(A, she) # s(T) / (np(3, sg) \ s(T))).
%term(they, A --> call_(A, they) # s(T) / (np(3, pl) \ s(T))).

%% prp, gen :: np(3, _) / n(_, _)
%term(my, A --> my(A) # np(3, X) / n(X, _)).
%term(our, A --> our(A) # np(3, X) / n(X, _)).
%term(your, A --> your(A) # np(3, X) / n(X, _)).
%term(his, A --> his(A) # np(3, X) / n(X, _)).
%term(her, A --> her(A) # np(3, X) / n(X, _)).
%term(their, A --> their(A) # np(3, X) / n(X, _)).

%% prp, acc :: (s(T) / np(3, _)) \ s(T)
%term(me, A --> call_(A, me) # (s(T) / np(_, _)) \ s(T)).
%term(us, A --> call_(A, us) # (s(T) / np(_, _)) \ s(T)).
%term(you, A --> call_(A, you) # (s(T) / np(_, _)) \ s(T)).
%term(him, A --> call_(A, him) # (s(T) / np(_, _)) \ s(T)).
%term(her, A --> call_(A, her) # (s(T) / np(_, _)) \ s(T)).
%term(them, A --> call_(A, them) # (s(T) / np(_, _)) \ s(T)).

%% prp, pos :: (s(T) / np(3, _)) \ s(T)
%term(mine, A --> call_(A, mine) # (s(T) / np(_, _)) \ s(T)).
%term(ours, A --> call_(A, ours) # (s(T) / np(_, _)) \ s(T)).
%term(yours, A --> call_(A, yours) # (s(T) / np(_, _)) \ s(T)).
%term(him, A --> call_(A, him) # (s(T) / np(_, _)) \ s(T)).
%term(hers, A --> call_(A, hers) # (s(T) / np(_, _)) \ s(T)).
%term(theirs, A --> call_(A, theirs) # (s(T) / np(_, _)) \ s(T)).

%% n({sg, pl}, {a, an})
term(cat, cat # n(sg, a)).
term(cats, pl(cat) # n(pl, a)).
term(animal, animal # n(sg, an)).
term(animals, pl(animal) # n(pl, an)).

%% adj :: n({a, an}, {a, an}) / n({a, an}) / n({a, an})
term(beautiful, A --> beautiful(A) # n(A, a) / n(A, _)).
term(white, A --> white(A) # n(A, a) / n(A, _)).

%% det :: np({sg, pl}) / n({sg, pl}, {a, an})
term(a, A --> A # np(3, sg) / n(sg, a)).
term(an, A --> A # np(3, sg) / n(sg, an)).
%term(the, A --> the(A) # np(X) / n(X, a)).
%term(the, A --> the(A) # np(X) / n(X, an)).

%% quantifier :: NP/N ... np(A, a) / n(A, _)
%term(a, A --> a(A) # np(3, sg) / n(sg, a)).
term(all, A --> B --> forall_(B, A) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).
term(no, A --> B --> not(forall_(B, A)) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).
term(some, A --> B --> exists_(B, A) # (s(T) / (np(3, pl) \ s(T)) ) / n(pl, _)).

