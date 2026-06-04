%% Example from: https://personal.utdallas.edu/~gupta/nfm-ex/
%% Author: Gopal Gupta (2025)    %%

person(john).
person(sam).
person(alice).
person(bill).
person(bob).

gender(male).
gender(female).

father(john,sam).
father(john,bill).

mother(alice,sam).
mother(alice,bill).

gender_of(john,male).
gender_of(alice,female).
gender_of(sam,male).
gender_of(bill,male).

parent(X,Y) :- father(X,Y).
parent(X,Y) :- mother(X,Y).

child(X,Y) :- parent(Y,X).

brother(X,Y) :- gender_of(X,male),
                father(F,X),
                father(F,Y),
                mother(M,X),
                mother(M,Y),
                X \= Y.

-father(X,Y) :- person(Y), gender_of(X,female).

-father(X,Y) :- person(X),                  % safe rule 
                father(Z,Y),   X \= Z. 


% Queries: 
?- brother(X,Y).         % X = sam, Y = bill | ...
