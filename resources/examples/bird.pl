%% Example from: https://personal.utdallas.edu/~gupta/nfm-ex/
%% Author: Gopal Gupta (2025)    %%

flies(X) :- bird(X), not ab(X).
ab(X) :- penguin(X).
bird(X) :- penguin(X).
bird(tweety).
bird(sam). 
penguin(tweety).

% Queries:
?- flies(X).       % X = sam

