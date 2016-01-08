/*
Assertions:
-----------

hold_tick(T)
hold_lock(T)
emp(Ticket, Serving)

Contexts:
---------
hd_t(T, Ticket, Serving)
hd_l(Ticket, Serving)

hd_l(T) * hd_t(T) : hd_l_hd_t()
hd_t(T) * hd_t(T) : hd_t_hd_t()
hd_l(T) * hd_l(T) : hd_l_hd_l()
*/

% Solutions:
%-----------
/*
emp(Ticket, Serving) := Ticket >= Serving.
hd_t(T, Ticket, Serving) := Ticket >T.
hd_l(Ticket, Serving) := Ticket > Serving.
hd_l_hd_t(T, Ticket1, Serving) := Serving=\=T.
hd_t_hd_t(_, _, _) := false.
hd_l_hd_l(_, _, _) := false.
*/

query_naming(emp, [ticket, serving]).
query_naming(hd_t, [t, ticket, serving]).
query_naming(hd_l_hd_t, [t, ticket, serving]).
query_naming(hd_l, [ticket, serving]).

/* emp(Ticket, Serving) :- Ticket=0, Serving=0.*/
emp(Ticket, Serving) :- Ticket \= Serving.

% Transition at 4.
emp(Ticket1, Serving) :- emp(Ticket, Serving), T=Ticket, Ticket1=Ticket+1.
hd_t(T, Ticket1, Serving) :- emp(Ticket, Serving), T=Ticket, Ticket1=Ticket+1.
hd_t(T1, Ticket1, Serving) :- emp(Ticket, Serving), hd_t(T1, Ticket, Serving), T=Ticket, Ticket1=Ticket+1.
hd_l(Ticket1, Serving) :- emp(Ticket, Serving),  T=Ticket, Ticket1=Ticket+1, hd_l(Ticket, Serving).
hd_l_hd_t(T, Ticket1, Serving) :- emp(Ticket, Serving), hd_l(Ticket, Serving),  T=Ticket, Ticket1=Ticket+1. 
hd_l_hd_t(T1, Ticket1, Serving) :- emp(Ticket, Serving), hd_l_hd_t(T1, Ticket, Serving), T=Ticket, Ticket1=Ticket+1.
hd_t_hd_t(T, Ticket1, Serving) :- emp(Ticket, Serving), hd_t(Ticket, Ticket, Serving), T=Ticket, Ticket1=Ticket+1.

% Transition at 8.
hd_l(Ticket, Serving) :- emp(Ticket, Serving), hd_t(T, Ticket, Serving), S=Serving, S=T.
%hd_l_hd_t(T1, Ticket, Serving) :- emp(Ticket, Serving),  hd_t(T, Ticket, Serving), hd_t(T1, Ticket, Serving), S=Serving, S=\=T.
hd_l_hd_l(T, Ticket, Serving) :-  emp(Ticket, Serving), hd_l_hd_t(T, Ticket, Serving), hd_t(T, Ticket, Serving), S=Serving, S=T.


% Transition at 16.
emp(Ticket, Serving1) :- emp(Ticket, Serving), hd_l(Ticket, Serving), Serving1=Serving+1.
hd_t(T, Ticket, Serving1) :- emp(Ticket, Serving), hd_l(Ticket, Serving), Serving1=Serving+1, hd_t(T, Ticket, Serving).
hd_l_hd_t(T, Ticket, Serving) :- emp(Ticket, Serving), hd_l(Ticket, Serving), Serving1=Serving+1, hd_t(T, Ticket, Serving), hd_l_hd_t(T, Ticket, Serving).

% Safety.
false :- hd_l_hd_l(T, Ticket, Serving).

