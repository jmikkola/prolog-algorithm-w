
% Expressions:
% evar(var_name) -- variable
% elit(Lit) -- literal value
% eapp(Exp1, Exp2) -- function application
% eabs(var_name, Exp) -- function abstraction
% elet(var_name, Exp1, Exp2) -- let

% Literals
% lint(123)
% lbool(true)

% Types
% tvar(var_name)
% tint
% tbool
% tfun(Type, Type)

% Scheme
% scheme([strings], Type)


%%% free_type_variables
%% Instances for Type:

% TVs is a set of atoms
free_type_variables(tvar(N), TVs) :-
    list_to_set([N], TVs).
free_type_variables(tint, []).
free_type_variables(tbool, []).
free_type_variables(tfun(T1, T2), TVs) :-
    free_type_variables(T1, TV1),
    free_type_variables(T2, TV2),
    union(TV1, TV2, TVs).

%% Instances for Scheme:

free_type_variables(scheme(Vars, T), TVs) :-
    free_type_variables(T, TVsT),
    list_to_set(Vars, VarsSet),
    subtract(TVsT, VarsSet, TVs).

%% Instances for a list of things:

free_type_variables([], []).
free_type_variables([T|Ts], TVs) :-
    free_type_variables(T, TVs1),
    free_type_variables(Ts, TVs2),
    union(TVs1, TVs2, TVs).

%% Instances for Type environments:

free_type_variables(typeenv(Env), TVs) :-
    assoc_to_values(Env, Values),
    free_type_variables(Values, TVs).




%%% apply_substitution
%% Instances for Type:

% Sub is a mapping from atom to type
apply_substitution(Sub, tvar(N), T) :-
    get_assoc(N, Sub, T),
    !.
apply_substitution(_, tvar(N), tvar(N)) :-
    !.
apply_substitution(Sub, tfun(T1, T2), tfun(T1s, T2s)) :-
    apply_substitution(Sub, T1, T1s),
    apply_substitution(Sub, T2, T2s),
    !.
apply_substitution(_, tint, tint).
apply_substitution(_, tbool, tbool).

%% Instances for Scheme:

apply_substitution(Sub, scheme(Vars, T), scheme(Vars, Tout)) :-
    del_all_assoc(Vars, Sub, LesserSub),
    apply_substitution(LesserSub, T, Tout).

%% Instances for a list of things:

apply_substitution(_, [], []).
apply_substitution(Sub, [T|Ts], [To|Tos]) :-
    apply_substitution(Sub, T, To),
    apply_substitution(Sub, Ts, Tos).

%% Instances for Type environments:

apply_substitution(Sub, typeenv(Env0), typeenv(Env)) :-
    map_assoc(Env0, apply_substitution(Sub), Env).




%%% Substitution

null_substitution(Sub) :-
    empty_assoc(Sub).

compose_subst(Sub1, Sub2, Sub) :-
    map_assoc(Sub2, apply_substitution(Sub1), Applied),
    map_union(Applied, Sub1, Sub).




%%% Type environments

remove(typeenv(Env0), Var, typeenv(Env)) :-
    map_delete(Env0, Var, Env).

generalize(typeenv(Env), Type, scheme(Vars, Type)) :-
    free_type_variables(Type, FtvT),
    free_type_variables(typeenv(Env), FtvE),
    subtract(FtvT, FtvE, Vars).


instantiate(scheme(Vars, Type0), Type) :-
    make_sub(Vars, Sub),
    apply_substitution(Sub, Type0, Type).


% helper for instantiate:
make_sub([], Sub) :-
    empty_assoc(Sub).
make_sub([V|Vs], Sub) :-
    make_sub(Vs, Sub0),
    gensym(tv_, Vnew),
    put_assoc(V, Sub0, tvar(Vnew), Sub).


%%% Actual type inference!

% most_general_unifier(T1, T2, Sub)
most_general_unifier(tfun(L1, R1), tfun(L2, R2), Sub) :-
    most_general_unifier(L1, L2, Sub1),
    apply_substitution(Sub1, R1, R1s),
    apply_substitution(Sub1, R2, R2s),
    most_general_unifier(R1s, R2s, Sub2),
    compose_subst(Sub1, Sub2, Sub),
    !.
most_general_unifier(tvar(U), T, Sub) :-
    var_bind(tvar(U), T, Sub), !.
most_general_unifier(T, tvar(U), Sub) :-
    var_bind(tvar(U), T, Sub), !.
most_general_unifier(tint, tint, Sub) :-
    empty_assoc(Sub), !.
most_general_unifier(tbool, tbool, Sub) :-
    empty_assoc(Sub), !.
most_general_unifier(T1, T2, _) :-
    format(atom(Err), 'cannot unify types ~w and ~w', [T1, T2]),
    throw(Err).

var_bind(tvar(U), tvar(U), Sub) :-
    empty_assoc(Sub).
var_bind(tvar(U), Type, _) :-
    free_type_variables(Type, Ftv),
    member(U, Ftv),
    format(atom(Err), 'occur check fails for ~w ~w', [tvar(U), Type]),
    throw(Err).
var_bind(tvar(U), Type, Sub) :-
    empty_assoc(Sub0),
    put_assoc(U, Sub0, Type, Sub).

literal_type(lint(_), tuple(NullSub, tint)) :-
    empty_assoc(NullSub).
literal_type(lbool(_), tuple(NullSub, tbool)) :-
    empty_assoc(NullSub).

infer(typeenv(_), elit(Literal), tuple(Sub, Type)) :-
    literal_type(Literal, tuple(Sub, Type)).
infer(typeenv(Env), evar(N), tuple(Sub, Type)) :-
    get_var_from_env(typeenv(Env), N, Sigma),
    instantiate(Sigma, Type),
    empty_assoc(Sub).
infer(typeenv(Env), eabs(N, Expr), tuple(Sub, tfun(tvar(TVsub), Type1))) :-
    gensym(tv_, TV),
    put_assoc(N, Env, scheme([], tvar(TV)), Env1),
    infer(typeenv(Env1), Expr, tuple(Sub, Type1)),
    apply_substitution(Sub, tvar(TV), tvar(TVsub)).
infer(typeenv(Env), eapp(Expr1, Expr2), tuple(Sub, TVsub)) :-
    gensym(tv_, TV),
    infer(typeenv(Env), Expr1, tuple(Sub1, Type1)),
    apply_substitution(Sub1, typeenv(Env), typeenv(EnvSub)),
    infer(typeenv(EnvSub), Expr2, tuple(Sub2, Type2)),
    apply_substitution(Sub2, Type1, Type1sub),
    most_general_unifier(Type1sub, tfun(Type2, tvar(TV)), Sub3),
    compose_subst(Sub3, Sub2, Sub32),
    compose_subst(Sub32, Sub1, Sub),
    apply_substitution(Sub3, tvar(TV), TVsub).
infer(typeenv(Env), elet(X, Expr1, Expr2), tuple(Sub, Type)) :-
    infer(typeenv(Env), Expr1, tuple(Sub1, Type1)),
    remove(typeenv(Env), X, typeenv(Env1)),
    apply_substitution(Sub1, typeenv(Env), typeenv(EnvSub)),
    generalize(typeenv(EnvSub), Type1, Type1G),
    put_assoc(X, Env1, Type1G, Env2),
    apply_substitution(Sub1, typeenv(Env2), typeenv(Env2Sub)),
    infer(typeenv(Env2Sub), Expr2, tuple(Sub2, Type)),
    compose_subst(Sub1, Sub2, Sub).

type_infer(typeenv(Env), Expr, Type) :-
    infer(typeenv(Env), Expr, tuple(Sub1, Type1)),
    apply_substitution(Sub1, Type1, Type).

% Helper for infer
get_var_from_env(typeenv(Env), N, Sigma) :-
    get_assoc(N, Env, Sigma), !.
get_var_from_env(typeenv(_), N, _) :-
    format(atom(Err), 'variable not defined: ~w', [N]),
    throw(Err).

%%% Helper functions:

% Delete multiple keys from an association
del_all_assoc([], Assoc, Assoc).
del_all_assoc([K|Ks], Assoc, AssocOut) :-
    map_delete(Assoc, K, Assoc1),
    del_all_assoc(Ks, Assoc1, AssocOut).

% Map a function over the values in an assoc
map_assoc(A, _, A) :-
    empty_assoc(A).
map_assoc(Assoc0, Fn, Assoc1) :-
    del_min_assoc(Assoc0, Key, Val, Assoc0b),
    call(Fn, Val, Result),
    map_assoc(Assoc0b, Fn, Assoc1b),
    put_assoc(Key, Assoc1b, Result, Assoc1).

% Unions two maps. If a key appears in both maps, the left map wins.
map_union(M1, M, M) :-
    empty_assoc(M1).
map_union(M1, M2, M) :-
    del_min_assoc(M1, Key, Val, M1b),
    map_union(M1b, M2, Mb),
    put_assoc(Key, Mb, Val, M).

map_delete(Assoc0, Key, Assoc) :-
    del_assoc(Key, Assoc0, _, Assoc), !.
% Handle the case where the key is not in the map
map_delete(Assoc0, _, Assoc0).


%%% Examples

show_example(Expr) :-
    empty_assoc(Env0),
    type_infer(typeenv(Env0), Expr, T),
    format('~w\n', [T]).

example1 :-
    show_example(elet(id, eabs(x, evar(x)), evar(id))).

example2 :-
    show_example(
        elet(
            id, eabs(x, evar(x)),
            eapp(evar(id), evar(id))
        )
    ).

example3 :-
    show_example(
        elet(
            id,
            eabs(x, elet(y, evar(x), evar(y))),
            eapp(evar(id), evar(id))
        )
    ).


% Should fail:
example6 :-
    show_example(
        eapp(elit(lint(2)), elit(lint(3)))
    ).
