Package["Wolfram`Patterns`"]

PackageExport["UnifyPatterns"]



simplifySubstitution[u_Association] := Pick[u, KeyValueMap[! MatchQ[#2, HoldComplete[Verbatim[Pattern][#1, ___]]] &, HoldComplete /@ u]]

substitutionChoices[u_Association] /; Length[u] <= 1 := {u}
substitutionChoices[u_Association] := DeleteDuplicates @ Map[KeySort] @ Catenate @ Table[
	With[{subst = u[[i ;; i]]},
		Join[applySubstitution[subst, #], #] & /@ substitutionChoices @ simplifySubstitution @ applySubstitution[Join[u[[;; i - 1]], u[[i + 1 ;;]]], subst]
	],
	{i, Range[Length[u]]}
]

applySubstitution[expr_, u_Association] := expr /. Normal @ KeyMap[Verbatim[Pattern][#, _] & , u]

combineSubstitutions[xs : {_Association...}, ys : {_Association...}] :=
	DeleteDuplicates @ Catenate @ Map[substitutionChoices] @ DeleteDuplicates @ Map[MapValues[UnevaluatedFirst]] @ Select[
		MergeIdentity /@ Tuples[{xs, ys}],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	]

PatternHead = Pattern |
	Blank | BlankSequence | BlankNullSequence |
	HoldPattern | Verbatim |
	Alternatives | Except |
	PatternSequence | OrderlessPatternSequence | Repeated |
	Longest | Shortest |
	PatternTest | Condition |
	Optional | OptionsPattern | KeyValuePattern | IgnoringInactive;


(* Alternatives *)
UnifyPatterns[OrderlessPatternSequence[head_[left___, Verbatim[Alternatives][xs___], right___], head_[y___]]] /; !MatchQ[head, PatternHead] :=
	DeleteDuplicates @ Map[KeySort] @ Catenate @ Tuples[DeleteCases[Function[Null, UnifyPatterns[Unevaluated @ head[left, #, right], Unevaluated @ head[y]], HoldAllComplete] /@ Unevaluated @ {xs}, {}]]

UnifyPatterns[OrderlessPatternSequence[Verbatim[Alternatives][xs___], y_]] :=
	DeleteDuplicates @ Map[KeySort] @ Catenate @ Tuples[DeleteCases[Function[Null, UnifyPatterns[Unevaluated @ #, Unevaluated @ y], HoldAllComplete] /@ Unevaluated @ {xs}, {}]]

(* HoldPattern *)
UnifyPatterns[Verbatim[HoldPattern][x_], Verbatim[HoldPattern][y_]] := UnifyPatterns[Unevaluated[x], Unevaluated[y]]
UnifyPatterns[OrderlessPatternSequence[Verbatim[HoldPattern][x_], y_]] := UnifyPatterns[Unevaluated[x], y]

(* Pattern *)
UnifyPatterns[OrderlessPatternSequence[Verbatim[Except][except_, patt_], y_]] := Select[UnifyPatterns[Unevaluated @ patt, Unevaluated @ y], !MatchQ[applySubstitution[y, #], except] &]

UnifyPatterns[px : Verbatim[Pattern][x_, _], py : Verbatim[Pattern][y_, _]] := {<|x :> py|>, <|y :> px|>}
UnifyPatterns[Verbatim[Pattern][x_, _], Verbatim[Pattern][x_, _]] := {<||>}
UnifyPatterns[OrderlessPatternSequence[Verbatim[Pattern][x_, patt_], y : Except[Blank /@ PatternHead]]] := Join[<|x :> y|>, #] & /@ UnifyPatterns[Unevaluated @ patt, Unevaluated @ y]

UnifyPatterns[OrderlessPatternSequence[Verbatim[PatternTest][patt_, test_], y : Except[Blank /@ PatternHead]]] := Select[UnifyPatterns[Unevaluated @ patt, Unevaluated @ y], test[applySubstitution[patt, #]] &]

UnifyPatterns[OrderlessPatternSequence[Verbatim[Condition][patt_, test_], y : Except[Blank /@ PatternHead]]] := Select[UnifyPatterns[Unevaluated @ patt, Unevaluated @ y], ReleaseHold[HoldComplete[test] /. #] &]

(* Verbatim *)
UnifyPatterns[OrderlessPatternSequence[x_, y : Verbatim[Verbatim][_]]] := If[MatchQ[Unevaluated[x], HoldPattern[y]], {<||>}, {}]

(* BlankSequence and BlankNullSequence *)

(* on the left head[x___, ___] *)
UnifyPatterns[OrderlessPatternSequence[
	head_[Verbatim[Pattern][x_, blank : Verbatim[__] | Verbatim[___]] | blank : Verbatim[__] | Verbatim[___], rest___],
	head_[y___]
]] /; !MatchQ[head, PatternHead] :=
	DeleteDuplicates @ Map[KeySort] @ Catenate[
		With[{u = UnifyPatterns[head[rest], head @@ #2]}, If[HoldComplete[x] === HoldComplete[], u, combineSubstitutions[{<|x -> Sequence @@ #1|>}, u], u]] & @@
			TakeDrop[{y}, #] & /@ Range[If[blank === ___, 0, 1], Length[{y}]]
	]

(* on the right head[___, x___] *)
UnifyPatterns[OrderlessPatternSequence[
	head_[rest___, Verbatim[Pattern][x_, blank : Verbatim[__] | Verbatim[___]] | blank : Verbatim[__] | Verbatim[___]],
	head_[y___]
]] /; !MatchQ[head, PatternHead] :=
	DeleteDuplicates @ Map[KeySort] @ Catenate[
		With[{u = UnifyPatterns[head[rest], head @@ #1]}, If[HoldComplete[x] === HoldComplete[], u, combineSubstitutions[{<|x -> Sequence @@ #2|>}, u], u]] & @@
			TakeDrop[{y}, #] & /@ Range[Length[{y}], If[blank === ___, 0, 1], -1]
	]

(* PatternSequence *)
UnifyPatterns[OrderlessPatternSequence[
	head_[Verbatim[PatternSequence][seq___], rest___],
	head_[y___]
]] /; !MatchQ[head, PatternHead] := UnifyPatterns[Unevaluated @ head[seq, rest], Unevaluated @ head[y]]

UnifyPatterns[OrderlessPatternSequence[
	head_[rest___, Verbatim[PatternSequence][seq___]],
	head_[y___]
]] /; !MatchQ[head, PatternHead] := UnifyPatterns[Unevaluated @ head[rest, seq], Unevaluated @ head[y]]

UnifyPatterns[OrderlessPatternSequence[Verbatim[PatternSequence][seq___], y_]] := UnifyPatterns[HoldComplete[seq], Unevaluated[y]]

UnifyPatterns[OrderlessPatternSequence[
	head_[left___, Verbatim[Repeated][patt_, spec___], right___],
	head_[y___]
]] /; !MatchQ[head, PatternHead] := With[{
	mid = Replace[HoldComplete[spec], {
		HoldComplete[n_Integer ? Positive] :> Alternatives @@ (PatternSequence @@ Table[Unevaluated @ patt, #] & /@ Range[0, n]),
		HoldComplete[{n_Integer ? Positive, m_Integer ? Positive}] :> Sequence @@ Table[Unevaluated @ patt, Range[n, m]],
		HoldComplete[{n_Integer ? Positive}] :> Sequence @@ Table[Unevaluated @ patt, n],
		HoldComplete[] :> PatternSequence[]
	}]
},
	UnifyPatterns[head[left, mid, right], Unevaluated @ head[y]]
]

(* OrderlessPatternSequence *)
UnifyPatterns[OrderlessPatternSequence[
	head_[Verbatim[OrderlessPatternSequence][seq___], rest___],
	head_[y___]
]] /; !MatchQ[head, PatternHead] := With[{holdRest = HoldComplete @@ HoldComplete /@ Unevaluated[{rest}]},
	DeleteDuplicates @ Map[KeySort] @ Catenate[
		With[{splice = Flatten @ Join[holdRest, HoldComplete[##]]}, UnifyPatterns[splice, HoldComplete[y]]] & @@@ Permutations[HoldComplete /@ Unevaluated @ {seq}]
	]
]

UnifyPatterns[OrderlessPatternSequence[
	head_[rest___, Verbatim[OrderlessPatternSequence][seq___]],
	head_[y___]
]] /; !MatchQ[head, PatternHead] := With[{holdRest = HoldComplete @@ HoldComplete /@ Unevaluated[{rest}]},
	DeleteDuplicates @ Map[KeySort] @ Catenate[
		With[{splice = Flatten @ Join[HoldComplete[##], holdRest]}, UnifyPatterns[splice, HoldComplete[y]]] & @@@ Permutations[HoldComplete /@ Unevaluated @ {seq}]
	]
]

UnifyPatterns[OrderlessPatternSequence[Verbatim[OrderlessPatternSequence][seq___], y_]] := UnifyPatterns[HoldComplete[OrderlessPatternSequence[seq]], HoldComplete[y]]

(* Head sequence *)
UnifyPatterns[head1_[x___], head2_[y___]] /; !MatchQ[Unevaluated @ head1, PatternHead] && !MatchQ[Unevaluated @ head2, PatternHead] :=
	If[ Length[Unevaluated @ {x}] == Length[Unevaluated @ {y}],
		With[{u = UnifyPatterns[Unevaluated @ head1, Unevaluated @ head2]},
			If[ u === {},
				{},
				combineSubstitutions[
					u,
					FoldWhile[
						combineSubstitutions[#1, UnifyPatterns @@ #2] &,
						{<||>},
						Thread[{HoldPattern /@ Unevaluated @ {x}, HoldPattern /@ Unevaluated @ {y}}],
						# =!= {} &
					]
				]
			]
		],
		{}
	]

UnifyPatterns[x_, x_] := {<||>}

UnifyPatterns[OrderlessPatternSequence[x_, y : Except[Blank[PatternHead]]]] /; MatchQ[x, y] := {<||>} 

UnifyPatterns[x_, y_] := {}

