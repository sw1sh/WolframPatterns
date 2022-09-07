Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["PatternMatchQ"]
PackageExport["MatchReplace"]
PackageExport["MatchReplaceAll"]
PackageExport["MatchReplaceList"]
PackageExport["MatchPosition"]
PackageExport["ReplaceAllBindings"]
PackageExport["MatchCases"]
PackageExport["MultiwayReplace"]



Replace[Match[match_], rhs_] ^:= MatchReplace[match, Unevaluated[rhs]]

ReplaceList[Match[match_], rhs_] ^:= MatchReplaceList[match, Unevaluated[rhs]]

MatchQ[m_Match[]] ^:= PatternMatchQ[m]


PatternMatchQ[Match[match_]] := Normal[LazyTake[MatchBindings[match], 1]] =!= {}
PatternMatchQ[expr_, patt_] := PatternMatchQ[PatternMatch[Unevaluated[expr], Unevaluated[patt]]]
PatternMatchQ[patt_][expr_] := PatternMatchQ[expr, patt]


MatchReplace[expr_, (Rule | RuleDelayed)[lhs_, rhs_], lvl_ : {0}] := Map[
    Function[
        subExpr,
        Quiet[Check[ReplaceAll[Unevaluated[rhs], ReleaseLazyValue[LazyFirst[MatchBindings[PatternMatch[Unevaluated[subExpr], Unevaluated[lhs]]]]] /. Verbatim[Sequence][x_] :> x], subExpr, Lazy::undef], Lazy::undef],
        HoldAll
    ],
    Unevaluated[expr],
    lvl
]

MatchReplace[expr_, rules_List, lvl_ : {0}] :=
    Fold[Function[rule, MatchReplace[Unevaluated[expr], Unevaluated[rule], lvl], HoldAll], Unevaluated[rules]]

MatchReplace[rules_][expr_] := MatchReplace[Unevaluated[expr], Unevaluated[rules]]

MatchReplace[match_ ? MatchObjectQ, rhs_] := ReplaceAll[Unevaluated[rhs], Normal[LazyTake[MatchBindings[match], 1]] /. Verbatim[Sequence][x_] :> x]


MatchReplaceList[match_ ? MatchObjectQ, rhs_] := LazyMap[ReplaceAll[Unevaluated[rhs], # /. Verbatim[Sequence][x_] :> x] &, MatchBindings[match]]

MatchReplaceList[expr_, (Rule | RuleDelayed)[lhs_, rhs_], n : (_Integer | Infinity) : Infinity] :=
    With[{bind = LazyTake[MatchBindings[PatternMatch[Unevaluated[expr], Unevaluated[lhs]]], n]},
        LazyMap[ReplaceAll[Unevaluated[rhs], # /. Verbatim[Sequence][x_] :> x] &, bind]
    ]

MatchReplaceList[expr_, rules_List, n : (_Integer | Infinity) : Infinity] :=
    LazyTake[n] @ LazyCatenate @ LazyMap[
        Function[
            rule,
            MatchReplaceList[Unevaluated[expr], Unevaluated[rule]],
            HoldAll
        ],
        LazyList[rules]
    ]

MatchReplaceList[rules_][expr_] := MatchReplaceList[Unevaluated[expr], Unevaluated[rules]]


MatchReplaceAll[expr_, rule : (Rule | RuleDelayed)[lhs_, rhs_]] :=
    With[{bind = ReleaseLazyValue @ LazyFirst[MatchBindings[PatternMatch[Unevaluated[expr], Unevaluated[lhs]]], Missing[]]},
        If[ MissingQ[bind],
            Function[subExpr, MatchReplaceAll[Unevaluated[subExpr], Unevaluated[rule]], HoldAll] /@ Unevaluated[expr],
            Unevaluated[rhs] /. bind
        ]
    ]

MatchReplaceAll[expr_, rules_List] :=
    Fold[Function[rule, MatchReplaceAll[Unevaluated[expr], Unevaluated[rule]], HoldAll], Unevaluated[rules]]


Options[MatchPosition] = {Heads -> True}
MatchPosition[expr_, patt_, lvl : _Integer | {Repeated[_Integer, {1, 2}]} | All : All, opts : OptionsPattern[]] := With[{pos = Position[Unevaluated[expr], _, lvl, opts]},
    LazySelect[
        LazyList[pos],
        With[{v = First @ Extract[Unevaluated[expr], {#}, Unevaluated]}, PatternMatchQ[v, patt]] &
    ]
]
MatchPosition[patt_][expr_, opts___] := MatchPosition[Unevaluated[expr], Unevaluated[patt], opts]


Options[ReplaceAllBindings] = {Heads -> True}
ReplaceAllBindings[expr_, patt_, lvl : _Integer | {Repeated[_Integer, {1, 2}]} | All : All, opts : OptionsPattern[]] := With[{pos = Position[Unevaluated[expr], _, lvl, opts]},
    Association @ MapThread[With[{v = Unevaluated @@ #2}, Quiet[Check[#1 -> ReleaseLazyValue[LazyFirst[MatchBindings[PatternMatch[v, patt]]]], Nothing, Lazy::undef]]] &, {pos, Extract[Unevaluated[expr], pos, Hold]}]
]
ReplaceAllBindings[patt_][expr_, opts___] := ReplaceAllBindings[Unevaluated[expr], Unevaluated[patt], opts]


Options[MatchCases] = {Heads -> False}

MatchCases[expr_, patt_, lvl : _Integer | {Repeated[_Integer, {1, 2}]} | All : {1}, opts : OptionsPattern[]] :=
    Extract[Unevaluated[expr], MatchPosition[Unevaluated[expr], patt, lvl, Heads -> OptionValue[Heads]]]

MatchCases[expr_, rules : {(_Rule | _RuleDelayed) ...}, lvl : _Integer | {Repeated[_Integer, {1, 2}]} | All : {1}, opts : OptionsPattern[]] :=
   Catenate @ Replace[Unevaluated[rules], _[lhs_, rhs_] :> (ReplaceAll[Unevaluated[rhs], # /. Verbatim[Sequence][x_] :> x] & /@ Values @ ReplaceAllBindings[Unevaluated[expr], Unevaluated[lhs], lvl, Heads -> OptionValue[Heads]]), {1}]

MatchCases[expr_, rule : _Rule | _RuleDelayed, lvl : _Integer | {Repeated[_Integer, {1, 2}]} | All : {1}, opts : OptionsPattern[]] :=
    MatchCases[Unevaluated[expr], Unevaluated[{rule}], lvl, opts]

MatchCases[pattOrRules_][expr_, opts___] := MatchCases[Unevaluated[expr], Unevaluated[pattOrRules], opts]



MultiwayReplace[rules_, inits_] := Map[
	Function[
		init,
		LazyTree[
			init,
			With[{expr = Replace[Hold[init], Hold[Labeled[expr_, _]] :> Hold[expr]]},
				LazyCatenate @ LazyMap[
					Function[pos, With[{subExpr = Unevaluated @@ Extract[expr, Prepend[pos, 1], Hold]},
                        LazyCatenate @ LazyMap[
                            With[{next = ReplacePart[expr, Prepend[pos, 1] -> #]},
                                With[{labeledNest = Unevaluated @@ Replace[next, Hold[x_] :> Hold[Labeled[x, pos]]]},
                                    MultiwayReplace[rules, labeledNest]
                                ]
                            ] &,
                            MatchReplaceList[subExpr, rules]
                        ]
					]],
					LazyPosition @@ expr
				]
			]
		],
		HoldAll
	],
	LazyList[inits]
]
