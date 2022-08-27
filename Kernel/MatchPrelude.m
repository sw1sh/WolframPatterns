Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["PatternMatchQ"]
PackageExport["MatchReplace"]
PackageExport["MatchReplaceAll"]
PackageExport["MatchReplaceList"]
PackageExport["MatchPosition"]



PatternMatchQ[expr_, patt_] := Normal[LazyTake[MatchBindings[PatternMatch[Unevaluated[expr], Unevaluated[patt]]], 1]] =!= {}


MatchReplace[expr_, (Rule | RuleDelayed)[lhs_, rhs_], lvl_ : {0}] := Map[
    Function[
        subExpr,
        With[{bind = ReleaseLazyValue @ LazyFirst[MatchBindings[PatternMatch[Unevaluated[subExpr], Unevaluated[lhs]]], Missing[]]},
            If[ MissingQ[bind],
                subExpr,
                Unevaluated[rhs] /. bind
            ]
        ],
        HoldAll
    ],
    Unevaluated[expr],
    lvl
]

MatchReplace[expr_, rules_List, lvl_ : {0}] :=
    Fold[Function[rule, MatchReplace[Unevaluated[expr], Unevaluated[rule], lvl], HoldAll], Unevaluated[rules]]

MatchReplace[rules_][expr_] := MatchReplace[Unevaluated[expr], Unevaluated[rules]]


MatchReplaceList[expr_, (Rule | RuleDelayed)[lhs_, rhs_], n : (_Integer | Infinity) : Infinity] :=
    With[{bind = LazyTake[MatchBindings[PatternMatch[Unevaluated[expr], Unevaluated[lhs]]], n]},
        LazyMap[Unevaluated[rhs] /. # &, bind]
    ]

MatchReplaceList[expr_, rules_List, n : (_Integer | Infinity) : Infinity] :=
    FoldWhile[
        Function[
            {res, rule},
            Join[res, MatchReplaceList[Unevaluated[expr], Unevaluated[rule], n - Length[res]]],
            HoldAll
        ],
        {},
        Unevaluated[rules],
        Length[#1] < n &
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


MatchPosition[expr_, patt_, opts___] := With[{pos = Position[Unevaluated[expr], _, opts]},
    Select[
        AssociationThread[pos, With[{subExpr = Unevaluated @@ #}, LazyListToList[MatchExpand[PatternMatch[subExpr, patt]]]] & /@ Extract[Unevaluated[expr], pos, Hold]],
        # =!= MatchSum[] &
    ]
]

