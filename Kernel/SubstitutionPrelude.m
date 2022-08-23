Package["Wolfram`Patterns`"]

PackageExport["SubstitutionMatchQ"]
PackageExport["SubstitutionReplace"]
PackageExport["SubstitutionReplaceAll"]
PackageExport["SubstitutionReplaceList"]
PackageExport["SubstitutionPosition"]



SubstitutionMatchQ[expr_, patt_] := PatternSubstitutions[Unevaluated[expr], Unevaluated[patt], 1] =!= SubstitutionSum[]


SubstitutionReplace[expr_, (Rule | RuleDelayed)[lhs_, rhs_], lvl_ : {0}] := Map[
    Function[
        subExpr,
        With[{bind = First[SubstitutionBindings[PatternSubstitutions[Unevaluated[subExpr], Unevaluated[lhs], 1]], Missing[]]},
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

SubstitutionReplace[expr_, rules_List, lvl_ : {0}] :=
    Fold[Function[rule, SubstitutionReplace[Unevaluated[expr], Unevaluated[rule], lvl], HoldAll], Unevaluated[rules]]

SubstitutionReplace[rules_][expr_] := SubstitutionReplace[Unevaluated[expr], Unevaluated[rules]]


SubstitutionReplaceList[expr_, (Rule | RuleDelayed)[lhs_, rhs_], n : (_Integer | Infinity) : Infinity] :=
    With[{bind = SubstitutionBindings[PatternSubstitutions[Unevaluated[expr], Unevaluated[lhs], n]]},
        (Unevaluated[rhs] /. #) & /@ bind
    ]

SubstitutionReplaceList[expr_, rules_List, n : (_Integer | Infinity) : Infinity] :=
    FoldWhile[
        Function[
            {res, rule},
            Join[res, SubstitutionReplaceList[Unevaluated[expr], Unevaluated[rule], n]],
            HoldAll
        ],
        {},
        Unevaluated[rules],
        Length[#1] < n &
    ]

SubstitutionReplaceList[rules_][expr_] := SubstitutionReplaceList[Unevaluated[expr], Unevaluated[rules]]


SubstitutionReplaceAll[expr_, rule : (Rule | RuleDelayed)[lhs_, rhs_]] :=
    With[{bind = First[SubstitutionBindings[PatternSubstitutions[Unevaluated[expr], Unevaluated[lhs], 1]], Missing[]]},
        If[ MissingQ[bind],
            Function[subExpr, SubstitutionReplaceAll[Unevaluated[subExpr], Unevaluated[rule]], HoldAll] /@ Unevaluated[expr],
            Unevaluated[rhs] /. bind
        ]
    ]

SubstitutionReplaceAll[expr_, rules_List] :=
    Fold[Function[rule, SubstitutionReplaceAll[Unevaluated[expr], Unevaluated[rule]], HoldAll], Unevaluated[rules]]


SubstitutionPosition[expr_, patt_, opts___] := With[{pos = Position[Unevaluated[expr], _, opts]},
    Select[
        AssociationThread[pos, With[{subExpr = Unevaluated @@ #}, PatternSubstitutions[subExpr, patt]] & /@ Extract[Unevaluated[expr], pos, Hold]],
        # =!= SubstitutionSum[] &
    ]
]

