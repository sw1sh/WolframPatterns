Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["PatternMatch"]
PackageExport["SequenceSplits"]
PackageExport["ShortestTriples"]
PackageExport["LongestTriples"]


SequenceSplits[args_, emptyRight_ : False, defaultMode_ : Automatic] := With[{mode = Replace[defaultMode, Except[Longest | Shortest] -> Shortest]},
    If[ TrueQ[emptyRight],
        MatchSum[{args, HoldComplete[]}],
        LazyMap[ConsToList] @ Switch[mode,
            Shortest,
            LazySplits[args, MatchSum],
            Longest,
            LazySplitsReverse[args, MatchSum]
        ]
    ]
]

ShortestTriples[xs_] := ToLazyList[
    LazyMap[ConsToList] @ LazyCatenate @ LazyMap[n |-> LazyCatenate @ LazyMap[split |-> With[{first = LazyFirst[split]},
	    If[Length[xs] - Length[first] < n, LazyList[], LazyMap[LazyList[first, ToLazyList[TakeDrop[#, UpTo[n]]]] &, LazyRest[split]]]], LazySplits[xs]], LazyRange[0, Length[xs]]],
    MatchSum
]

LongestTriples[xs_] := ToLazyList[
    LazyMap[ConsToList] @ LazyCatenate @ LazyMap[n |-> LazyCatenate @ LazyMap[split |-> With[{first = LazyFirst[split]},
	    If[Length[xs] - Length[first] < n, LazyList[], LazyMap[LazyList[first, ToLazyList[TakeDrop[#, UpTo[n]]]] &, LazyRest[split]]]], LazySplitsReverse[xs]], LazyRange[Length[xs], 0, -1]],
    MatchSum
]


PatternMatch[expr_, patt_] := PatternMatch[Unevaluated[expr], Unevaluated[patt], Infinity]


PatternMatch[head_Symbol[args___], head_Symbol[patt___]] /;
    Not[Length[Unevaluated[{patt}]] == 1 && Head[Unevaluated[patt]] === OrderlessPatternSequence] && MemberQ[Attributes[head], Orderless] :=
    Block[{h},
        SetAttributes[h, DeleteCases[Attributes[head], Orderless]];
        PatternMatch[Unevaluated[h[args]], Unevaluated[h[OrderlessPatternSequence[patt]]]] /. h :> head
    ]


(* Shortest *)

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Shortest][patt_], right___]] := With[{
    l = Length[Hold[left]], r = Length[Hold[right]]
},
    LazyMap[Apply[
        If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
            MatchSum[],
            MatchProduct[
                If[ l == 0,
                    MatchValues[],
                    MatchPart[{1},
                        HoldPattern[head[left]],
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                            LazyMap[
                                Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                                ReleaseLazy @ PatternMatch[val, Unevaluated[head[left]]]
                            ]
                        ]
                    ]
                ],
                MatchPart[{l + 1},
                    HoldPattern[mid],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                        LazyMap[
                            Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[patt]]]
                        ]
                    ]
                ],
                If[ r == 0,
                    MatchValues[],
                    MatchPart[{l + 2},
                        HoldPattern[head[right]],
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#3]},
                            LazyMap[
                                Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                                ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                            ]
                        ]
                    ]
                ]
            ]
        ] &
    ],
        ShortestTriples[HoldComplete[args]]
    ]
]


(* Longest *)

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Longest][patt_], right___]] := With[{
    l = Length[HoldComplete[left]], r = Length[HoldComplete[right]]
},
    LazyMap[Apply[
        If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
            MatchSum[],
            MatchProduct[
                If[ l == 0,
                    MatchValues[],
                    MatchPart[{1},
                        HoldPattern[head[left]],
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                            LazyMap[
                                Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                                ReleaseLazy @ PatternMatch[val, Unevaluated[head[left]]]
                            ]
                        ]
                    ]
                ],
                MatchPart[{l + 1},
                    HoldPattern[mid],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                        LazyMap[
                            Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[patt]]]
                        ]
                    ]
                ],
                If[ r == 0,
                    MatchValues[],
                    MatchPart[{l + 2},
                        HoldPattern[head[right]],
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#3]},
                            LazyMap[
                                Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                                ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                            ]
                        ]
                    ]
                ]
            ]
        ] &
    ],
        LongestTriples[HoldComplete[args]]
    ]
]


(* Pattern *)

PatternMatch[expr_, patt : Verbatim[Pattern][_Symbol, subPatt_]] :=
	MatchPart[{}, HoldPattern[patt], MatchPart[{}, HoldPattern[subPatt], ReleaseLazy @ PatternMatch[Unevaluated[expr], Unevaluated[subPatt]]]]

PatternMatch[head_Symbol[args___], head_Symbol[mid : Verbatim[Pattern][_Symbol, patt_], right___]] :=
    LazyMap[Apply[
        If[ Length[HoldComplete[right]] == 0,
            If[ Length[#2] > 0,
                MatchSum[],
                MatchPart[{1},
                    HoldPattern[mid],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[patt]]]
                        ]
                    ]
                ]
            ],
            MatchProduct[
                MatchPart[{1},
                    HoldPattern[mid],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[patt]]]
                        ]
                    ]
                ],
                MatchPart[{2},
                    HoldPattern[head[right]],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                        ]
                    ]
                ]
            ]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* Blank *)

PatternMatch[expr_, Verbatim[Blank][], _] := MatchValues[expr]

PatternMatch[expr_, Verbatim[Blank][h_]] := With[{head = Unevaluated @@ Head[Unevaluated[expr], HoldComplete]},
	MatchProduct[PatternMatch[head, h], MatchValues[expr]]]

PatternMatch[head_Symbol[args___], head_Symbol[Verbatim[Blank][h___], right___]] :=
    LazyMap[Apply[
        If[ Length[HoldComplete[right]] == 0,
            If[ Length[#2] > 0, MatchSum[],
                MatchPart[{1}, HoldPattern[Blank[h]],
                    HoldApply[
                        If[(MemberQ[Attributes[head], Flat] || MemberQ[Attributes[head], OneIdentity]), head, Sequence],
                        #1,
                        MatchValues
                    ]
                ]
            ],
            MatchProduct[
                MatchPart[{1}, HoldPattern[Blank[h]],
                    HoldApply[
                        If[(MemberQ[Attributes[head], Flat] || MemberQ[Attributes[head], OneIdentity]), head, Sequence],
                        #1,
                        MatchValues
                    ]
                ],
                LaztPartSubstitution[{2},
                    HoldPattern[head[right]],
                    With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                        ]
                    ]
                ]
            ]
        ] &],
        If[ MemberQ[Attributes[head], Flat], Identity, LazySelect[#, MatchQ[#[[1]], HoldComplete[_h]] &] &] @
            SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* BlankSequence *)

PatternMatch[head_Symbol[args__], head_Symbol[Verbatim[BlankSequence][h___], right___]] :=
	LazyMap[Apply[
        If[ Length[HoldComplete[right]] == 0,
            If[Length[#2] > 0, MatchSum[], MatchPart[{1}, HoldPattern[BlankSequence[h]], HoldApply[Sequence, #1, MatchValues]]],
            MatchProduct[
                MatchPart[{1}, HoldPattern[BlankSequence[h]], HoldApply[Sequence, #1, MatchValues]],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    MatchPart[{2}, HoldPattern[head[right]],
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                        ]
                    ]
                ]
            ]
		] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[__h]] &
		]
	]


(* BlankNullSequence *)

PatternMatch[head_Symbol[args___], head_Symbol[Verbatim[BlankNullSequence][h___], right___]] :=
	LazyMap[Apply[
        If[ Length[HoldComplete[right]] == 0,
            If[Length[#2] > 0, MatchSum[], MatchPart[{1}, HoldPattern[BlankNullSequence[h]], HoldApply[Sequence, #1, MatchValues]]],
            MatchProduct[
                MatchPart[{1}, HoldPattern[BlankNullSequence[h]], HoldApply[Sequence, #1, MatchValues]],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    MatchPart[{2}, HoldPattern[head[right]],
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                        ]
                    ]
                ]
            ]
		] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[___h]] &
		]
	]


(* OrderlessPatternSequence *)

PatternMatch[head_Symbol[args___], head_Symbol[mid : Verbatim[OrderlessPatternSequence][patt___], right___]] :=
    LazyMap[Apply[
        If[ Length[HoldComplete[right]] == 0,
            If[ Length[#2] > 0, MatchSum[],
                MatchPart[{1}, HoldPattern[mid],
                    LazyMap[
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#]}, PatternMatch[val, head[patt]]] &,
                        ToLazyList[LazyPermutations[#1], MatchSum]
                    ]
                ]
            ],
            MatchProduct[
                MatchPart[{1}, HoldPattern[mid],
                    LazyMap[
                        With[{val = Unevaluated @@ head @@@ HoldComplete[#]}, PatternMatch[val, head[patt]]] &,
                        ToLazyList[LazyPermutations[#1], MatchSum]
                    ]
                ],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    MatchPart[{2}, HoldPattern[head[right]],
                        LazyMap[
                            Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                        ]
                    ]
                ]
            ]
		] &],
		SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
	]


(* PatternSequence *)

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[PatternSequence][patt___], right___], n_] :=
    FoldTakeWhile[
		With[{
            valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]},
            valMid = Unevaluated @@ head @@@ HoldComplete @@ {#[[2]]},
            valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}
        },
			SubstitutionExpand[
				SubstitutionMerge[
                    If[ Length[HoldComplete[left]] > 0,
					    PartSubstitution[{1}, HoldPattern[head[left]], PatternMatch[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
					PartSubstitution[{Length[HoldComplete[left]] + 1}, HoldPattern[mid], PatternMatch[valMid, Unevaluated[head[patt]]]],
                    If[ Length[HoldComplete[right]] > 0,
					    PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternMatch[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
		tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n,
        SubstitutionSum
	]


(* RepeatedNull *)

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[RepeatedNull][patt_, spec_ : Infinity], right___], n_] := Block[{
    shift = Length[HoldComplete[left]],
    min = Replace[spec, {{k_} :> k, {min_, _} :> min, _ -> 0}],
    max = Replace[spec, {{k_} :> k, {_, max_} :> max}],
    numRepeats,
    i = 0,
    rest
},
    numRepeats = max - min + 1;
	FoldTakeWhile[
        Apply[
        SubstitutionExpand[
            SubstitutionMerge[
                With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternMatch[val, Unevaluated[head[left]]]],
                PartSubstitution[{shift + 1},
                    HoldPattern[mid],
                    SubstitutionSum @@ NestWhile[
                        With[{
                            p = If[
                                i == 0,
                                Unevaluated @@ head @@@ HoldComplete @@ {Append[Flatten[HoldComplete @@ Table[HoldComplete[patt], min]], rest___]},
                                Unevaluated @@ {head[patt, rest___]}
                            ]
                        },
                            i++;
                            Map[
                                With[{
                                    prevSubst = #[[1]], len = Length[#[[2]]],
                                    val = Unevaluated @@ head @@@ HoldComplete @@ {#[[2]]}
                                },
                                    Which[
                                        (* input sequence is empty*)
                                        len == 0,
                                        {If[i == 1 && min > 0, SubstitutionSum[], prevSubst], #[[2]]},
                                        (* last iteration but input is not empty *)
                                        i == numRepeats + 1,
                                        {SubstitutionSum[], #[[2]]},
                                        True,
                                        Splice @ Block[{subst = SubstitutionExpand @ PatternMatch[val, p]},
                                            With[{next = HoldComplete @@ Lookup[First @ SubstitutionBindings[#], rest, Null, Hold]},
                                                If[ Length[next] <= len,
                                                    {
                                                        SubstitutionProduct[
                                                            prevSubst,
                                                            (* replace with dummy sequence *)
                                                            # /. PartSubstitution[{2}, Verbatim[HoldPattern][Verbatim[Pattern][rest, _]], _] -> SubstitutionValues[Sequence[]]
                                                        ],
                                                        next
                                                    },
                                                    Nothing
                                                ]
                                            ] & /@ List @@ subst
                                        ]
                                    ]
                                ] &,
                                #
                            ]
                        ] &,
                        {{SubstitutionValues[], #2}},
                        i == 0 || AnyTrue[#[[All, 2]], Length[#] > 0 &] &,
                        1,
                        numRepeats,
                        1
                    ][[;; UpTo[n], 1]]
                ],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternMatch[val, Unevaluated[head[right]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
            ],
            n
        ] &],
        tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
        n,
        SubstitutionSum
    ]
]


(* Repeated *)

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Repeated][patt_, spec_ : Infinity], right___], n_] := With[{
    newSpec = Replace[spec, {k : Except[_List] :> {1, k}}]
},
    PatternMatch[Unevaluated[head[args]], Unevaluated[head[left, RepeatedNull[patt, newSpec], right]], n]
]


(* HoldPattern *)

PatternMatch[expr_, Verbatim[HoldPattern][patt_]] := PatternMatch[Unevaluated[expr], Unevaluated[patt]]


(* Verbatim *)

PatternMatch[expr_, Verbatim[Verbatim][expr_]] := MatchValues[]


(* Except *)

PatternMatch[expr_, Verbatim[Except][patt_, t___]] := With[{
	subst = PatternMatch[Unevaluated[expr], Unevaluated[patt]]
},
	If[ Normal[LazyTake[LazySubstitutionBindings[subst], 1]] === {},
		MatchProduct[
            MatchDefault[Unevaluated[patt]],
            If[ HoldComplete[t] === HoldComplete[],
                MatchValues[expr],
                PatternMatch[Unevaluated[expr], Unevaluated[t]]
            ]
        ],
		MatchSum[]
	]
]


PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Except][patt_, t___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternMatch[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    With[{
                        subst = PatternMatch[val, Unevaluated[head[patt]], 1]
                    },
                        If[ subst === SubstitutionSum[],
                            SubstitutionProduct[
                                DefaultSubstitutions[Unevaluated[head[patt]]],
                                If[ HoldComplete[t] === HoldComplete[],
                                    SubstitutionValues @@ #2,
                                    PatternMatch[val, Unevaluated[head[t]], n]
                                ]
                            ],
                            SubstitutionSum[]
                        ]
                    ]
                ] /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternMatch[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n
	]
]


(* Alternatives *)

PatternMatch[expr_, Verbatim[Alternatives][alts___]] :=
    LazyMap[
        Function[alt, MatchPart[{}, HoldPattern[alt], PatternMatch[Unevaluated[expr], Unevaluated[alt]]], HoldAll],
        ToLazyList[Hold[alts], MatchSum]
    ]

PatternMatch[head_Symbol[args___], head_Symbol[mid : Verbatim[Alternatives][alts___], right___]] :=

    LazyMap[Apply[MatchProduct[
        MatchPart[{1},
            HoldPattern[mid],
            With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                LazyMap[
                    Function[alt, MatchPart[{}, HoldPattern[alt],
                        LazyMap[
                            Replace[MatchPart[part_, rest__] :> MatchPart[Rest[part], rest]],
                            ReleaseLazy @ PatternMatch[val, Unevaluated[head[alt]]]
                        ]
                    ], HoldAll],
                    ToLazyList[Hold[alts], MatchSum]
                ]
            ]
        ],
        With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
            MatchPart[{2}, HoldPattern[head[right]],
                LazyMap[
                    Replace[MatchPart[part_, rest___] :> MatchPart[Rest[part], rest]],
                    ReleaseLazy @ PatternMatch[val, Unevaluated[head[right]]]
                ]
            ]
        ]
    ] &], SequenceSplits[HoldComplete[args]]]



(* Optional *)

PatternMatch[expr_, Verbatim[Optional][patt_, def___], n_] := SubstitutionSum[
    PatternMatch[Unevaluated[expr], Unevaluated[patt], n],
    PartSubstitution[
        {},
        Replace[HoldPattern[patt], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
        If[HoldComplete[def] === HoldComplete[], SubstitutionValues[Sequence[]], SubstitutionValues[def]]
    ]
]


PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Optional][patt_, def___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[SubstitutionSum @@ Map[Apply[
        Block[{
            lsubst = If[Length[HoldComplete[left]] > 0,
                With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternMatch[val, Unevaluated[head[left]]]],
                SubstitutionValues[]
            ],
            nsubst, rsubst
        },
            (* negative case *)
            nsubst = If[
                lsubst === SubstitutionSum[],
                SubstitutionSum[],
                PartSubstitution[
                    {shift + 1},
                    Replace[HoldPattern[mid], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
                    DefaultSubstitutions[Unevaluated[patt]]
                ]
            ];
            rsubst = Which[
                Length[HoldComplete[right]] > 0,
                SubstitutionValues[],
                nsubst === SubstitutionSum[],
                SubstitutionSum[],
                True,
                With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternMatch[val, Unevaluated[head[right]]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]
            ];
            With[{
                val = Unevaluated @@ head @@@ HoldComplete[#2]
            },
            With[{
                posSubst = (* positive case *)
                    SubstitutionExpand[
                        SubstitutionMerge[
                            lsubst,
                            PartSubstitution[
                                {shift + 1},
                                Replace[HoldPattern[mid], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
                                SubstitutionSum[
                                    PatternMatch[val, Unevaluated[head[patt]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest],
                                    If[HoldComplete[def] =!= HoldComplete[], SubstitutionValues[def], SubstitutionSum[]]
                                ]
                            ],
                            rsubst
                        ],
                        n
                    ]
            },
                SubstitutionSum[
                    posSubst,
                    If[ Length[posSubst] >= n,
                        SubstitutionSum[],
                        SubstitutionProduct[lsubst, nsubst, rsubst]
                    ]
                ]
            ]]
        ] &],
		    tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]]
	    ],
        n
    ]
]


(* Condition *)

PatternMatch[expr_, Verbatim[Condition][patt_, cond_]] :=
	LazySelect[LazySubstitutionExpand @ PatternMatch[Unevaluated[expr], Unevaluated[patt]], ReplaceAll[Unevaluated[cond], LazyFirst[LazySubstitutionBindings[#], {}] &]]


(* PatternTest *)

PatternMatch[expr_, Verbatim[PatternTest][patt_, test_]] :=
	LazySelect[LazySubstitutionExpand @ PatternMatch[Unevaluated[expr], Unevaluated[patt]], test[ReleaseHold @ LazyFirst[LazySubstitutionApply[patt, #], HoldComplete[patt]]] &]


(* fallback *)

PatternMatch[head1_[same__, args___], head2_[same__, patt___]] := PatternMatch[Unevaluated[head1[args]], Unevaluated[head2[patt]]]

PatternMatch[head1_[args___], head2_[patt___]] /; Length[Unevaluated[{args}]] == Length[Unevaluated[{patt}]] := With[{
    headSubst = If[
        Unevaluated[head1] === Unevaluated[head2],
        MatchValues[],
        PatternMatch[Unevaluated[head1], Unevaluated[head2]]
    ]
},
    MatchProduct[
        LazyMap[Replace[MatchPart[part_, rest__] :> MatchPart[Prepend[part, 0], rest]], headSubst],
        Evaluate @ Catch @ ToLazyList[MapThread[
                With[{e = Unevaluated @@ #1, p = Unevaluated @@ #2},
                    With[{subst = MatchSum[Evaluate[PatternMatch[e, p]]]},
                        If[ subst === MatchSum[],
                            Throw[subst],
                            LazyMap[Replace[MatchPart[part_, rest__] :> MatchPart[Prepend[part, #3], rest]], subst]
                        ]
                    ]
                ] &,
                {HoldComplete /@ Unevaluated[{args}], HoldComplete /@ Unevaluated[{patt}], Range[Length[Unevaluated[{args}]]]}
            ],
            MatchProduct
        ]
    ]
]


PatternMatch[head_Symbol[args___], head_Symbol[patt___]] /; MemberQ[Attributes[head], Flat] := Block[{h},
    SetAttributes[h, DeleteCases[Attributes[head], Flat]];
    SubstitutionProduct @@ (
        With[{expr = Unevaluated @@ #1, p = Unevaluated @@ #2}, PatternMatch[expr, p]] & @@@
            Tuples[{Groupings[Unevaluated[{args}], {{h -> 1, 1}, h -> 2}, Hold], Groupings[Unevaluated[{patt}], {{h -> 1, 1}, h -> 2}, Hold]}]
    ) /. h :> head
]


PatternMatch[expr_, Unevaluated[Sequence[]], _] := MatchValues[expr]

PatternMatch[expr_, expr_, _] := MatchPart[{}, HoldPattern[expr], MatchValues[expr]]

PatternMatch[___] := MatchSum[]

